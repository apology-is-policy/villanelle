; A parked activation owns the typed request and a slot for its completion tag.
%vn2.pending = type { ptr, ptr, i32 }

define internal fastcc void @vn2_park_host(ptr %scheduler, ptr %member, ptr %wait, ptr %request, ptr %complete) {
  store ptr %request, ptr %wait
  %fn = getelementptr %vn2.pending, ptr %wait, i32 0, i32 1
  store ptr %complete, ptr %fn
  %slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 5
  store ptr %wait, ptr %slot
  %waiting = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 2
  %n = load i64, ptr %waiting
  %next = add i64 %n, 1
  store i64 %next, ptr %waiting
  %idle = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 3
  store ptr @vn2_select_host, ptr %idle
  call fastcc void @vn2_block_member(ptr %scheduler, ptr %member)
  ret void
}

; No ready tasks remain. Offer a waiting root first, then waiting members
; in spawn order. A true return lets the root complete its own request.
define internal fastcc i1 @vn2_select_host(ptr %scheduler, ptr %root) {
entry:
  %waiting = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 2
  %n = load i64, ptr %waiting
  %alone = icmp eq i64 %n, 0
  br i1 %alone, label %root_only, label %members
root_only:
  call fastcc i1 @vn2_poll_cancel()
  call i64 @vn2_pick_waiting(ptr %root, i64 1)
  ret i1 true
members:
  %has_root = icmp ne ptr %root, null
  %offset = zext i1 %has_root to i64
  %count = add i64 %n, %offset
  ; Parallel arrays of host handles and member frames. The common single
  ; operation fits on the stack. Each live member frame is larger than two pointers.
  %local = alloca [2 x ptr]
  %single = icmp eq i64 %count, 1
  br i1 %single, label %prepare, label %allocate
allocate:
  %slots = shl i64 %count, 1
  %bytes = ptrtoint ptr getelementptr (ptr, ptr null, i64 1) to i64
  %size = mul i64 %slots, %bytes
  %heap = call ptr @malloc(i64 %size)
  %failed = icmp eq ptr %heap, null
  br i1 %failed, label %exhausted, label %prepare
exhausted:
  call void @llvm.trap()
  unreachable
prepare:
  %states = phi ptr [ %local, %members ], [ %heap, %allocate ]
  %frames = getelementptr ptr, ptr %states, i64 %count
  br i1 %has_root, label %add_root, label %scan
add_root:
  %root_state = load ptr, ptr %root
  store ptr %root_state, ptr %states
  store ptr null, ptr %frames
  br label %scan
scan:
  %link = phi ptr [ %scheduler, %prepare ], [ %scheduler, %add_root ], [ %member, %advance ]
  %i = phi i64 [ %offset, %prepare ], [ %offset, %add_root ], [ %next, %advance ]
  %member = load ptr, ptr %link
  %slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 5
  %wait = load ptr, ptr %slot
  %pending = icmp ne ptr %wait, null
  br i1 %pending, label %add_member, label %advance
add_member:
  %request = load ptr, ptr %wait
  %state = load ptr, ptr %request
  %state_slot = getelementptr ptr, ptr %states, i64 %i
  store ptr %state, ptr %state_slot
  %frame_slot = getelementptr ptr, ptr %frames, i64 %i
  store ptr %member, ptr %frame_slot
  %added = add i64 %i, 1
  br label %advance
advance:
  %next = phi i64 [ %i, %scan ], [ %added, %add_member ]
  %full = icmp eq i64 %next, %count
  br i1 %full, label %pick, label %scan
pick:
  call fastcc i1 @vn2_poll_cancel()
  %choice = call i64 @vn2_pick_waiting(ptr %states, i64 %count)
  %index = urem i64 %choice, %count
  %chosen_slot = getelementptr ptr, ptr %frames, i64 %index
  %chosen = load ptr, ptr %chosen_slot
  br i1 %single, label %dispatch, label %release
release:
  call void @free(ptr %states)
  br label %dispatch
dispatch:
  %root_chosen = icmp eq ptr %chosen, null
  br i1 %root_chosen, label %done, label %deliver
deliver:
  %active_slot = getelementptr %vn2.member_header, ptr %chosen, i32 0, i32 5
  %active = load ptr, ptr %active_slot
  %bound = load ptr, ptr %active
  %fn = getelementptr %vn2.pending, ptr %active, i32 0, i32 1
  %complete = load ptr, ptr %fn
  %tag = call i32 %complete(ptr %bound)
  %result = getelementptr %vn2.pending, ptr %active, i32 0, i32 2
  store i32 %tag, ptr %result
  store ptr null, ptr %active_slot
  %flag = getelementptr %vn2.member_header, ptr %chosen, i32 0, i32 3
  store i1 false, ptr %flag
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %r = load i64, ptr %ready
  %nr = add i64 %r, 1
  store i64 %nr, ptr %ready
  %nw = sub i64 %n, 1
  store i64 %nw, ptr %waiting
  br label %done
done:
  ret i1 %root_chosen
}

define internal fastcc void @vn2_wait_for_root(ptr %scheduler, ptr %request) {
entry:
  %alone = icmp eq ptr %scheduler, null
  br i1 %alone, label %root_only, label %active
root_only:
  call fastcc i1 @vn2_poll_cancel()
  call i64 @vn2_pick_waiting(ptr %request, i64 1)
  ret void
active:
  call fastcc void @vn2_run_ready_members(ptr %scheduler)
  %selected = call fastcc i1 @vn2_select_host(ptr %scheduler, ptr %request)
  br i1 %selected, label %done, label %active
done:
  ret void
}
