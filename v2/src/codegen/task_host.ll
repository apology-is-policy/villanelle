; A parked activation owns the typed request and a slot for its completion tag.
%vn2.pending = type { ptr, ptr, i32, ptr }

; An inherited cancellation yields a ready member with its result already
; bound. The started request parks the member until completion or withdrawal.
define internal fastcc void @vn2_member_host(ptr %scheduler, ptr %member, ptr %wait, ptr %request, ptr %start, ptr %complete, ptr %cancel, i1 %skip) {
entry:
  br i1 %skip, label %release, label %issue
release:
  %tag = call fastcc i32 %cancel(ptr %request, i1 false)
  %result = getelementptr %vn2.pending, ptr %wait, i32 0, i32 2
  store i32 %tag, ptr %result
  ret void
issue:
  call void %start(ptr %request)
  store ptr %request, ptr %wait
  %fn = getelementptr %vn2.pending, ptr %wait, i32 0, i32 1
  store ptr %complete, ptr %fn
  %cleanup = getelementptr %vn2.pending, ptr %wait, i32 0, i32 3
  store ptr %cancel, ptr %cleanup
  %cancellable = icmp ne ptr %cancel, null
  br i1 %cancellable, label %arm, label %park
arm:
  %sweep = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 4
  store ptr @vn2_withdraw_members, ptr %sweep
  br label %park
park:
  %slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 6
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

define internal fastcc void @vn2_wake_host(ptr %scheduler, ptr %member, ptr %wait, i32 %tag) {
  %result = getelementptr %vn2.pending, ptr %wait, i32 0, i32 2
  store i32 %tag, ptr %result
  %active_slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 6
  store ptr null, ptr %active_slot
  %flag = getelementptr %vn2.member_header, ptr %member, i32 0, i32 3
  store i1 false, ptr %flag
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %r = load i64, ptr %ready
  %nr = add i64 %r, 1
  store i64 %nr, ptr %ready
  %waiting = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 2
  %n = load i64, ptr %waiting
  %nw = sub i64 %n, 1
  store i64 %nw, ptr %waiting
  ret void
}

; Root withdrawal, if any, precedes this walk. Waking a member leaves it
; in spawn order. Its activation resumes only after a ready choice.
define internal fastcc void @vn2_withdraw_members(ptr %scheduler, i1 %all) {
entry:
  br label %scan
scan:
  %link = phi ptr [ %scheduler, %entry ], [ %member, %advance ]
  %member = load ptr, ptr %link
  %end = icmp eq ptr %member, null
  br i1 %end, label %done, label %inspect
inspect:
  %slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 6
  %wait = load ptr, ptr %slot
  %parked = icmp ne ptr %wait, null
  %flag = getelementptr %vn2.member_header, ptr %member, i32 0, i32 4
  %local = load i1, ptr %flag
  %affected = or i1 %all, %local
  %withdraw_wait = and i1 %parked, %affected
  br i1 %withdraw_wait, label %pending, label %advance
pending:
  %fn = getelementptr %vn2.pending, ptr %wait, i32 0, i32 3
  %cancel = load ptr, ptr %fn
  %cancellable = icmp ne ptr %cancel, null
  br i1 %cancellable, label %withdraw, label %advance
withdraw:
  %request = load ptr, ptr %wait
  %tag = call fastcc i32 %cancel(ptr %request, i1 true)
  call fastcc void @vn2_wake_host(ptr %scheduler, ptr %member, ptr %wait, i32 %tag)
  br label %advance
advance:
  br label %scan
done:
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
  %slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 6
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
  %active_slot = getelementptr %vn2.member_header, ptr %chosen, i32 0, i32 6
  %active = load ptr, ptr %active_slot
  %bound = load ptr, ptr %active
  %fn = getelementptr %vn2.pending, ptr %active, i32 0, i32 1
  %complete = load ptr, ptr %fn
  %tag = call i32 %complete(ptr %bound)
  call fastcc void @vn2_wake_host(ptr %scheduler, ptr %chosen, ptr %active, i32 %tag)
  br label %done
done:
  ret i1 %root_chosen
}

; The caller has started the root request. At the start of each turn decide
; withdrawal before offering ready members or any pending handle to the host.
; True means the caller must withdraw and make the root ready in this turn.
define internal fastcc i1 @vn2_wait_for_root(ptr %scheduler, ptr %request, i1 %cancellable) {
entry:
  %alone = icmp eq ptr %scheduler, null
  br label %turn
turn:
  %flag = call fastcc i1 @vn2_poll_cancel()
  %stop = and i1 %cancellable, %flag
  br i1 %stop, label %withdraw, label %waiting
withdraw:
  ret i1 true
waiting:
  br i1 %alone, label %root_only, label %members
root_only:
  call i64 @vn2_pick_waiting(ptr %request, i64 1)
  ret i1 false
members:
  call fastcc void @vn2_cancel_parked(ptr %scheduler, i1 %flag)
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %count = load i64, ptr %ready
  %idle = icmp eq i64 %count, 0
  br i1 %idle, label %host, label %offer
offer:
  %choice = call i64 @vn2_pick_turn(i64 %count)
  %index = urem i64 %choice, %count
  call fastcc void @vn2_step_member(ptr %scheduler, i64 %index)
  br label %turn
host:
  %selected = call fastcc i1 @vn2_select_host(ptr %scheduler, ptr %request)
  br i1 %selected, label %complete, label %turn
complete:
  ret i1 false
}
