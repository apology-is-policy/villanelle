; A queue holds its head and the address of the link to fill on append.
; One ready queue and count serve all sets in the run. Each set holds
; its own completion queue, undelivered count, producer entry and spare frame.
%vn2.queue = type { ptr, ptr }
%vn2.scheduler = type { %vn2.queue, i64 }
%vn2.pool = type { %vn2.queue, i64, ptr, ptr }
; next link, resume index/result tag, heap flag, originating set
%vn2.member_header = type { ptr, i32, i1, ptr }

declare void @llvm.trap()

; An awaited owner joins the current run. The first owner in a fresh run
; supplies storage that stays live until its last set has been drained.
define internal fastcc ptr @vn2_owner_scheduler(ptr %inherited, ptr %scheduler) {
entry:
  %fresh = icmp eq ptr %inherited, null
  br i1 %fresh, label %initialize, label %inherit
inherit:
  ret ptr %inherited
initialize:
  store %vn2.scheduler zeroinitializer, ptr %scheduler
  %tail = getelementptr %vn2.queue, ptr %scheduler, i32 0, i32 1
  store ptr %scheduler, ptr %tail
  ret ptr %scheduler
}

define internal fastcc void @vn2_pool_init(ptr %pool, ptr %resume) {
  store %vn2.pool zeroinitializer, ptr %pool
  %tail = getelementptr %vn2.queue, ptr %pool, i32 0, i32 1
  store ptr %pool, ptr %tail
  %entry_slot = getelementptr %vn2.pool, ptr %pool, i32 0, i32 2
  store ptr %resume, ptr %entry_slot
  ret void
}

define internal fastcc void @vn2_append(ptr %queue, ptr %member) {
  %tail = getelementptr %vn2.queue, ptr %queue, i32 0, i32 1
  %link = load ptr, ptr %tail
  store ptr null, ptr %member
  store ptr %member, ptr %link
  store ptr %member, ptr %tail
  ret void
}

; Look up the link that points to the indexed ready member. A yielding
; member retains its place in spawn order.
define internal fastcc ptr @vn2_link_at(ptr %queue, i64 %index) {
entry:
  br label %seek
seek:
  %link = phi ptr [ %queue, %entry ], [ %member, %advance ]
  %i = phi i64 [ %index, %entry ], [ %less, %advance ]
  %found = icmp eq i64 %i, 0
  br i1 %found, label %return, label %advance
advance:
  %member = load ptr, ptr %link
  %less = sub i64 %i, 1
  br label %seek
return:
  ret ptr %link
}

define internal fastcc ptr @vn2_unlink(ptr %queue, ptr %link) {
  %member = load ptr, ptr %link
  %next = load ptr, ptr %member
  store ptr %next, ptr %link
  %last = icmp eq ptr %next, null
  br i1 %last, label %last_member, label %return
last_member:
  %tail = getelementptr %vn2.queue, ptr %queue, i32 0, i32 1
  store ptr %link, ptr %tail
  br label %return
return:
  ret ptr %member
}

; All members of a set have the same producer and frame layout. A delivered
; heap frame can be rebound once the owner reaches its next spawn.
define internal fastcc ptr @vn2_take_frame(ptr %pool, i64 %size) {
entry:
  %spare = getelementptr %vn2.pool, ptr %pool, i32 0, i32 3
  %cached = load ptr, ptr %spare
  %empty = icmp eq ptr %cached, null
  br i1 %empty, label %allocate, label %reuse
reuse:
  store ptr null, ptr %spare
  ret ptr %cached
allocate:
  %new = call ptr @malloc(i64 %size)
  %failed = icmp eq ptr %new, null
  br i1 %failed, label %exhausted, label %allocated
exhausted:
  call void @llvm.trap()
  unreachable
allocated:
  ret ptr %new
}

define internal fastcc void @vn2_spawn(ptr %scheduler, ptr %pool, ptr %member, i1 %heap, i64 %max) {
entry:
  %total = getelementptr %vn2.pool, ptr %pool, i32 0, i32 1
  %t = load i64, ptr %total
  %full = icmp eq i64 %t, %max
  br i1 %full, label %exhausted, label %append
exhausted:
  call void @llvm.trap()
  unreachable
append:
  %state = getelementptr %vn2.member_header, ptr %member, i32 0, i32 1
  store i32 0, ptr %state
  %storage = getelementptr %vn2.member_header, ptr %member, i32 0, i32 2
  store i1 %heap, ptr %storage
  %set_slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 3
  store ptr %pool, ptr %set_slot
  call fastcc void @vn2_append(ptr %scheduler, ptr %member)
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %r = load i64, ptr %ready
  %nr = add i64 %r, 1
  %nt = add i64 %t, 1
  store i64 %nr, ptr %ready
  store i64 %nt, ptr %total
  ret void
}

; The owner is task zero whenever it is ready. Children follow in spawn
; order. A finished member stays counted until delivered by await next.
; At a defined await the owner is ready even with outstanding children.
; At await next it is ready only when a result or empty can be delivered.
define internal fastcc void @vn2_choose_owner(ptr %scheduler, ptr %awaited_set) {
entry:
  %inactive = icmp eq ptr %scheduler, null
  br i1 %inactive, label %alone, label %active
alone:
  call i64 @vn2_pick_turn(i64 1)
  ret void
active:
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %defined_await = icmp eq ptr %awaited_set, null
  br label %choose
choose:
  br i1 %defined_await, label %offer, label %waiting_next
waiting_next:
  %head = load ptr, ptr %awaited_set
  %has_done = icmp ne ptr %head, null
  %total = getelementptr %vn2.pool, ptr %awaited_set, i32 0, i32 1
  %t = load i64, ptr %total
  %empty = icmp eq i64 %t, 0
  %can_deliver = or i1 %empty, %has_done
  br label %offer
offer:
  %owner = phi i1 [ true, %choose ], [ %can_deliver, %waiting_next ]
  %r = load i64, ptr %ready
  %offset = zext i1 %owner to i64
  %offered = add i64 %r, %offset
  %choice = call i64 @vn2_pick_turn(i64 %offered)
  %index = urem i64 %choice, %offered
  %take_owner = icmp ult i64 %index, %offset
  br i1 %take_owner, label %selected, label %child
child:
  %i = sub i64 %index, %offset
  %link = call fastcc ptr @vn2_link_at(ptr %scheduler, i64 %i)
  %member = load ptr, ptr %link
  %set_slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 3
  %pool = load ptr, ptr %set_slot
  %entry_slot = getelementptr %vn2.pool, ptr %pool, i32 0, i32 2
  %resume = load ptr, ptr %entry_slot
  %tag = call fastcc i32 %resume(ptr %member)
  ; -3 gives up the turn. A nonnegative alternative finishes the member.
  %yielded = icmp eq i32 %tag, -3
  br i1 %yielded, label %choose, label %finished
finished:
  call fastcc ptr @vn2_unlink(ptr %scheduler, ptr %link)
  %result = getelementptr %vn2.member_header, ptr %member, i32 0, i32 1
  store i32 %tag, ptr %result
  %nr = sub i64 %r, 1
  store i64 %nr, ptr %ready
  call fastcc void @vn2_append(ptr %pool, ptr %member)
  br label %choose
selected:
  ret void
}

define internal fastcc ptr @vn2_next(ptr %scheduler, ptr %pool) {
  call fastcc void @vn2_choose_owner(ptr %scheduler, ptr %pool)
  %total = getelementptr %vn2.pool, ptr %pool, i32 0, i32 1
  %t = load i64, ptr %total
  %empty = icmp eq i64 %t, 0
  br i1 %empty, label %no_members, label %oldest
no_members:
  %last_spare = getelementptr %vn2.pool, ptr %pool, i32 0, i32 3
  %last = load ptr, ptr %last_spare
  %has_spare = icmp ne ptr %last, null
  br i1 %has_spare, label %release_spare, label %empty_set
release_spare:
  call void @free(ptr %last)
  br label %empty_set
empty_set:
  ret ptr null
oldest:
  %first = call fastcc ptr @vn2_unlink(ptr %pool, ptr %pool)
  %nt = sub i64 %t, 1
  store i64 %nt, ptr %total
  %storage = getelementptr %vn2.member_header, ptr %first, i32 0, i32 2
  %heap = load i1, ptr %storage
  br i1 %heap, label %cache, label %deliver
cache:
  ; The caller moves the selected payload before it can next use the set.
  ; Retain at most one delivered frame, even when draining a large batch.
  %spare = getelementptr %vn2.pool, ptr %pool, i32 0, i32 3
  %previous = load ptr, ptr %spare
  call void @free(ptr %previous)
  store ptr %first, ptr %spare
  br label %deliver
deliver:
  ret ptr %first
}
