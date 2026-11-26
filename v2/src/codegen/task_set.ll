; A queue holds its head and the address of the link to fill on append.
; Each activation starts with its next link, resume index/result tag, and heap flag.
; Both queues and the producer entry belong to one invocation of the owner.
%vn2.member_header = type { ptr, i32, i1 }
%vn2.queue = type { ptr, ptr }
%vn2.pool = type { %vn2.queue, %vn2.queue, i64, i64, ptr, ptr }

declare void @llvm.trap()

define internal fastcc void @vn2_pool_init(ptr %pool, ptr %resume) {
  store %vn2.pool zeroinitializer, ptr %pool
  %ready_tail = getelementptr %vn2.pool, ptr %pool, i32 0, i32 0, i32 1
  store ptr %pool, ptr %ready_tail
  %done = getelementptr %vn2.pool, ptr %pool, i32 0, i32 1
  %done_tail = getelementptr %vn2.queue, ptr %done, i32 0, i32 1
  store ptr %done, ptr %done_tail
  %entry_slot = getelementptr %vn2.pool, ptr %pool, i32 0, i32 4
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
  %spare = getelementptr %vn2.pool, ptr %pool, i32 0, i32 5
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

define internal fastcc void @vn2_spawn(ptr %pool, ptr %member, i1 %heap, i64 %max) {
entry:
  %total = getelementptr %vn2.pool, ptr %pool, i32 0, i32 3
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
  call fastcc void @vn2_append(ptr %pool, ptr %member)
  %ready = getelementptr %vn2.pool, ptr %pool, i32 0, i32 2
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
define internal fastcc void @vn2_choose_owner(ptr %pool, i1 %defined_await) {
entry:
  %inactive = icmp eq ptr %pool, null
  br i1 %inactive, label %alone, label %active
alone:
  call i64 @vn2_pick_turn(i64 1)
  ret void
active:
  %entry_slot = getelementptr %vn2.pool, ptr %pool, i32 0, i32 4
  %resume = load ptr, ptr %entry_slot
  %done = getelementptr %vn2.pool, ptr %pool, i32 0, i32 1
  %ready = getelementptr %vn2.pool, ptr %pool, i32 0, i32 2
  %total = getelementptr %vn2.pool, ptr %pool, i32 0, i32 3
  %t = load i64, ptr %total
  %empty = icmp eq i64 %t, 0
  br label %choose
choose:
  %r = load i64, ptr %ready
  %head = load ptr, ptr %done
  %has_done = icmp ne ptr %head, null
  %can_deliver = or i1 %empty, %has_done
  %owner = or i1 %defined_await, %can_deliver
  %offset = zext i1 %owner to i64
  %offered = add i64 %r, %offset
  %choice = call i64 @vn2_pick_turn(i64 %offered)
  %index = urem i64 %choice, %offered
  %take_owner = icmp ult i64 %index, %offset
  br i1 %take_owner, label %selected, label %child
child:
  %i = sub i64 %index, %offset
  %link = call fastcc ptr @vn2_link_at(ptr %pool, i64 %i)
  %member = load ptr, ptr %link
  %tag = call fastcc i32 %resume(ptr %member)
  ; -3 gives up the turn. A nonnegative alternative finishes the member.
  %yielded = icmp eq i32 %tag, -3
  br i1 %yielded, label %choose, label %finished
finished:
  call fastcc ptr @vn2_unlink(ptr %pool, ptr %link)
  %result = getelementptr %vn2.member_header, ptr %member, i32 0, i32 1
  store i32 %tag, ptr %result
  %nr = sub i64 %r, 1
  store i64 %nr, ptr %ready
  call fastcc void @vn2_append(ptr %done, ptr %member)
  br label %choose
selected:
  ret void
}

define internal fastcc ptr @vn2_next(ptr %pool) {
  call fastcc void @vn2_choose_owner(ptr %pool, i1 false)
  %done = getelementptr %vn2.pool, ptr %pool, i32 0, i32 1
  %total = getelementptr %vn2.pool, ptr %pool, i32 0, i32 3
  %t = load i64, ptr %total
  %empty = icmp eq i64 %t, 0
  br i1 %empty, label %no_members, label %oldest
no_members:
  %last_spare = getelementptr %vn2.pool, ptr %pool, i32 0, i32 5
  %last = load ptr, ptr %last_spare
  %has_spare = icmp ne ptr %last, null
  br i1 %has_spare, label %release_spare, label %empty_set
release_spare:
  call void @free(ptr %last)
  br label %empty_set
empty_set:
  ret ptr null
oldest:
  %first = call fastcc ptr @vn2_unlink(ptr %done, ptr %done)
  %nt = sub i64 %t, 1
  store i64 %nt, ptr %total
  %storage = getelementptr %vn2.member_header, ptr %first, i32 0, i32 2
  %heap = load i1, ptr %storage
  br i1 %heap, label %cache, label %deliver
cache:
  ; The caller moves the selected payload before it can next use the set.
  ; Retain at most one delivered frame, even when draining a large batch.
  %spare = getelementptr %vn2.pool, ptr %pool, i32 0, i32 5
  %previous = load ptr, ptr %spare
  call void @free(ptr %previous)
  store ptr %first, ptr %spare
  br label %deliver
deliver:
  ret ptr %first
}
