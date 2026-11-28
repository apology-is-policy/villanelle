; A queue holds its head and the address of the link to fill on append.
; The scheduler lists unfinished members in spawn order and counts ready ones.
; A pool holds its completion queue, count, producer, spare frame and waiter.
%vn2.queue = type { ptr, ptr }
; Unfinished members, ready count, host-waiting member count, idle callback, pending withdrawal callback.
%vn2.scheduler = type { %vn2.queue, i64, i64, ptr, ptr }
%vn2.pool = type { %vn2.queue, i64, ptr, ptr, ptr }
; Next link, resume index/result tag, heap flag, blocked flag, originating set, host wait.
%vn2.member_header = type { ptr, i32, i1, i1, ptr, ptr }

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
  %member = load ptr, ptr %link
  %flag = getelementptr %vn2.member_header, ptr %member, i32 0, i32 3
  %blocked = load i1, ptr %flag
  %ready = xor i1 %blocked, true
  %first = icmp eq i64 %i, 0
  %found = and i1 %ready, %first
  br i1 %found, label %return, label %advance
advance:
  %step = zext i1 %ready to i64
  %less = sub i64 %i, %step
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
  %flag = getelementptr %vn2.member_header, ptr %member, i32 0, i32 3
  store i1 false, ptr %flag
  %set_slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 4
  store ptr %pool, ptr %set_slot
  %wait = getelementptr %vn2.member_header, ptr %member, i32 0, i32 5
  store ptr null, ptr %wait
  call fastcc void @vn2_append(ptr %scheduler, ptr %member)
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %r = load i64, ptr %ready
  %nr = add i64 %r, 1
  %nt = add i64 %t, 1
  store i64 %nr, ptr %ready
  store i64 %nt, ptr %total
  ret void
}

define internal fastcc i1 @vn2_can_deliver(ptr %pool) {
  %head = load ptr, ptr %pool
  %has_done = icmp ne ptr %head, null
  %total = getelementptr %vn2.pool, ptr %pool, i32 0, i32 1
  %t = load i64, ptr %total
  %empty = icmp eq i64 %t, 0
  %can_deliver = or i1 %empty, %has_done
  ret i1 %can_deliver
}

define internal fastcc void @vn2_block_member(ptr %scheduler, ptr %member) {
  %flag = getelementptr %vn2.member_header, ptr %member, i32 0, i32 3
  store i1 true, ptr %flag
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %r = load i64, ptr %ready
  %nr = sub i64 %r, 1
  store i64 %nr, ptr %ready
  ret void
}

; Only the task that owns a set can wait for its next completion. Leave a
; blocked member in its original position and exclude it from turn offers.
define internal fastcc void @vn2_wait_member(ptr %scheduler, ptr %member, ptr %pool) {
entry:
  %eligible = call fastcc i1 @vn2_can_deliver(ptr %pool)
  br i1 %eligible, label %yield, label %block
block:
  %waiter = getelementptr %vn2.pool, ptr %pool, i32 0, i32 4
  store ptr %member, ptr %waiter
  call fastcc void @vn2_block_member(ptr %scheduler, ptr %member)
  br label %yield
yield:
  ret void
}

; Run one eligible member through its next yield or completion.
define internal fastcc void @vn2_step_member(ptr %scheduler, i64 %index) {
entry:
  %link = call fastcc ptr @vn2_link_at(ptr %scheduler, i64 %index)
  %member = load ptr, ptr %link
  %set_slot = getelementptr %vn2.member_header, ptr %member, i32 0, i32 4
  %pool = load ptr, ptr %set_slot
  %entry_slot = getelementptr %vn2.pool, ptr %pool, i32 0, i32 2
  %resume = load ptr, ptr %entry_slot
  %tag = call fastcc i32 %resume(ptr %member, ptr %scheduler)
  ; -3 gives up the turn. A nonnegative alternative finishes the member.
  %yielded = icmp eq i32 %tag, -3
  br i1 %yielded, label %done, label %finished
finished:
  call fastcc ptr @vn2_unlink(ptr %scheduler, ptr %link)
  %result = getelementptr %vn2.member_header, ptr %member, i32 0, i32 1
  store i32 %tag, ptr %result
  call fastcc void @vn2_append(ptr %pool, ptr %member)
  %waiter_slot = getelementptr %vn2.pool, ptr %pool, i32 0, i32 4
  %waiter = load ptr, ptr %waiter_slot
  %waiting = icmp ne ptr %waiter, null
  br i1 %waiting, label %wake, label %retire
wake:
  ; One task leaves the ready count and one enters it.
  store ptr null, ptr %waiter_slot
  %flag = getelementptr %vn2.member_header, ptr %waiter, i32 0, i32 3
  store i1 false, ptr %flag
  br label %done
retire:
  %ready = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 1
  %current = load i64, ptr %ready
  %nr = sub i64 %current, 1
  store i64 %nr, ptr %ready
  br label %done
done:
  ret void
}

; Parking a cancellable request installs a callback. Once the root is
; cancelled, further member awaits release before issue, so scan only once.
define internal fastcc void @vn2_cancel_parked(ptr %scheduler, i1 %cancelled) {
entry:
  br i1 %cancelled, label %check, label %done
check:
  %slot = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 4
  %sweep = load ptr, ptr %slot
  %armed = icmp ne ptr %sweep, null
  br i1 %armed, label %withdraw, label %done
withdraw:
  store ptr null, ptr %slot
  call fastcc void %sweep(ptr %scheduler)
  br label %done
done:
  ret void
}

; The owner is task zero whenever it is ready. Children follow in spawn
; order. A finished member stays counted until delivered by await next.
; At a defined await the owner is ready even with outstanding children.
; At await next it is ready only when a result or empty can be delivered.
define internal fastcc void @vn2_choose_owner(ptr %scheduler, ptr %awaited_set) {
  %flag = call fastcc i1 @vn2_poll_cancel()
  call fastcc void @vn2_choose_owner_polled(ptr %scheduler, ptr %awaited_set, i1 %flag)
  ret void
}

; A withdrawal has already polled this turn. Only poll again after a member
; runs or a host completion ends the turn.
define internal fastcc void @vn2_choose_owner_polled(ptr %scheduler, ptr %awaited_set, i1 %flag) {
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
  %cancelled = phi i1 [ %flag, %active ], [ %next_flag, %next_turn ]
  call fastcc void @vn2_cancel_parked(ptr %scheduler, i1 %cancelled)
  br i1 %defined_await, label %offer, label %waiting_next
waiting_next:
  %can_deliver = call fastcc i1 @vn2_can_deliver(ptr %awaited_set)
  br label %offer
offer:
  %owner = phi i1 [ true, %choose ], [ %can_deliver, %waiting_next ]
  %r = load i64, ptr %ready
  %offset = zext i1 %owner to i64
  %offered = add i64 %r, %offset
  %idle = icmp eq i64 %offered, 0
  br i1 %idle, label %host, label %pick
host:
  ; With the owner blocked and no ready member, a member is waiting for the host.
  %callback = getelementptr %vn2.scheduler, ptr %scheduler, i32 0, i32 3
  %poll = load ptr, ptr %callback
  call fastcc i1 %poll(ptr %scheduler, ptr null)
  br label %next_turn
pick:
  %choice = call i64 @vn2_pick_turn(i64 %offered)
  %index = urem i64 %choice, %offered
  %take_owner = icmp ult i64 %index, %offset
  br i1 %take_owner, label %selected, label %child
child:
  %i = sub i64 %index, %offset
  call fastcc void @vn2_step_member(ptr %scheduler, i64 %i)
  br label %next_turn
next_turn:
  %next_flag = call fastcc i1 @vn2_poll_cancel()
  br label %choose
selected:
  ret void
}

define internal fastcc ptr @vn2_take_result(ptr %pool) {
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
