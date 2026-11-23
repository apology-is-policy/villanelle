# Second review of the task rules

Reviewed at `df3a205` on 23 November 2026. The review reads the [core](core.md),
sections 3, 6.8 to 6.12, 7 and 8, against the task rows, [A3], [I9], [I10]
and example 10.2 of the [fact logic](facts.md). The changes of 22 November
are recorded in core section 12. The fact logic describes its purity repair
in the introduction and [I10]. Its section 14 has no entry for that date.
The status of the crate is the one in the [implementation review](review.md).

The question is whether a history allowed by the written checks can get
stuck under a faithful host. The examples below abbreviate decisions with a
single empty alternative and omit unused continuations. The oracle result
in RT1 checks the schedule and the failure only. There is no slice 4
checker. This review does not establish any of the slice exits.

**RT1. A cancelled direct run can discard an argument it cannot release**
([E-Run], [E-AwaitHost], [TK1], [TK4]). Rule silent for an extern root,
and the static rule is wrong for the behavior implemented. Consider:

```text
extern resource lock
extern async control finish(k : lock) ■ { ok {} │ cancelled {} } uses io
control bridge(k : lock) ■ { done {} } uses io
    ⊤ ▷ d : Δ run finish(k) ▸ ok {} │ cancelled {}
    ⊤ ▷ ■ done {}
```

Let an async caller await a cancellable tick, open a lock on either history,
then call `bridge(k)`. Set the root flag at the tick. The resource crosses
no await in the caller. The synchronous bridge moves it exactly once.
[W10] allows the direct run. [TK4] constrains by-value operands of await
and spawn, and leaves the operand of run unrestricted. [E-Run] starts an
activation of the callee, but an extern has no body and no rule explains
how that root requests the host operation.

The draft oracle has a special extern branch in `Operation::RunControl`.
It inherits cancellation and tries to release the lock. A `vn2 test` run
with `cancel_at 1` and only `open_lock -> ok {lock#1}` scripted reached
`X8 E-Unwind`. The normal host call would have completed the lock.
If direct extern run is supported, specify its start, waiting, withdrawal
and completion, and require releasable by-value arguments wherever the
operation can be withdrawn. Running a *defined* control with a lock it
completes before its first await does not need this restriction.

**RT2. A member can interrupt the owner's own pending host operation**
([E-MemberFault], [E-Unwind], [E-Stop]). Rule silent. Take a producer
whose first statement faults. In an async control that permits faults,
spawn one such member and immediately await a host operation with a
by-value lease declared `on fault release`. Drain the set on the normal
continuation. The owner starts the operation, then the member takes the
turn and faults. All the values at the suspension satisfy [TK4].

There are zero activations above the owner. [E-MemberFault] stops those
above it and faults the owner itself. [E-Unwind] visits the owner's slots,
but the lease has already moved to the host. [E-AwaitHost] specifies
withdrawal on cancellation and stop. Neither occurred in the owner.
Theorem 2 needs the operation withdrawn once, its lease released once,
and no later completion event. The oracle explicitly withdraws a waiting
host operation before stopping the activations above the owner. This is a
missing transition in the paper. It applies even to an operation without
a cancelled alternative.

**RT3. A spawn can exceed the range of count** ([E-Spawn], [TK1], [TK6],
[A3]). Rule wrong. Take an initially empty set and a loop with no await:

```text
⊤ ▷ s : ↻ again() {
    ⊤ ▷ spawn worker() into pool
    ⊤ ▷ ↑ again()
}
```

The producer has no arguments and returns one empty payload. No turn passes
in the loop, no member is removed, and there is no scope exit to check.
On a machine with 32-bit usize the 4,294,967,296th spawn has no precondition
to fail. [TK6] then says the new count is 4,294,967,296 and [A3] bounds it
by 4,294,967,295. There is no valuation for the facts on this reachable
history. This breaks the fact invariant of section 8 without needing a
host operation or an actual allocation experiment. A wrap would falsify
[TK6] and a range trap would be an unexcluded X7. Give spawn a capacity
obligation or specify an observable exhaustion behavior and its facts.

**RT4. A plain expansion of await drops a turn** ([E-Await], theorem 4).
Rule wrong if the theorem includes decisions on defined async controls.
Let a parent spawn a child that emits "child", then await a defined
control whose only statement emits "parent" before returning. Drain the
set. At the entry to the awaited activation the child may run first.
Binding the parameters and substituting the body as in theorem 4 leaves
no suspension between spawn and the parent's emit. The child-first trace
is lost. This is an observation difference, not a stuck state. Restrict
the theorem to ordinary calls, or specify an expansion with the same
scheduling point. Expansion of a run would also have to preserve its
pool and root.

**What held up.** [W11] now rules out capture of next. On an empty set a
decision moves the slot on precisely its empty atom. An ordinary producer
return leaves the slot available even when it removes the last member.
[W12] reserves empty for that final test and gives synthetic cancellation
no payload and no condition that the host would have to establish.
[TK1], [TK2] and [E-Done] then agree on availability, payload shape and
coverage, including when a done member is waiting to be collected.

The revised [TK6] gives the completion and entry values of an exclusive
parameter distinct names. For a producer that increments it, the returned
condition is satisfiable. Fresh names per delivered member also prevent
identifying one member's argument with another's. The decrement counts a
delivered member and the empty fact refers to the set before consumption.
[I10] correctly excludes async operations and synchronous callers that
reach run transitively, including through supervision. Two calls that
collect the first of two racing members can return different answers.

[E-AwaitHost] checks the precondition and allowance even on an immediate
cancelled completion. It releases by-value arguments and passes the turn.
A previously started operation withdrawn by cancellation has no completion
event. [E-Cancel] propagates the request down ownership and into nested
runs. A member spawned *after* cancelling the current members of a set
in an uncancelled owner does not inherit a flag from the set itself.

[E-Turn] freezes outer pools during a nested run. Within one pool a wait
for next follows the ownership tree towards a member, never back to its
parent. A finite chain bottoms out at a ready task, a done payload or a
host wait. No fairness or termination guarantee is needed for progress in
this sense. [TK3] keeps a lender alive through the last empty decision and
transfers loans to a borrowed payload. [TK4] covers queued arguments,
boundary care and done payloads during a stop. [TK5] checks every await
with an available faulting set, including awaits on a different set, and
prevents opening a lexical boundary around an already available set.
[TK7] charges child effects to the spawning or calling activation, as the
extended stack of [E-Effect] requires. These checks explain why the usual
schedules preserve ownership and fault permission. RT1 to RT3 remain
obligations for the general safety and resource claims.
