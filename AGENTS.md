# Agents working on Villanelle

This file binds every agent that works in this repository, whoever made it:
Claude, Codex, Gemini or any other. It holds the conduct every agent follows, the
source style and the native performance rule. `CLAUDE.md` is not only for
Claude: its hard rules and its sections "Working with the author", "Where the
truth lives", "Checkpoint discipline" and "Context economy and handoff" bind
every agent. So does the git-ignored `CLAUDE.local.md` beside it, where one
exists, with its protected files, authorizations and machine rules. Read all
three before your first change. All three apply in full: the conduct below
restates their core so that no agent can miss it, and it relaxes none of them.

## Conduct

Code for four vertical slices of v2 was written on 21 and 22 November 2026 and
reported complete through oracle, checker and backend. The review of
23 November found that no slice met its exit:

- the "generator" produced one fixed program;
- the checker accepted programs that get stuck;
- the kernel did not validate what it was given;
- the oracle was wrong on fault boundaries;
- compiled programs freed memory twice;
- the status documents called all of it done.

Repairing it is a requalification that is still running (`docs/v2/review.md`).
The standard below applies to every agent alike, so that this does not happen
again.

### What "done" means

- Work is done when the exit condition named for it, in the plan or in section
  3 of the review, is met and its evidence is in the repository. Evidence is a
  test that runs in the suite, or a measurement given with its command and its
  output. Code that has not met that bar is "draft". Always say which of the
  two a piece of work is.
- `docs/v2/review.md` governs every statement about the state of v2. A slice is
  complete only when its row in section 3 is met. A finding is closed only with
  its date and the test that holds it. The words "complete", "done",
  "verified", "passes", "matches" and "green" carry exactly that meaning, in a
  commit message, a document, the shared log or Yip.
- Report a failure as plainly as a success, with its output. Write a known gap
  where the next agent will look (the review, the roadmap table); never leave
  it out.
- Claim no parity, performance or coverage that you did not measure on the
  complete path. "Not measured" is an acceptable answer. An estimate presented
  as a measurement is not.

### Evidence that can fail

- Every clause you implement gets a test that accepts and a test that rejects.
  Every program in a checker test is run in the oracle too: use
  `stuck_and_rejected` and `done_and_accepted` in `v2/tests/`.
- A test must be able to fail. Before you rely on a new test, break the code it
  covers, watch the test fail, and restore the code; or name the mutant it
  catches. None of these is evidence:
  - a test that asserts nothing;
  - a test that checks only that a run returns;
  - a test that passes whatever the code does.
- Never make a check pass by weakening it. That means no lowered expectations,
  widened tolerances, skipped or ignored tests, silenced warnings, `#[allow]` on
  a real lint, and no expected output rewritten to match what the code prints
  now. The one exception: the review records why the old expectation was wrong.
- A component does what its name says. A stand-in (a stub, a shortcut, or a
  fixed program where a generator belongs) is named as one in the code and in
  the review; `generate::template` is the example. Nothing that relies on a
  stand-in is reported as verified.
- When the code raises a question about the specification, the answer goes into
  the specification (`docs/v2/`), with an entry in that document's list of
  changes. Code never quietly departs from the specification.

### Order and size

- Build in the order of the plan and of section 10 of the review: one slice at a
  time, and within it the specification, oracle, checker, backend and fuzzing.
  Write nothing for a later slice until the earlier one is met.
- A checkpoint is one step that a reviewer can read in one sitting: a clause, a
  finding, or one part of a component. A push of thousands of lines across
  several slices cannot be reviewed, and is treated as draft.
- Run the gate before every commit:
  - `cargo fmt --check`;
  - `cargo clippy -D warnings`;
  - `cargo test --no-fail-fast`;
  - the `vn2` suite and the certificates, as `CLAUDE.md` lists them;
  - for a change to the checker or the generator, the regression campaigns,
    with their counts compared with the last gate.

  After a push, read the workflow run (`gh run view`) before calling it green.

### Context, handoff and the work of others

- When your context or quota runs low, stop at a clean boundary. Work in
  progress is not done: never commit it as done to close a session. Write the
  handoff first. It says what is verified (with the commands), what is written
  but not verified, and what comes next.
- Work that another agent left uncommitted or unverified is draft. Verify it as
  if it were new before you commit it. Say in the commit and in the log whose it
  was and what you checked.
- A finding against your work is recorded and fixed with a test, not argued
  away. If you believe a finding is wrong, show it with a program run in the
  oracle.

### The shared checkout and records

- Stage by explicit path. Never use `git add -A` or `git add .`. Never read,
  stage or copy an untracked file you did not create. The files and directories
  that `CLAUDE.local.md` protects are out of bounds.
- Push to `main` only if the author has authorized you by name, and then only
  validated checkpoints. Without that authorization, work on a branch of your
  own and hand it over. It lands after another agent has rebased it, read the
  diff, rerun the gate, and recorded in the review what it closes. Force
  pushes, history rewrites, tags and releases need the author's explicit
  request.
- Before you change a file, claim it on Yip. Stay off files that another agent
  has claimed.
- Sign the shared cross-agent log that `CLAUDE.local.md` names with your own
  name, and write in it only what you verified. Never edit another agent's
  entries.
- The repository is public. Committed files contain no home paths, machine
  details, personal names or e-mail addresses.
- Run one heavy build or test suite at a time, check free disk space first, and
  never rebuild the pinned LLVM.
- Ask the author only at a real language-design fork, with a recommendation.
  Never settle a language-design question silently in code.

## Source style

Use `applications/settings/server.vn` and `docs/reference/formatting.md` as the
style reference for new or edited Villanelle code. The language author's preference is:

- Keep path labels visually distinct and unbraced unless grouping helps understanding.
- Keep short dispositions beside their labels, for example `[missing]: exit absent;`.
- For a label on its own line, indent its selected statements beneath it.
- Wrap long signatures, calls and payloads into readable multiline lists. The
  formatter's default target is 100 columns with four spaces.
- Separate decisions from their final path dispositions with a blank line when it
  helps scanning. Retain meaningful comments and paragraph breaks.

Run `./bin/vnc format FILE --write` on new or substantially edited Villanelle files
using the current compiler. Preview the result when preserving a user's manual
layout matters. Avoid unrelated repository-wide reformatting. Rust source uses
`cargo fmt`. Formatting never adds or removes path-grouping braces.

## Native performance

Aim to match or beat equivalent optimized Rust for every operation, data structure,
algorithm, and memory-management path. Use the same observable work and verify the
results. Measure the hot operation separately from launch, decoding and output.
For a gap, inspect generated code and measure allocation count, requested bytes
and data movement as well as time. Record the workload, compiler settings, hardware,
remaining gap and next experiment. Preserve checked ownership, origins, outcomes,
resource completion, cancellation and fault diagnostics when optimizing.
