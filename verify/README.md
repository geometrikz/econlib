# Verification protocol

Lean's kernel only certifies that a proof proves *its own statement*. The main
risk in formalized economics is a statement that says the wrong thing: a
hypothesis that can never hold, a junk value (Mathlib's `sSup ∅ = 0`, `x / 0 = 0`)
doing the work, a weaker conclusion than the textbook's. So "checked" means two
steps, in order. Nothing counts as done until both pass.

## Step 1: context-isolated adversarial statement review

1. `python3 verify/strip_proofs.py EconLean /tmp/review_in/EconLean` produces
   statement-only files (comments stripped, proofs replaced by `sorry`).
2. Give a **fresh** agent (no thread context, no proofs, no comments) only those
   files plus the textbook, using the prompt in `verify/REVIEW_PROMPT.md`; record verdicts in `Audit/REVIEW-<topic>.md`. It
   tries to show each statement does not match canonical economics, and writes
   Lean sanity tests (satisfiability witnesses, negations it believes hold).
3. Compile its sanity tests against the real library; keep the confirmed ones, sorry-free, in `EconLean/Audit/` (e.g. `ConsumerFindings.lean`). Fix confirmed problems,
   then re-review the changed statements.

## Step 2: machine checks (`verify/check.sh`, also run in CI)

1. **Challenge drift.** `verify/make_challenge.py` regenerates
   `challenge/` (the frozen, reviewed statements, as a separate Lake project with the same module names) and `comparator.json`.
   Any diff fails: a statement cannot change, and a theorem cannot be added,
   without the reviewed challenge changing in the same commit.
2. **`lake check`** exports the whole library and replays it through Lean's
   kernel. Fails on `sorry` or on any axiom beyond `propext`, `Quot.sound`,
   `Classical.choice`. About 9 minutes on 4 cores.
3. **`lake comparator --paranoid`** (Lean's built-in successor of the FRO's
   Comparator) proves each theorem in `comparator.json` has exactly the
   statement in `challenge/`, with permitted axioms only, and has the proofs
   checked by Lean's kernel plus every independent checker bundled with Lean:
   `leanchecker-paranoid`, `lean4lean`, `nanoda` (Rust), `con-leche`, `con-ron`.
   This covers the theorems and everything they depend on (~36k declarations,
   about 4 minutes).

`PARANOID=1 verify/check.sh` also runs the independent checkers in step 2,
over all ~340k declarations including Mathlib: ~35 minutes, and nanoda needs
more than 16 GB of RAM there, so CI does not run it.

Both lake commands sandbox the build with `bubblewrap`; install it
(`apt install bubblewrap`). On Ubuntu 24.04 you may also need
`sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`.
On macOS, run step 2 in CI or a Linux VM.
