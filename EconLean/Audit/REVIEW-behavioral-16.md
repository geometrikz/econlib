# Review record: behavioral round 16 (2026-11-24)

Module: `BoundedRationality/KMRDarwin.lean` (KMR simultaneous-revision chain: best response by
everybody, then independent mutations; selection of the risk-dominant convention via the
cut-flow identity). Header-only edit in `KMRChain.lean` (pointer).
Frozen statements: `Audit/Statements/BehavioralXVI.lean` (7 statements).

## Step 1: adversarial statement review (context-isolated agent)
No MAJOR findings. Verified: `darwin` is the right chain (binomial mutation probabilities in
both directions, row-to-column convention matching `π ᵥ* Q = π`); `flux_cut` is the standard
cut balance; `darwin_last_ge` is true and all hypotheses matter (`0 < ε` essential, `2m ≤ N`
keeps the ℕ exponent positive); `darwin_selects` is not vacuous (invariant families exist) and
not trivial (fails when `p* > 1/2`).
MINOR, fixed in documentation: "KMR Theorem 3" qualified as the best-response special case; the
B case needs strict risk dominance of B under ties-to-A; stag hunt's A is the safe action
(checked in `StochasticStability.lean`). MINOR, disclosed: payoffs against the share including
oneself (`z/N`), as in `StochasticStability.lean`.

## Step 2: mechanical checks
* `lake build EconLean` against the shared tree: success, 7842 jobs, no warnings.
* `#print axioms` on all 16 blueprint names: only propext, Classical.choice, Quot.sound.
* `leanchecker` on KMRDarwin, KMRChain, BehavioralXVI: pass.
* `leanexport` + `nanoda`: 16506 declarations, no typechecker errors.
* Blueprint: `leanblueprint pdf` and `web` succeed, no undefined references.
