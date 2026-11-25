# Review: behavioral round 23 (risk attitudes under rank-dependent utility)

Files: `Behavioral/RDURiskAttitude.lean` (new). Frozen statements: `Audit/Statements/BehavioralXXIII.lean` (10 statements).

## Step 1: adversarial statement review (context-isolated agent, 2026-11-25)
No MAJOR findings. The reviewer confirmed that with the decumulative convention (weight w(G k) − w(G (k+1))),
w(t) ≤ t is pessimism (Yaari risk aversion; Wakker), checked `binLot`, `rdu_le_eu_iff`, `rdu_le_u_mean` (pessimism +
Jensen) and the Chew–Karni–Safra necessity theorem (non-vacuous: U = id, w = t²). MINOR fixes applied:
- Header no longer claims `x` is increasing (only `U ∘ x` is assumed monotone).
- `pessimism_of_riskAverse`: stake bound ε now chosen per t (weaker hypothesis).
- Added `rdu_sq_le_eu` (t² gives RDU ≤ EU); replaced the trivial `exists_rdu_gt_eu` by `yaari_riskSeeking`
  (optimistic w makes a linear-utility agent strictly risk seeking); inverse-S marked as not formalized.
- Not done: weakening `HasDerivAt` to a right derivative.

## Step 2: mechanical checks
- `#print axioms` on 11 declarations: only propext, Classical.choice, Quot.sound.
- `leanchecker` on RDURiskAttitude and BehavioralXXIII: exit 0.
- `leanexport` + nanoda: 16313 declarations, no typechecker errors (one benign "Unable to print axioms").
- `lake build EconLean` on the shared tree with these files: success (7932 jobs).
- Blueprint `leanblueprint pdf` and `web` succeed; new label `thm:beh-rdu-risk`.
