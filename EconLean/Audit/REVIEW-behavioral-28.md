# Review: behavioral round 28 (GumbelLogit)

Date: 2026-11-25. Files: `Behavioral/GumbelLogit.lean` (new); header-only edits to `Behavioral/StochasticChoice.lean`
(McFadden pointer) and `Behavioral/RDURiskAttitude.lean` (stale scope line); frozen `Audit/Statements/BehavioralXXVIII.lean`.
Closes catalog A4.12/C5.1 "logit = Gumbel random utility".

## Adversarial statement review (context-isolated agent)
Checked against McFadden (1974), Train (2009) §3.10.
- No MAJOR findings. Gumbel CDF/density/measure correct; `gumbel_choice` (product measure, ≤ event, softmax 1)
  and `gumbel_choice_indep` (iIndepFun, laws = gumbel) correct and non-vacuous; helper lemmas true with the
  stated S-conditions.
- MINOR (fixed): header no longer claims "ties have probability zero" as a stated result.
- MINOR (not adopted): `[IsProbabilityMeasure P]` and measurability in `gumbel_choice_indep` are partly
  redundant; harmless.

## Mechanical checks
- Full `lake build EconLean` on the shared tree: success (7956 jobs), no warnings.
- `#print axioms` (15 library + 15 frozen): only propext, Classical.choice, Quot.sound.
- `leanchecker` on GumbelLogit, StochasticChoice, RDURiskAttitude, BehavioralXXVIII: exit 0.
- `leanexport` + nanoda: 38738 declarations, no typechecker errors.
- Blueprint: thm:beh-gumbel-logit at end of "Stochastic choice"; pdf and web build; no new undefined refs.
