# Review record: behavioral round 13 (2026-11-24)

Module: `EconLean/BoundedRationality/ESSUniform.lean` (Weibull 1995 Props 2.5 and 2.6).
Frozen statements: `EconLean/Audit/Statements/BehavioralXIII.lean` (7 statements).

## Step 1: adversarial statement review (context-isolated agent)
No MAJOR findings. Verified: the barrier in `isESS_iff_uniform` is chosen before the
mutant (truly uniform); local superiority is relative to the simplex with the right
inequality; `exists_ray` and `advantage_ray` checked by hand; no vacuous hypotheses.
MINOR, fixed: `hawkDove_uniform` renamed `hawkDove_uniform_locallySuperior` and listed in
the header; `le_one_of_mem` renamed `lotteries_le_one`; header now says `IsESS` is the
payoff-comparison definition and `isESS_iff_invasion` is the per-mutant barrier version.
MINOR, kept: Hawk–Dove witness assumes `0 < V` (textbook interior case).

## Step 2: mechanical checks
* `lake build EconLean` against the shared tree: success, 7768 jobs, no warnings.
* `#print axioms` on all 14 blueprint names: only propext, Classical.choice, Quot.sound.
* `leanchecker` on ESSUniform and BehavioralXIII: pass.
* `leanexport` + `nanoda`: 14651 declarations, no typechecker errors.
* Blueprint: `leanblueprint pdf` and `web` succeed, no undefined references.
