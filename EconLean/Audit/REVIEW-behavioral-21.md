# Review: behavioral round 21 (salience theory and the common-ratio effect)

Files: `Behavioral/SalienceCommonRatio.lean` (new). Frozen statements: `Audit/Statements/BehavioralXXI.lean` (14 statements).

## Step 1: adversarial statement review (context-isolated agent, 2026-11-25)
No MAJOR findings. The reviewer hand-checked the KT problems 3/4 encoding, the independent joint distribution,
saliences, ranks, closed-form sums (roots of the B sum ≈ 1.10 and 10.9), signs and `eu_no_common_ratio`.
MINOR fixes applied:
- Header attributes the "most salient state" claims to `salience_CA/CB`, `ranks_CA/CB`, and states the sign convention.
- Added `common_ratio_prefers`: the pattern via `Prefers` (weak one way, not the other) for BGS's range 0 < δ < 3/4.
- Not done: structural (index-built) independence statement; `crB_product` is a literal equation.

## Step 2: mechanical checks
- `#print axioms` on 17 declarations: only propext, Classical.choice, Quot.sound.
- `leanchecker` on SalienceCommonRatio and BehavioralXXI: exit 0.
- `leanexport` + nanoda: 9476 declarations, no typechecker errors (one benign "Unable to print axioms").
- `lake build EconLean`: success (7910 jobs) after locally dropping the import of
  `Econometrics/Asymptotics/TestPower`, which another thread has listed in the shared `EconLean.lean`
  but whose file is not in the shared tree yet.
- Blueprint `leanblueprint pdf` and `web` succeed; new label `thm:beh-salience-common-ratio`.
