# Review: behavioral round 20 (salience theory and the Allais paradox)

Files: `Behavioral/SalienceAllais.lean` (new). Frozen statements: `Audit/Statements/BehavioralXX.lean` (14 statements).

## Step 1: adversarial statement review (context-isolated agent, 2026-11-25)
No MAJOR findings. The reviewer hand-checked all numbers, joint state spaces (independent B, correlated B), saliences,
ranks, closed-form sums, signs and `eu_no_allais`. MINOR fixes applied:
- Header: given θ < 2/3, δ < 1/40 is exact for problem A; θ ≥ 2/3 not formalized; results hold for all real δ below
  the bounds (including δ ≤ 0, outside BGS's range).
- Added `allaisB_correlated_iff'` (reverse comparison) so strict choices agree in the correlated presentation.
- Added `marginals_B`: both presentations of B have the marginals of L₁' and L₂'.
- Not done: `allaisA_safe_iff` covering θ ≥ 2/3; restating `allais_paradox` via `Prefers`.

## Step 2: mechanical checks
- `#print axioms` on 20 declarations: only propext, Classical.choice, Quot.sound.
- `leanchecker` on SalienceAllais and BehavioralXX: exit 0.
- `leanexport` + nanoda: 9449 declarations, no typechecker errors (one benign "Unable to print axioms").
- `lake build EconLean` on the shared tree with these files: success (7894 jobs).
- Blueprint `leanblueprint pdf` and `web` succeed; new label `thm:beh-salience-allais`.
