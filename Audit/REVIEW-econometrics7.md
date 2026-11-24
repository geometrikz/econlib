# Review: econometrics batch 7

Files: `EconLean/Econometrics/Asymptotics/FirstStepGMM.lean`,
`TimeSeries/{WhiteNoise,KalmanRecursion,YuleWalkerPD}.lean`. Blueprint: `chapters/econometrics7.tex`.

## Step 1: context-isolated adversarial statement review

A fresh agent saw only the proof-stripped statements (`verify/strip_proofs.py`) and checked them against Hansen (1982),
White (1980), Hayashi Prop. 3.4–3.6, Newey–McFadden, Kalman (1960), Hamilton §3.4/§13.2/§13.5, Anderson–Moore §3.1/§4.4
and Brockwell–Davis §5.1. Full table: `Audit/independent-econometrics7-statement_review.md`.

Verdict: no false or contradictory statement. The residual-based Ŝ, the Riccati map, the filter recursion and the
Toeplitz matrix match the textbook objects. Findings and handling:

| # | Finding | Action |
|---|---------|--------|
| D1 | `two_step_feasible_witness` is just-identified (weighting and J trivial); CLT holds exactly | Documented in module docstring and blueprint; overidentified abstract witness is `two_step_witness` (l = 2, S = diag(1,2)). Overidentified data-level witness open |
| C1 | J limit: mean l − k, not the χ²(l − k) law | Open (Mathlib has no χ²) |
| C2 | Steady state assumes boundedness, only P₀ = 0, no uniqueness/closed-loop stability | Documented; open |
| C3 | Kalman optimality over gain sequences missing | Added `gainCov`, `filter_mse` (any gains), `kalman_optimal_gains` |
| C4 | Toeplitz result is not B–D Prop. 5.1.1 | Citation changed to "cf. B–D §5.1", difference stated |
| C5 | White-noise Toeplitz witness is the identity | Added `ma1_witness` (tridiagonal Γ) |
| C6 | `sHat_consistent` assumes convergence where boundedness in probability suffices | Documented (stronger hypothesis, still standard) |
| C7 | Riccati map takes junk values where S is singular | All theorems assume R ≻ 0 or S invertible where it matters |
| C8–C10 | Witness strength | MSE witness now nondegenerate (Rademacher noise); steady-state witness computes the golden ratio |

## Step 2: proof reverifiers

- `#print axioms` on all 70 declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- `lake env leanchecker` on the 4 modules: pass.
- nanoda on the export closure: 60,377 declarations, no typechecker errors.
- Full `lake build`: warning-free (also checked with `autoImplicit=false`). `leanblueprint pdf`: builds, 0 undefined
  references in the final pass.

Comparator (`verify/check.sh`) runs at integration after `make_challenge.py`.
