# Review: econometrics batch 5

Files: `EconLean/Econometrics/TimeSeries/{ARMA,Kalman}.lean`, `Asymptotics/DeltaMethodVec.lean`.
Blueprint: `chapters/econometrics5.tex`.

## Step 1: context-isolated adversarial statement review

A fresh agent saw only the proof-stripped statements (`verify/strip_proofs.py`) with an econometrics version of
`verify/REVIEW_PROMPT.md`. Full table: `Audit/independent-econometrics5-statement_review.md`.

Verdict: no false statement, no unsatisfiable hypothesis set, no junk-value truths. Index conventions of the companion
matrix, characteristic equation and lag polynomial confirmed against Hamilton Prop. 1.1. Findings and handling:

| # | Finding | Action |
|---|---------|--------|
| 1 | ARMA solution results are pathwise for bounded inputs; i.i.d. Gaussian noise is a.s. unbounded; L² stationary solution (B–D 3.1.1) not stated | Documented in module docstring and blueprint; open |
| 2 | `IsARMA` is AR(p+1) with forcing; ψ-weights θ/φ not computed | Documented; open |
| 3 | Kalman: no multi-period recursion, Riccati steady state, or conditional-expectation form | Documented; open |
| 4 | Gain optimality lacked uniqueness | Added `kalman_gain_unique` (R positive definite) |
| 5 | MA(∞) result does not identify ψⱼ, mean, autocovariances | Open (Yule–Walker etc. for a later batch) |
| 6 | Delta method only at rate √n | Documented |
| 7 | No one-statement Gaussian vector delta method | Added `delta_method_vec_gaussian`; `delta_method_gaussian` docstring reworded |
| 8 | No result that explosive / unit-root ARs lack bounded solutions | Open |
| 9 | Invertibility of S not derived from R positive definite | Added `innovCov_posDef`, `isUnit_innovCov` |
| 10 | Soundness depends on Mathlib's `gelfandRadius` | Checked: it is the Fekete limit of ‖aᵏ‖^(1/k) (`tendsto_gelfandRadius`), equal to the spectral radius over ℂ (`spectralRadius_eq_gelfandRadius`) |

## Step 2: proof reverifiers

- `#print axioms` on all 58 declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- `lake env leanchecker` on the 3 modules: pass.
- nanoda on the export closure: 60,141 declarations, no typechecker errors.
- Full `lake build`: warning-free. `leanblueprint pdf`: builds, 0 undefined references.

Comparator (`verify/check.sh`) runs at integration after `make_challenge.py`.
