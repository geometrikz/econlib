# Review: econometrics batch 4

Files: `EconLean/Econometrics/Asymptotics/{MLE,GaussianLimits,JTest}.lean`, `GLS.lean`,
`Structural/BLPContraction.lean`, `TimeSeries/SVARRestrictions.lean` (horizon signs, zero restrictions).
Blueprint: `chapters/econometrics4.tex`.

## Step 1: context-isolated adversarial statement review

A fresh agent saw only the proof-stripped statements (`verify/strip_proofs.py`) and the prompt in
`verify/REVIEW_PROMPT.md` (econometrics references). Full table:
`Audit/independent-econometrics4-statement_review.md`.

Verdict: no false statement and no contradictory hypothesis set; every theorem has a nondegenerate witness.
Findings and how they were handled:

| # | Finding | Action |
|---|---------|--------|
| 1 | J test: χ²(l−k) law not stated, only mean l−k and the idempotent structure | Documented as open (Mathlib has no χ²); CATALOG C2.7 says so |
| 2 | `mle_consistent_of_density`: ULLN and continuity assumed, criterion abstract | Docstring now says so; CATALOG C2.6 stays 🟢 |
| 3 | `mle_limit_law`: information equality assumed | Docstring now says so |
| 4 | Order-condition uniqueness witness fails positive-diagonal normalisation | Added `order_condition_continuum`: continuum of orthogonal `diag(1, R_θ)` with positive diagonal for abs θ < π/2 |
| 5 | BLP: mixed-logit existence assumed; `hs` redundant | `hs` removed (derived from `hstar`); existence documented as open |
| 6 | `integral_sandwich_sq` is the infeasible estimator | Docstring points to residual bias and HC2 |
| 7 | `neweyWest` unnormalised, not demeaned | Docstring says so (irrelevant for PSD) |
| 8 | Horizon signs: Φ abstract, weak inequality, bookkeeping only | Accepted; RWZ rank condition listed open in C4.3 |
| 9 | Existence counterexample violates RWZ per-column count | Accepted: it illustrates that the total count is not sufficient, which is the claim |
| 10 | `S` names sample Jacobian in `jStat_tendsto` but long-run variance in `jForm` | Docstring clarifies |

## Step 2: proof reverifiers

- `#print axioms` on all 101 declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- `lake env leanchecker` on the 6 modules: pass.
- nanoda on the export closure: 59,792 declarations, no typechecker errors.
- `lake build` of the full library: warning-free. `leanblueprint pdf`: builds, 0 undefined references.

Comparator (`verify/check.sh`) runs at integration after `make_challenge.py`.
