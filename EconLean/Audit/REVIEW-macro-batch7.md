# Review record: macro batch 7 (2026-11-23)

Files: Macro/DSGE/SaddlePath.lean, Macro/Fiscal/RamseyPrimal.lean,
Macro/BaqaeeFarhiNested.lean, Macro/Fiscal/Ricardian.lean,
Macro/Fiscal/TaxSmoothing.lean, Macro/Monetary/BarroGordon.lean,
Macro/NK/Calvo.lean, Macro/Trade/ACR.lean, Finance/HolmstromTirole.lean.
Frozen statements: Audit/Statements/MacroBatch7.lean (13).

## Step 1: context-isolated adversarial statement review
The referee saw statements, docstrings and the background definitions only.

| # | Finding | Severity | Resolution |
|---|---------|----------|------------|
| 1 | `RamseyPrimal.Feasible` had no c ≥ 0 or k ≥ 0. Every summable c′ was feasible, so `IsOptimal` forced W′(cₜ) = 0, making `chamley_judd_primal` vacuously true and `planner_euler` trivial. | FALSE (vacuous) | `Feasible` now requires c ≥ 0 and k ≥ 0. `planner_euler` takes interiority (cₛ, cₛ₊₁, kₛ₊₁ > 0) and uses only small perturbations (continuity of F). `nonvacuous` proves an interior optimum (β = 1/2, W = id, F = 2k, c = k = 1) via a telescoping bound and satisfies every hypothesis of `chamley_judd_primal`. |
| 1b | Not exactly Chari–Kehoe: same W at every date (no date-0 levy term), W not tied to u, household Euler assumed | MISLEADING | Stated in the docstring deviations. |
| 2 | `not_ricardian_of_constraint` only showed that the budget sets differ | MISLEADING | Now exhibits U = −(c₀−1)² − (c₁−1)². After the tax cut, (1,1) gives U = 0, while every plan affordable without it gives U ≤ −1 < 0, so the optimum moves. |
| 3 | Baqaee–Farhi nested: θ is the elasticity only under the price-index reading (x = log productivities) | note | Interpretation paragraph added. |
| 4 | ACR imposes no equilibrium conditions | note | Docstring says `acr` is the sufficient-statistic identity, valid between any configurations. |
| 5 | Tax smoothing assumes βR = 1 | note | Already stated in the docstring. |
| 6 | Barro–Gordon did not show π = 0 is the optimal commitment | MINOR | Added `commitment_optimal`. |
| 7 | Calvo boundedness rules out trend inflation | note | Docstring deviation added. |
| 8 | Saddle: bounded vs non-explosive; repeated root also indeterminate | MINOR | Docstring notes. |
| 9 | Holmström–Tirole: p_H ≤ 1, p_L ≥ 0, entrepreneur IR not imposed | MINOR | Docstring notes; the results do not use them. |

Verified correct by the referee (own algebra): saddle-path solution and counting rule, nested second-order formula, tax-smoothing optimum, Barro–Gordon bias λk, NKPC slope (1−θ)(1−βθ)/θ, ACR formula, Holmström–Tirole threshold.

## Step 2: proof checks
- `#print axioms`: all 64 theorems use only [propext, Classical.choice, Quot.sound].
- leanchecker: all 9 modules and the frozen-statements module return rc = 0.
- nanoda: 29,318 declarations, no typechecker errors (the "Unable to print axioms" message is the known, harmless one).
- Comparator: the frozen statements compile against the library theorems.
