# Adversarial review: macro batch 15 (Atkinson–Stiglitz, Diamond–Mirrlees)

Files: `Macro/PublicFinance/AtkinsonStiglitz.lean`, `Macro/PublicFinance/DiamondMirrlees.lean`.

Two rounds of context-isolated review (statements only), 2026-11-24.

## Round 1

| # | Severity | Finding | Resolution |
|---|---|---|---|
| AS-1 | blocking | All consumer-theory facts (`V(q,c_j) = v x_j`, duality `V p (e u) = u`, `e(v x) ≤ p·x`) were bare assumptions in a structure. | `V` and `e` are now defined as a supremum over the budget set and an infimum of costs; `V_of_optimal`, `e_le` and `V_e` (duality, from continuity of `v`, `p > 0` and `v 0 ≤ u`) are proved. |
| AS-2 | should-fix | Name claimed more than Laroque's dominance lemma; `ic_iff` not in the main statement. | Renamed `income_tax_dominates`, which includes payoffs, the IC equivalence and revenue. |
| AS-3 | should-fix | New net income not shown to be an income schedule. | `c'_schedule`; docstring notes `κ = ℝ` covers off-menu deviations. |
| AS-4 | nit | Revenue only option by option. | `aggregate_revenue_ge`. |
| AS-5 | nit | Weak non-vacuity witness. | `example_regime` with a nonzero commodity tax. |
| DM-1 | should-fix | Conclusion was the topological boundary only. | `weakly_efficient`: with free disposal, no feasible plan strictly dominates `x(q*) + g`; `mem_frontier` kept. |
| DM-2 | should-fix | Nonsatiation at the unknown optimum; name `_of_deriv`. | Renamed `weakly_efficient_of_price_decrease`; docstring: holds whenever price cuts raise welfare at every price (as in the example). |
| DM-3 | nit | Price domain, profits and budget implicit. | Admissible set `Q` with `q* ∈ interior Q`; scope documented. |
| DM-4 | nit | No non-vacuity witness. | `example_one_good`, `example_efficient` (the theorem applied). |

## Round 2 (after the rewrite)

No blocking issues. Fixed: the expenditure-attainment assumption was redundant and is now
proved by compactness (`exists_expenditure_min`); `hdec` is required only at the optimum
(strictly more general); the example applies the theorem directly; docstrings note Lean's
`sSup`/`sInf` junk values, which no result uses.

Checks: both files compile warning-free; `#print axioms` standard only (24 declarations);
leanchecker passes on all three modules; nanoda checked 15565 declarations with no
typechecker errors.
