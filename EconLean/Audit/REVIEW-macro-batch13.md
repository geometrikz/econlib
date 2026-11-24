# Adversarial review: macro batch 13 (two-type optimal income tax, Ramsey commodity taxes, intertemporal Keynesian cross, Zipf granularity)

Files: `Macro/PublicFinance/TwoTypeMirrlees.lean`, `Macro/PublicFinance/RamseyCommodityTax.lean`,
`Macro/IKC.lean`, `Macro/Granularity.lean` (new upper bound).

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-24.
Core formulas checked by hand: the welfare decomposition `S − κ(U_H − U_L)`, the bottom FOC
and the sign of the bottom wedge, the Lagrange step of the Ramsey rule, `t/q = c/ε`, the IKC
algebra and `pv_budget`, the Zipf bounds `Σ 1/i² ≤ 2 − 2/(N+1)` and `H_N ≥ log(N+1)`.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| IKC-1 | blocking | Invertibility of `I − M` is incompatible with the PV condition `qᵀM = qᵀ`, so existence/uniqueness and the balanced-budget theorem never applied to ARS matrices. | Added `not_isUnit_of_pv` (the tension as a theorem); `balanced_budget_isEq` (`dY = dG` is an equilibrium for **every** `M`) and `balanced_budget_iff` (all equilibria differ by `ker(I − M)`); the unique-equilibrium results are documented as the truncated/invertible case, with `static_isUnit` as an instance. |
| IKC-2 | should-fix | `existsUnique_eq` had trivial uniqueness (the formula was a conjunct). | Now `∃! dY, IsEq M dG dT dY`; formula moved to `isEq_iff_inv`. |
| IKC-3 | nit | Mixed hypotheses (`IsUnit det` vs injectivity); `q = 0` allowed. | `balanced_budget` now uses `IsUnit det` and follows from uniqueness; `not_isUnit_of_pv` requires `q ≠ 0`; `pv_budget` is true for any `q`. |
| RT-1 | should-fix | Ordering by elasticity only under an unproved `c > 0`. | Added `inverse_elasticity_pos`: positive revenue, prices, demands and elasticities imply `c > 0` and the unconditional ordering. |
| RT-2 | nit | `ramsey_rule` is the separable case only. | Scope documented in the module docstring. |
| MI-1 | should-fix | FOCs were for the relaxed problem only. | Added `IsOptimum` (full program with both ICs), `optimum_welfare_eq` (ICH binds), `optimum_isLocalMax_top/bottom` (no bunching ⇒ local max of `W`), and `optimum_no_distortion_top`, `optimum_bottom_tax_pos` stated for the full program. |
| MI-2 | nit | `g_H` could be negative. | Added `hgH : 0 ≤ gH`. |
| MI-3 | nit | `v'` tied to `v` only at two points. | Full-program versions assume `∀ x > 0, HasDerivAt v (v' x) x`. |
| GR-1 | nit | `hv` redundant in Zipf bounds. | Dropped; `v_nonneg` derives it (also in the batch 12 frozen statement). |
| GR-2 | nit | Bounds, not Gabaix's sharp constant; deterministic rank-size shares. | Documented. |

Checks after fixes: all four files compile warning-free; `#print axioms` standard only
(56 declarations); leanchecker passes on all five modules; nanoda checked 44589
declarations with no typechecker errors.
