# Adversarial review: macro batch 12 (Saez top rate, inverse Euler, granularity, rare disasters)

Files: `Macro/PublicFinance/SaezTopRate.lean`, `Macro/PublicFinance/InverseEuler.lean`,
`Macro/Granularity.lean`, `Finance/RareDisasters.lean`.

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-24.
Core formulas checked: Saez `τ* = (1−ḡ)/(1−ḡ+ae)`, the inverse Euler equation
`1/u'(c₀) = (1/βR) E[1/u'(c₁)]` and the sign of the savings wedge, `Var = σ² Σ s²`,
the Barro premium ratio and two-point covariance. No sign errors, no blocking issues.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| IE-1 | should-fix | `Σ π = 1` missing; utility and incentive neutrality of the perturbation only in prose. | Added `utility_neutral` (with `Σ π = 1`, lifetime utility is constant in `Δ`) and `incentive_neutral` (state utility differences unchanged). |
| IE-2 | nit | `savings_wedge` not linked to `inverse_euler`. | Added `inverse_euler_wedge` composing them with `u' = 1/h'`. |
| SZ-1 | should-fix | `dSW` asserted, not derived from welfare; "optimal" rested on the name. | Added `welfare_hasDerivAt` (envelope decomposition: `τ(Z−z*) + ḡV` with `Z' = −eZ/(1−τ)`, `V' = −(Z−z*)` has derivative `dSW`), `welfare_hasDerivAt_dSW`, explicit `welfare` with `W' = dSW`, and `topRate_isMaxOn`: `τ*` maximizes `W` on `[0,1)`. |
| SZ-2 | nit | Pareto mean not connected to `zbar`. | Added `zbar_eq_integral`. |
| SZ-3 | nit | `e > 0` excludes `e = 0`. | Documented (`τ* = 1` then). |
| GR-1 | should-fix | Gabaix's `1/log N` rate missing; bounds trivial. | Added `var_equal` (`Var = σ²/N` for equal shares), Zipf shares `zipf`, `zipf_sum`, `zipf_herfindahl` (`h² ≥ 1/(1+log N)²`) and `var_zipf_ge`. Upper bound documented as not formalized. |
| GR-2 | nit | `hv` redundant; Domar weights sum to more than one. | `hv` dropped from `granular_bound` (derived); Domar remark added. |
| RD-1 | should-fix | `riskfree_anti_p` did not mention `Rf` or fix `β`. | Renamed the old lemma `E_mu_strictMono_p`; `riskfree_anti_p` now assumes `β' = β` and concludes `R_f' < R_f`. |
| RD-2 | nit | Strip vs tree, leverage, lognormal shocks undocumented. | Docstring explains the i.i.d. strip/tree equivalence and the simplifications. |
| RD-3 | nit | `premium_zero` trivial. | Kept as a sanity check, documented. |

Checks after fixes: all four files compile warning-free; `#print axioms` standard
only (57 declarations); leanchecker passes on all five modules; nanoda checked
43753 declarations with no typechecker errors.

Follow-up (batch 13 review, 2026-11-24): `var_zipf_ge` no longer takes `hv : 0 ≤ v`
(it is derived from `hcov` by `v_nonneg`); the frozen statement was strengthened
accordingly by dropping that hypothesis.
