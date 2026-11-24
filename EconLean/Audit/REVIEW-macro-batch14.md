# Adversarial review: macro batch 14 (Thomas–Worrall, Goldstein–Pauzner, BGG accelerator)

Files: `Macro/Contracts/ThomasWorrall.lean`, `Macro/Banking/GoldsteinPauzner.lean`,
`Macro/Credit/FinancialAccelerator.lean`.

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-24.
Checked by hand: the KKT-to-clamp step, path dynamics, GP's payoff difference (including the
sequential-service branch `−1/n`), `A_eq`, the direction of the `r` comparative static, BGG's
capital-market condition and its comparative statics. No blocking issues.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| GP-1 | should-fix | `p ≤ 1` not required. | Added `hp_le`. |
| GP-2 | should-fix | No global game modelled; uniqueness of the run equilibrium not proved. | Docstring: `θ*` is the Laplacian-limit threshold; GP Theorem 1 (limit and uniqueness) is assumed; `existsUnique_threshold` is uniqueness of the root of `A`. |
| GP-3 | should-fix | `r` comparative statics only weak. | Added `A_strictAnti_r` (strict on `[λ, 1/r']`, via `integral_lt_integral_of_continuousOn_of_le_of_exists_lt`); `threshold_mono_r` now strict. |
| GP-4 | nit | Linear utility: no risk-sharing side of the trade-off. | Documented. |
| BGG-1 | should-fix | Premium not shown countercyclical over the cycle; can be procyclical. | Docstring now claims only "falls with net worth at given productivity" and notes the procyclical case. |
| BGG-2 | should-fix | `amplification` is static; second conjunct restated the first. | Now `K₁ < K₂' ∧ K₂' < K₂`; documented as the static net-worth channel (no `Q` channel or dynamics). |
| BGG-3 | nit | No level condition on `s`. | Added `hs1 : 1 ≤ s x`; `premium_example_ge`. |
| TW-1 | should-fix | Missing long-run confinement when intervals do not overlap. | Added `eventually_mem_Icc_B_A`. |
| TW-2 | nit | Deterministic states, exogenous bounds, additive multiplier form, `x₀` unclamped. | Documented. |

Checks after fixes: all three files compile warning-free; `#print axioms` standard only
(50 declarations); leanchecker passes on all four modules; nanoda checked 42284
declarations with no typechecker errors.
