# Adversarial review: macro batch 10 (innovation-driven growth, modern trade)

Files: `Macro/Growth/AghionHowitt.lean`, `Macro/Growth/DirectedTechChange.lean`,
`Macro/Trade/EatonKortum.lean`, `Macro/Trade/Melitz.lean`.

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-23.
All formulas checked against the sources (AH arbitrage and `n*`; DTC `N* = η^σ x^{σ−1}`,
wage exponent `σ − 2`; EK share `Φ_i/Φ`, Gamma moment with `σ < 1 + θ`; Melitz `Λ`, Pareto `J`).
No sign errors or contradictory hypotheses.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| AH-1 | should-fix | Uniqueness stated for the bare arbitrage equality over all reals; corner `n = 0` not captured. | Added `IsEquilibrium` (complementary slackness, `0 ≤ n ≤ L`), `isEquilibrium_iff` (`n = max 0 n*`), `existsUnique_equilibrium`, `interior`, and `nStar_lt_L`. |
| AH-2 | should-fix | `no_research` did not show `n = 0` is the equilibrium. | Restated: `IsEquilibrium n ↔ n = 0` when `λγθL ≤ r`. |
| AH-3 | nit | Comparative statics in `λ`, `θ` missing. | Not added (`n*` depends on `γθ`; the `γ` result covers the same channel). |
| DTC-1 | nit | `σ` is the derived elasticity; normalization. | Documented. |
| EK-1 | should-fix | `priceIndex_eq` was only a power identity. | Defined `priceIndex` as `(E p^{1−σ})^{1/(1−σ)}` (the integral) and `gammaConst`; `priceIndex_eq` now proves `priceIndex = γ Φ^{−1/θ}` via `price_moment`. |
| EK-2 | should-fix | `real_wage` was a standalone identity. | Now stated for sources with `Φ_k = T_k (w_k d_k)^{−θ}`, `d_n = 1`, domestic share `Φ_n/ΣΦ` and the defined `priceIndex`. |
| EK-3 | nit | Fréchet never appears. | Added `frechet_to_exp` (change of variables) and docstring. |
| EK-4 | nit | `trade_shares_sum`, `survival_min` trivial. | Kept as helpers. |
| MZ-1 | nit | Density without support indicator. | Documented; every use is guarded by `φ ≥ φ_min`. |
| MZ-2 | nit | `exporter_share` not tied to the survival function. | Added `surv` with `surv_eq_integral` (`∫_φ^∞ pdf = surv φ`); `exporter_share` stated with `surv`. |
| MZ-3 | nit | Cutoffs assumed interior. | Kept as hypotheses (documented). |

Checks after fixes: all four files compile warning-free; `#print axioms` standard
only; leanchecker and nanoda pass.
