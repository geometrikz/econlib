# Adversarial review: macro batch 11 (CAPM, Modigliani–Miller, THANK, CIA Friedman rule)

Files: `Finance/CAPM.lean`, `Finance/ModiglianiMiller.lean`, `Macro/NK/THANK.lean`,
`Macro/Monetary/CashInAdvance.lean`.

Reviewer: context-isolated agent, given statements only (proofs elided), 2026-11-24.
Core formulas checked: CAPM beta pricing, MM II, Bilbiie's `δ = (1−λ)/(1−λχ)` and the
`χ > 1` condition, the cash–credit FOC `U₁' = (1+i)U₂'`. No sign errors, no blocking issues.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| CAPM-1 | should-fix | Quadratic utility not modelled; `u₀` free. | Added `hasDerivAt_quadU` (`u = −(κ−c)²/2`, `u' = κ − c`), `quadSDF = β u'(W R_m)/u'(c₀)` with `c₀ < κ`; `linearSDF_of_quadratic` proves it is affine with `b > 0`. |
| CAPM-2 | nit | `capm_of_quadratic` restated `beta_pricing`. | Now also concludes a positive market premium. |
| CAPM-3 | nit | `beta_pricing` is the general linear-SDF result. | Documented (Cochrane §9). |
| MM-1 | should-fix | `mm_I` is linearity for any `m`. | Documented as an accounting identity; `mm_I_market` (no arbitrage ⇒ costs add up, via `ftap`) presented as the theorem. |
| MM-2 | should-fix | `mm_II` restricted to riskless debt. | Generalized to risky debt with `r_D` the expected debt return; `hrisk` dropped. |
| MM-3 | nit | `mm_II_mono` standalone. | Docstring ties it to the MM II equity return. |
| MM-4 | nit | Limited liability not imposed. | Documented (not needed for the identities). |
| TH-1 | should-fix | `impact` was `aggregate_IS` at `t = 0`. | Replaced: if `y_T = 0`, `y_0 = −δσ Σ_{t<T}(r_t − r^n_t)`. |
| TH-2 | nit | Perfect foresight; `χ` reduced form; demand block only. | Documented; title says "aggregate demand block". |
| TH-3 | nit | Non-vacuity example only for RANK. | Added `λ = 1/2`, `χ = 3/2` example (`δ = 2`) with an equilibrium path. |
| CIA-1 | should-fix | No existence: results could be vacuous. | Added `hpos₁` and Inada conditions to `Env`; `existsUnique_eq`: unique interior equilibrium for every `i ≥ 0` (Darboux + strictly decreasing wedge). |
| CIA-2 | should-fix | `nominalRate` disconnected from policy. | Added `IsEqμ` and `friedman_rule_μ`: among `μ ≥ β − 1`, efficient iff `μ = β − 1`. |
| CIA-3 | should-fix | Mislabelled as Lucas–Stokey (1983). | Citation changed to the Lucas–Stokey (1987) cash–credit model as in Walsh / Ljungqvist–Sargent; docstring notes it is not the LS83 optimal-tax result. |
| CIA-4 | nit | `IsEq` allows `i < 0`. | Documented; all results assume `i ≥ 0`. |

Checks after fixes: all four files compile warning-free; `#print axioms` standard
only; leanchecker and nanoda pass.
