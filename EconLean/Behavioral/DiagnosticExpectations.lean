/-
# Diagnostic expectations: forecast errors, revisions and overreaction

References. P. Bordalo, N. Gennaioli and A. Shleifer (2018), "Diagnostic
Expectations and Credit Cycles", *J. Finance* 73(1); P. Bordalo,
N. Gennaioli, Y. Ma and A. Shleifer (2020), "Overreaction in Macroeconomic
Expectations", *AER* 110(9); O. Coibion and Y. Gorodnichenko (2015),
"Information Rigidity and the Expectations Formation Process", *AER*
105(8).

**Setting.** An AR(1) process `x_{s+1} = ρ x_s + ε_{s+1}` with i.i.d.
zero-mean shocks of variance `s²`. Every variable in a two-period window
is a linear combination of four mutually uncorrelated zero-mean variables
`(x_{t−2}, ε_{t−1}, ε_t, ε_{t+1})`, with variances `(v, s², s², s²)`; we
represent a variable by its coefficient vector `Fin 4 → ℝ` and the
covariance is `cov`. So `x_{t−1} = (ρ, 1, 0, 0)`, `x_t = (ρ², ρ, 1, 0)` and
`x_{t+1} = (ρ³, ρ², ρ, 1)`.

Forecasts of `x_{t+1}` are formed by a linear belief rule `B = (m, θ)` from
`BeliefRule.lean` applied to the rational forecasts
`E_t x_{t+1} = ρ x_t`, `E_{t−1} x_{t+1} = ρ² x_{t−1}`,
`E_{t−2} x_{t+1} = ρ³ x_{t−2}` (the rule is linear, so it acts
coefficientwise). The Coibion–Gorodnichenko regression projects the forecast
error `FE = x_{t+1} − Ê_t x_{t+1}` on the forecast revision
`FR = Ê_t x_{t+1} − Ê_{t−1} x_{t+1}`.

**Results.**
* `cov_FE_FR`: for any linear rule,
  `Cov(FE, FR) = s² ρ² [(1 − m − θ)(m + θ) − θ(1 − m) ρ²]`.
* `cov_FE_FR_diagnostic`: diagnostic expectations give
  `Cov(FE, FR) = −θ(1 + θ) ρ² s² < 0` for `θ > 0`: **overreaction**, the
  negative CG coefficient documented by Bordalo et al. (2020) for individual
  forecasters (`cgCoeff_neg_iff`).
* `cov_FE_FR_cognitive`: uniform shrinkage (`cognitive m`, applied with the
  same factor `m` at every horizon; this is not Gabaix's horizon-dependent
  `m^h`) gives `(1 − m) m ρ² s² > 0` for `m ∈ (0, 1)`: **underreaction**, the
  sign of the positive consensus coefficient of Coibion–Gorodnichenko (who
  derive it from sticky or noisy information, not from shrinkage).
* `cov_FE_FR_rational`: rational expectations give `0`.
* `fe_orthogonal_iff`: forecast errors are uncorrelated with all date-`t`
  information iff the rule is rational.
* Asset prices (BGS 2018): a claim paying `x_{t+k}` with discount `δ`
  priced with diagnostic forecasts at every horizon responds to a unit shock
  by `(1 + θ) c` on impact and `ρ^k c` afterwards, where
  `c = δρ/(1 − δρ)` is the rational response (`hasSum_priceIRF`): the price
  **overreacts on impact and then reverts** (`price_overreaction`,
  `price_reversal`), so the return after good news is predictably low.
-/
module

public import EconLean.Behavioral.BeliefRule
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

namespace Econ

namespace Diagnostic

open BeliefRule

/-- A variable in the window, as coefficients on
`(x_{t−2}, ε_{t−1}, ε_t, ε_{t+1})`. -/
abbrev Var := Fin 4 → ℝ

/-- Covariance: the four basic variables are uncorrelated, with variances
`v` (for `x_{t−2}`) and `s2` (for each shock). -/
def cov (v s2 : ℝ) (a b : Var) : ℝ := v * a 0 * b 0 + s2 * (a 1 * b 1 + a 2 * b 2 + a 3 * b 3)

/-- `x_{t−2}`. -/
def xm2 : Var := ![1, 0, 0, 0]
/-- `x_{t−1} = ρ x_{t−2} + ε_{t−1}`. -/
def xm1 (ρ : ℝ) : Var := ![ρ, 1, 0, 0]
/-- `x_t`. -/
def x0 (ρ : ℝ) : Var := ![ρ ^ 2, ρ, 1, 0]
/-- `x_{t+1}`. -/
def x1 (ρ : ℝ) : Var := ![ρ ^ 3, ρ ^ 2, ρ, 1]
/-- The shock `ε_t`. -/
def εt : Var := ![0, 0, 1, 0]

/-- The subjective forecast `Ê_t x_{t+1}`. -/
def fcT (B : Linear) (ρ : ℝ) : Var := fun k => B.forecast (ρ * x0 ρ k) (ρ ^ 2 * xm1 ρ k)

/-- The subjective forecast `Ê_{t−1} x_{t+1}`. -/
def fcT1 (B : Linear) (ρ : ℝ) : Var := fun k => B.forecast (ρ ^ 2 * xm1 ρ k) (ρ ^ 3 * xm2 k)

/-- Forecast error `x_{t+1} − Ê_t x_{t+1}`. -/
def FE (B : Linear) (ρ : ℝ) : Var := x1 ρ - fcT B ρ

/-- Forecast revision `Ê_t x_{t+1} − Ê_{t−1} x_{t+1}`. -/
def FR (B : Linear) (ρ : ℝ) : Var := fcT B ρ - fcT1 B ρ

/-- The Coibion–Gorodnichenko coefficient: the slope of the forecast error on
the forecast revision. -/
def cgCoeff (B : Linear) (ρ v s2 : ℝ) : ℝ :=
  cov v s2 (FE B ρ) (FR B ρ) / cov v s2 (FR B ρ) (FR B ρ)

theorem FE_eq (B : Linear) (ρ : ℝ) :
    FE B ρ = ![(1 - B.m) * ρ ^ 3, (1 - B.m) * ρ ^ 2, (1 - B.m - B.θ) * ρ, 1] := by
  funext k; fin_cases k <;>
    simp [FE, fcT, x1, x0, xm1, Linear.forecast] <;> ring

theorem FR_eq (B : Linear) (ρ : ℝ) : FR B ρ = ![0, -B.θ * ρ ^ 2, (B.m + B.θ) * ρ, 0] := by
  funext k; fin_cases k <;>
    simp [FR, fcT, fcT1, x0, xm1, xm2, Linear.forecast] <;> ring

/-- **Covariance of forecast errors and revisions** for a general linear
belief rule. -/
theorem cov_FE_FR (B : Linear) (ρ v s2 : ℝ) :
    cov v s2 (FE B ρ) (FR B ρ) =
      s2 * ρ ^ 2 * ((1 - B.m - B.θ) * (B.m + B.θ) - B.θ * (1 - B.m) * ρ ^ 2) := by
  rw [FE_eq, FR_eq]; simp [cov]; ring

theorem cov_FR_FR (B : Linear) (ρ v s2 : ℝ) :
    cov v s2 (FR B ρ) (FR B ρ) = s2 * ρ ^ 2 * (B.θ ^ 2 * ρ ^ 2 + (B.m + B.θ) ^ 2) := by
  rw [FR_eq]; simp [cov]; ring

/-- Rational expectations: errors are uncorrelated with revisions. -/
theorem cov_FE_FR_rational (ρ v s2 : ℝ) : cov v s2 (FE Linear.rational ρ) (FR Linear.rational ρ) = 0 := by
  rw [cov_FE_FR]; simp [Linear.rational]

/-- Diagnostic expectations: `Cov(FE, FR) = −θ(1 + θ) ρ² s²`. -/
theorem cov_FE_FR_diagnostic (θ ρ v s2 : ℝ) :
    cov v s2 (FE (Linear.diagnostic θ) ρ) (FR (Linear.diagnostic θ) ρ) =
      -(θ * (1 + θ) * ρ ^ 2 * s2) := by
  rw [cov_FE_FR]; simp [Linear.diagnostic]; ring

/-- Cognitive discounting: `Cov(FE, FR) = (1 − m) m ρ² s²`. -/
theorem cov_FE_FR_cognitive (m ρ v s2 : ℝ) :
    cov v s2 (FE (Linear.cognitive m) ρ) (FR (Linear.cognitive m) ρ) =
      (1 - m) * m * ρ ^ 2 * s2 := by
  rw [cov_FE_FR]; simp [Linear.cognitive]; ring

/-- **Overreaction (Bordalo–Gennaioli–Ma–Shleifer 2020).** With `θ ≥ 0`,
`ρ ≠ 0` and `s² > 0`, the CG coefficient under diagnostic expectations is
negative iff `θ > 0`. -/
theorem cgCoeff_neg_iff {θ ρ v s2 : ℝ} (hθ : 0 ≤ θ) (hρ : ρ ≠ 0) (hs : 0 < s2) :
    cgCoeff (Linear.diagnostic θ) ρ v s2 < 0 ↔ 0 < θ := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hden : 0 < cov v s2 (FR (Linear.diagnostic θ) ρ) (FR (Linear.diagnostic θ) ρ) := by
    rw [cov_FR_FR]; simp only [Linear.diagnostic]; positivity
  rw [cgCoeff, div_neg_iff, cov_FE_FR_diagnostic]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_lt.2 hden.le)
    · rcases hθ.lt_or_eq with h' | rfl
      · exact h'
      · simp at h
  · intro h
    right; exact ⟨by have : 0 < θ * (1 + θ) * ρ ^ 2 * s2 := by positivity
                     linarith, hden⟩

/-- **Uniform underreaction.** With `m ∈ (0, 1)`, `ρ ≠ 0` and `s² > 0`, the CG
coefficient under horizon-independent shrinkage is positive, the sign
Coibion–Gorodnichenko (2015) find for consensus forecasts. -/
theorem cgCoeff_cognitive_pos {m ρ v s2 : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hρ : ρ ≠ 0)
    (hs : 0 < s2) : 0 < cgCoeff (Linear.cognitive m) ρ v s2 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [cgCoeff, cov_FE_FR_cognitive, cov_FR_FR]
  simp only [Linear.cognitive]
  have : 0 < 1 - m := by linarith
  positivity

/-- The subjective forecast for a general rule:
`Ê_t x_{t+1} = m ρ x_t + θ ρ ε_t`, i.e. coefficients `(mρ³, mρ², (m + θ)ρ, 0)`. -/
theorem fcT_eq (B : Linear) (ρ : ℝ) :
    fcT B ρ = ![B.m * ρ ^ 3, B.m * ρ ^ 2, (B.m + B.θ) * ρ, 0] := by
  funext k; fin_cases k <;>
    simp [fcT, x0, xm1, Linear.forecast] <;> ring

/-- **Diagnostic forecasts overreact to news**: `Ê_t x_{t+1} = ρ x_t + θ ρ ε_t`,
i.e. they exceed the rational forecast `ρ x_t` by `θ ρ ε_t`. -/
theorem fcT_diagnostic (θ ρ : ℝ) :
    fcT (Linear.diagnostic θ) ρ = ρ • x0 ρ + (θ * ρ) • εt := by
  rw [fcT_eq]; funext k
  fin_cases k <;> simp [x0, εt, Linear.diagnostic] <;> ring

/-- **Rational expectations iff unpredictable errors.** If `ρ ≠ 0` and
`s² > 0`, the forecast error is uncorrelated with every date-`t`
variable (no loading on `ε_{t+1}`) iff the rule is rational. -/
theorem fe_orthogonal_iff (B : Linear) {ρ v s2 : ℝ} (hρ : ρ ≠ 0) (hs : 0 < s2) :
    (∀ y : Var, y 3 = 0 → cov v s2 (FE B ρ) y = 0) ↔ B = Linear.rational := by
  constructor
  · intro h
    have h1 := h ![0, 1, 0, 0] rfl
    have h2 := h εt rfl
    rw [FE_eq] at h1 h2
    simp [cov, εt] at h1 h2
    have hm : B.m = 1 := by
      rcases h1 with h1 | h1 | h1
      · exact absurd h1 hs.ne'
      · linarith
      · exact absurd h1 hρ
    have hθ : B.θ = 0 := by
      rcases h2 with h2 | h2 | h2
      · exact absurd h2 hs.ne'
      · linarith
      · exact absurd h2 hρ
    cases B; simp_all [Linear.rational]
  · rintro rfl y hy
    rw [FE_eq]; simp [cov, Linear.rational, hy]

/-! ### Asset prices: overreaction and reversal -/

/-- Response, at date `t + k`, of the subjective forecast of
`x_{t+k+h}` (`h ≥ 1`) to a unit shock `ε_t`: the rational forecast responds
by `ρ^{k+h}`, and yesterday's rational forecast by `ρ^{k+h}` if `k ≥ 1`
and `0` on impact. -/
def forecastIRF (B : Linear) (ρ : ℝ) (k h : ℕ) : ℝ :=
  B.forecast (ρ ^ (k + h)) (if k = 0 then 0 else ρ ^ (k + h))

/-- Response at date `t + k` of the price `P = Σ_{h ≥ 1} δ^h Ê x_{t+k+h}`. -/
def priceIRF (θ ρ δ : ℝ) (k : ℕ) : ℝ :=
  ∑' h : ℕ, δ ^ (h + 1) * forecastIRF (Linear.diagnostic θ) ρ k (h + 1)

/-- **The diagnostic price response.** With `|δρ| < 1`, the price responds to
a unit shock by `(1 + θ) c` on impact and by `ρ^k c` at `k ≥ 1`, where
`c = δρ/(1 − δρ)`. -/
theorem hasSum_priceIRF {θ ρ δ : ℝ} (h : |δ * ρ| < 1) (k : ℕ) :
    HasSum (fun h : ℕ => δ ^ (h + 1) * forecastIRF (Linear.diagnostic θ) ρ k (h + 1))
      ((if k = 0 then 1 + θ else 1) * ρ ^ k * (δ * ρ / (1 - δ * ρ))) := by
  have hg := (hasSum_geometric_of_abs_lt_one h).mul_left
    ((if k = 0 then 1 + θ else 1) * ρ ^ k * (δ * ρ))
  convert hg using 1
  · funext n
    simp only [forecastIRF, Linear.forecast_diagnostic]
    split_ifs <;> ring
  · rw [div_eq_mul_inv]; ring

theorem priceIRF_eq {θ ρ δ : ℝ} (h : |δ * ρ| < 1) (k : ℕ) :
    priceIRF θ ρ δ k = (if k = 0 then 1 + θ else 1) * ρ ^ k * (δ * ρ / (1 - δ * ρ)) :=
  (hasSum_priceIRF h k).tsum_eq

/-- **Overreaction on impact**: relative to rational pricing (`θ = 0`), the
impact response is scaled by `1 + θ`. -/
theorem price_overreaction {θ ρ δ : ℝ} (h : |δ * ρ| < 1) :
    priceIRF θ ρ δ 0 = (1 + θ) * priceIRF 0 ρ δ 0 := by
  rw [priceIRF_eq h, priceIRF_eq h]; simp

/-- **Reversal**: after impact the price is back on the rational path. -/
theorem price_reversal {θ ρ δ : ℝ} (h : |δ * ρ| < 1) (k : ℕ) :
    priceIRF θ ρ δ (k + 1) = priceIRF 0 ρ δ (k + 1) := by
  rw [priceIRF_eq h, priceIRF_eq h]; simp

/-- **Predictable price drop after good news.** For `θ > 0`, `0 < ρ`,
`0 < δ` and `δρ < 1`, the price change from impact to the next period after a
positive shock is strictly below its rational counterpart, by `θ c`. -/
theorem price_change_lt {θ ρ δ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) (hδ : 0 < δ) (h1 : δ * ρ < 1) :
    priceIRF θ ρ δ 1 - priceIRF θ ρ δ 0 < priceIRF 0 ρ δ 1 - priceIRF 0 ρ δ 0 := by
  have h : |δ * ρ| < 1 := by rw [abs_of_pos (mul_pos hδ hρ)]; exact h1
  rw [priceIRF_eq h, priceIRF_eq h, priceIRF_eq h, priceIRF_eq h]
  have : 0 < δ * ρ / (1 - δ * ρ) := div_pos (mul_pos hδ hρ) (by linarith)
  simp only [ite_true, one_ne_zero, ite_false, pow_zero, pow_one, add_zero]
  nlinarith

end Diagnostic

end Econ
