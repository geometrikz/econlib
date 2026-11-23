/-
# Diagnostic expectations and credit cycles (Bordalo–Gennaioli–Shleifer 2018)

Reference. P. Bordalo, N. Gennaioli and A. Shleifer (2018), "Diagnostic
Expectations and Credit Cycles", *J. Finance* 73(1), §§II–III; the
spread-reversal evidence of D. López-Salido, J. Stein and E. Zakrajšek (2017),
"Credit-Market Sentiment and the Business Cycle", *QJE* 132(3).

**Model (log-linear).** Productivity follows the AR(1) of
`DiagnosticExpectations.lean`, `a_{t+1} = ρ a_t + ε_{t+1}`. Lenders and firms
form diagnostic forecasts `Ê_t a_{t+1} = ρ a_t + θρ ε_t`
(`Diagnostic.fcT_diagnostic`). Two macro-financial variables load on this
forecast:
* the **credit spread** `S_t = −χ Ê_t a_{t+1}` (`χ > 0`: expected default falls
  when expected productivity rises);
* **investment** `k_{t+1} = Ê_t a_{t+1}/(1 − α)` (expected marginal product
  of capital equals the cost of funds, Cobb–Douglas share `α < 1`).

**Results.**
* `spreadIRF_eq`, `investIRF_eq`: the responses at date `t + k` to good news
  `ε_t = 1` are `−χ(1 + θ·[k = 0])ρ^{k+1}` and `(1 + θ·[k = 0])ρ^{k+1}/(1 − α)`.
* `spread_too_low`, `invest_boom`: on impact spreads fall and investment
  rises by more than under rational expectations (`θ = 0`).
* `spread_reversal`, `invest_bust`: in the next period the spread rises,
  and investment falls, by `χθρ` and `θρ/(1 − α)` more than under rational
  expectations: a predictable credit cycle.
* `condExp_spreadNext`, `spread_sentiment`, `expected_spread_change_eq`,
  `cov_expected_change`: the expected future spread `E_t S_{t+1} = −χρ²a_t`
  does not depend on `θ` (derived), today's spread contains a
  sentiment component `S_t − S_t^{RE} = −χθρ ε_t`, and the rationally
  expected change `E_t S_{t+1} − S_t` exceeds its rational-expectations value
  by exactly `χθρ ε_t`: the sentiment fully reverts next period, so low
  spreads predict rising spreads (López-Salido–Stein–Zakrajšek).
-/
module

public import EconLean.Behavioral.DiagnosticExpectations
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

namespace Econ

namespace CreditCycles

open BeliefRule Diagnostic

/-- Response of the spread at date `t + k` to a unit shock `ε_t`. -/
def spreadIRF (χ θ ρ : ℝ) (k : ℕ) : ℝ := -χ * forecastIRF (Linear.diagnostic θ) ρ k 1

/-- Response of investment `k_{t+k+1}` to a unit shock `ε_t`. -/
def investIRF (α θ ρ : ℝ) (k : ℕ) : ℝ := forecastIRF (Linear.diagnostic θ) ρ k 1 / (1 - α)

theorem forecastIRF_diagnostic (θ ρ : ℝ) (k : ℕ) :
    forecastIRF (Linear.diagnostic θ) ρ k 1 = (if k = 0 then 1 + θ else 1) * ρ ^ (k + 1) := by
  simp only [forecastIRF, Linear.forecast_diagnostic]
  split_ifs <;> ring

theorem spreadIRF_eq (χ θ ρ : ℝ) (k : ℕ) :
    spreadIRF χ θ ρ k = -χ * ((if k = 0 then 1 + θ else 1) * ρ ^ (k + 1)) := by
  rw [spreadIRF, forecastIRF_diagnostic]

theorem investIRF_eq (α θ ρ : ℝ) (k : ℕ) :
    investIRF α θ ρ k = (if k = 0 then 1 + θ else 1) * ρ ^ (k + 1) / (1 - α) := by
  rw [investIRF, forecastIRF_diagnostic]

/-- **Spreads are too low after good news.** -/
theorem spread_too_low {χ θ ρ : ℝ} (hχ : 0 < χ) (hθ : 0 < θ) (hρ : 0 < ρ) :
    spreadIRF χ θ ρ 0 < spreadIRF χ 0 ρ 0 := by
  simp only [spreadIRF_eq, ite_true, add_zero, zero_add, pow_one]
  have := mul_pos (mul_pos hχ hθ) hρ
  nlinarith

/-- **Investment booms after good news.** -/
theorem invest_boom {α θ ρ : ℝ} (hα : α < 1) (hθ : 0 < θ) (hρ : 0 < ρ) :
    investIRF α 0 ρ 0 < investIRF α θ ρ 0 := by
  simp only [investIRF_eq, ite_true, add_zero, zero_add, pow_one]
  apply div_lt_div_of_pos_right _ (by linarith)
  nlinarith

/-- **Spread reversal.** From impact to the next period the spread rises by
exactly `χθρ` more than under rational expectations. -/
theorem spread_reversal (χ θ ρ : ℝ) :
    (spreadIRF χ θ ρ 1 - spreadIRF χ θ ρ 0) - (spreadIRF χ 0 ρ 1 - spreadIRF χ 0 ρ 0) =
      χ * θ * ρ := by
  simp only [spreadIRF_eq]; norm_num; ring

/-- **Relative investment reversal.** From impact to the next period
investment falls by exactly `θρ/(1 − α)` more than under rational
expectations. (The level stays above steady state; the reversal is relative to
the rational path.) -/
theorem invest_bust {α : ℝ} (hα : α < 1) (θ ρ : ℝ) :
    (investIRF α θ ρ 1 - investIRF α θ ρ 0) - (investIRF α 0 ρ 1 - investIRF α 0 ρ 0) =
      -(θ * ρ / (1 - α)) := by
  have : 1 - α ≠ 0 := by linarith
  simp only [investIRF_eq]; norm_num; field_simp; ring

/-- After good news, investment growth is strictly below its rational
counterpart. -/
theorem invest_bust_lt {α θ ρ : ℝ} (hα : α < 1) (hθ : 0 < θ) (hρ : 0 < ρ) :
    investIRF α θ ρ 1 - investIRF α θ ρ 0 < investIRF α 0 ρ 1 - investIRF α 0 ρ 0 := by
  have h := invest_bust hα θ ρ
  have : 0 < θ * ρ / (1 - α) := div_pos (mul_pos hθ hρ) (by linarith)
  linarith

/-- After good news, the spread rises strictly more than rational
expectations predict. -/
theorem spread_reversal_pos {χ θ ρ : ℝ} (hχ : 0 < χ) (hθ : 0 < θ) (hρ : 0 < ρ) :
    spreadIRF χ 0 ρ 1 - spreadIRF χ 0 ρ 0 < spreadIRF χ θ ρ 1 - spreadIRF χ θ ρ 0 := by
  have h := spread_reversal χ θ ρ
  have : 0 < χ * θ * ρ := by positivity
  linarith

/-! ### Predictable spread changes in the state-space representation -/

/-- The spread `S_t = −χ Ê_t a_{t+1}`, as a variable on
`(a_{t−2}, ε_{t−1}, ε_t, ε_{t+1})`. -/
def spread (χ θ ρ : ℝ) : Var := (-χ) • fcT (Linear.diagnostic θ) ρ

/-- Next period's diagnostic forecast `Ê_{t+1} a_{t+2}`: the diagnostic rule
applied to the rational forecasts `E_{t+1} a_{t+2} = ρ a_{t+1}` and
`E_t a_{t+2} = ρ² a_t`. -/
def fcNext (θ ρ : ℝ) : Var := fun k => (Linear.diagnostic θ).forecast (ρ * x1 ρ k) (ρ ^ 2 * x0 ρ k)

/-- Next period's spread `S_{t+1} = −χ Ê_{t+1} a_{t+2}`. -/
def spreadNext (χ θ ρ : ℝ) : Var := (-χ) • fcNext θ ρ

/-- Conditional expectation given date-`t` information: the shocks are
independent with mean zero, so it drops the loading on `ε_{t+1}`. -/
def condExp (y : Var) : Var := ![y 0, y 1, y 2, 0]

theorem fcNext_eq (θ ρ : ℝ) : fcNext θ ρ = ![ρ ^ 4, ρ ^ 3, ρ ^ 2, (1 + θ) * ρ] := by
  funext k; fin_cases k <;> simp [fcNext, x1, x0, Linear.forecast, Linear.diagnostic] <;> ring

/-- **The expected future spread does not depend on diagnosticity**:
`E_t S_{t+1} = −χρ² a_t` (coefficients `−χρ²·(ρ², ρ, 1, 0)`), because next period's distortion `θρε_{t+1}` is
unpredictable today. -/
theorem condExp_spreadNext (χ θ ρ : ℝ) :
    condExp (spreadNext χ θ ρ) = ![-χ * ρ ^ 4, -χ * ρ ^ 3, -χ * ρ ^ 2, 0] := by
  funext k; fin_cases k <;> simp [condExp, spreadNext, fcNext_eq]

/-- The sentiment component of the spread is `−χθρ ε_t`. -/
theorem spread_sentiment (χ θ ρ : ℝ) :
    spread χ θ ρ - spread χ 0 ρ = (-χ * θ * ρ) • εt := by
  simp only [spread, fcT_diagnostic]
  funext k; simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

/-- **Low spreads predict rising spreads.** The rationally expected change in
the spread, `E_t S_{t+1} − S_t`, exceeds its rational-expectations value by
`χθρ ε_t`. -/
theorem expected_spread_change_eq (χ θ ρ : ℝ) :
    (condExp (spreadNext χ θ ρ) - spread χ θ ρ) - (condExp (spreadNext χ 0 ρ) - spread χ 0 ρ) =
      (χ * θ * ρ) • εt := by
  rw [condExp_spreadNext, condExp_spreadNext,
    show ∀ a b c : Var, (a - b) - (a - c) = -(b - c) from fun a b c => by abel,
    spread_sentiment]
  funext k; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- In covariance form: the excess expected spread change covaries positively
with today's news (`θ, ρ, χ, s² > 0`) and negatively with today's spread
sentiment. -/
theorem cov_expected_change {χ θ ρ v s2 : ℝ} (hχ : 0 < χ) (hθ : 0 < θ) (hρ : 0 < ρ)
    (hs : 0 < s2) :
    0 < cov v s2 ((condExp (spreadNext χ θ ρ) - spread χ θ ρ) -
      (condExp (spreadNext χ 0 ρ) - spread χ 0 ρ)) εt ∧
    cov v s2 ((condExp (spreadNext χ θ ρ) - spread χ θ ρ) -
      (condExp (spreadNext χ 0 ρ) - spread χ 0 ρ)) (spread χ θ ρ - spread χ 0 ρ) < 0 := by
  rw [expected_spread_change_eq, spread_sentiment]
  simp only [cov, εt, Pi.smul_apply, smul_eq_mul]
  simp
  constructor <;> nlinarith [mul_pos (mul_pos (mul_pos hχ hθ) hρ) hs,
    mul_pos (mul_pos (mul_pos (mul_pos hχ hθ) hρ) (mul_pos (mul_pos hχ hθ) hρ)) hs]

end CreditCycles

end Econ
