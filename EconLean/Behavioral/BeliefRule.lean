/-
# Belief rules: a parametrized family with rational expectations as a limit

PLAN §7.1 (core abstraction 4, `BeliefRule`) and bridge B5 (rational ↔
behavioral expectations). This file fixes a small, concrete instance of that
abstraction, shared by `DiagnosticExpectations.lean` and
`CognitiveDiscounting.lean`: **linear belief rules** that distort the
rational forecast of a variable (measured as a deviation from its steady
state).

A linear belief rule with parameters `(m, θ)` maps the rational forecast made
today, `e = E_t[y]`, and the rational forecast of the same variable made
yesterday, `e' = E_{t−1}[y]`, to the subjective forecast

    Ê_t[y] = m · e + θ · (e − e').

* `rational` (`m = 1`, `θ = 0`): rational expectations.
* `cognitive m` (`θ = 0`): Gabaix's (2020) cognitive discounting, which
  shrinks forecasts toward the steady state by `m ∈ [0, 1]`.
* `diagnostic θ` (`m = 1`): diagnostic expectations (Bordalo, Gennaioli and
  Shleifer 2018), which overweight the news `e − e'`. For Gaussian AR
  processes this is exactly the mean of BGS's representativeness-distorted
  distribution.

Rational expectations is the point `(1, 0)` of the family, and forecasts are
continuous (indeed linear) in `(m, θ)` (`continuous_forecast`). Model
results can then be classified as **robust** (they hold on a neighborhood of
`(1, 0)`) or **knife-edge** (they fail arbitrarily close to it); see
`CognitiveDiscounting.lean` for one of each.
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

namespace BeliefRule

/-- A linear belief rule: forecasts `m · e + θ · (e − e')`. -/
structure Linear where
  /-- shrinkage toward the steady state (cognitive discounting) -/
  m : ℝ
  /-- weight on news (diagnosticity) -/
  θ : ℝ

namespace Linear

/-- The subjective forecast given today's (`e`) and yesterday's (`e'`)
rational forecasts of the same variable. -/
def forecast (B : Linear) (e e' : ℝ) : ℝ := B.m * e + B.θ * (e - e')

/-- Rational expectations. -/
def rational : Linear := ⟨1, 0⟩

/-- Cognitive discounting with factor `m`. -/
def cognitive (m : ℝ) : Linear := ⟨m, 0⟩

/-- Diagnostic expectations with diagnosticity `θ`. -/
def diagnostic (θ : ℝ) : Linear := ⟨1, θ⟩

@[simp] theorem forecast_rational (e e' : ℝ) : rational.forecast e e' = e := by
  simp [forecast, rational]

@[simp] theorem forecast_cognitive (m e e' : ℝ) : (cognitive m).forecast e e' = m * e := by
  simp [forecast, cognitive]

@[simp] theorem forecast_diagnostic (θ e e' : ℝ) :
    (diagnostic θ).forecast e e' = e + θ * (e - e') := by
  simp [forecast, diagnostic]

/-- Both behavioral families pass through rational expectations. -/
theorem cognitive_one : cognitive 1 = rational := rfl

theorem diagnostic_zero : diagnostic 0 = rational := rfl

/-- A rule forecasts rationally for all inputs iff it is the rational rule. -/
theorem forecast_eq_iff (B : Linear) : (∀ e e', B.forecast e e' = e) ↔ B = rational := by
  constructor
  · intro h
    have h1 := h 1 1
    have h2 := h 1 0
    simp only [forecast, sub_self, mul_zero, add_zero, mul_one, sub_zero] at h1 h2
    cases B
    simp only [rational, Linear.mk.injEq]
    exact ⟨h1, by simp_all⟩
  · rintro rfl e e'; exact forecast_rational e e'

/-- Forecasts are continuous in the parameters `(m, θ)`, so rational
expectations is a limit of behavioral rules. -/
theorem continuous_forecast (e e' : ℝ) :
    Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : Linear).forecast e e' := by
  unfold forecast
  fun_prop

end Linear

end BeliefRule

end Econ
