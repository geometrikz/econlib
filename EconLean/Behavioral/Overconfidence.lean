/-
# Overconfidence as overprecision

References. A. Moore and P. Healy (2008), "The Trouble with Overconfidence",
*Psych. Review* 115(2) (overprecision); K. Daniel, D. Hirshleifer and
A. Subrahmanyam (1998), *J. Finance* 53(6), and T. Odean (1998), *J. Finance*
53(6) (overconfident investors overweight private signals).

**Setting (Gaussian updating).** A state `ω ~ N(μ, 1/τ₀)` and a signal
`s = ω + η`, `η ~ N(0, 1/τ_s)` independent. An estimate `w s + (1 − w) μ`
has error `ω − estimate = (1 − w)(ω − μ) − w η`, so its mean squared error is

    mse(w) = (1 − w)²/τ₀ + w²/τ_s.

(We take this formula, which follows from independence, as the definition.)
The Bayesian weight is `w* = τ_s/(τ₀ + τ_s)`. An **overconfident** agent
believes the signal precision is `k τ_s` with `k > 1` and so uses
`w(k τ_s)`.

**Results.**
* `mse_sub_mse_bayes`: `mse(w) − mse(w*) = (w − w*)²(τ₀ + τ_s)/(τ₀ τ_s)`, so
  `w*` is the unique minimizer (`mse_bayes_lt`), with
  `mse(w*) = 1/(τ₀ + τ_s)` (`mse_bayes`).
* `weight_overconfident_gt`: overconfident agents overweight the signal.
* `mse_overconfident_gt`: overconfidence strictly raises the actual error.
* `overprecision`: the overconfident agent's perceived posterior variance
  `1/(τ₀ + k τ_s)` strictly understates the actual mean squared error of its
  own estimate.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace Econ

namespace Overconfidence

/-- Mean squared error of the estimate `w s + (1 − w) μ`. -/
def mse (τ₀ τs w : ℝ) : ℝ := (1 - w) ^ 2 / τ₀ + w ^ 2 / τs

/-- The weight on a signal believed to have precision `τs`. -/
def weight (τ₀ τs : ℝ) : ℝ := τs / (τ₀ + τs)

theorem mse_sub_mse_bayes {τ₀ τs : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (w : ℝ) :
    mse τ₀ τs w - mse τ₀ τs (weight τ₀ τs) = (w - weight τ₀ τs) ^ 2 * (τ₀ + τs) / (τ₀ * τs) := by
  have : τ₀ + τs ≠ 0 := by positivity
  unfold mse weight
  field_simp
  ring

/-- The Bayesian error: `mse(w*) = 1/(τ₀ + τ_s)`. -/
theorem mse_bayes {τ₀ τs : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) :
    mse τ₀ τs (weight τ₀ τs) = 1 / (τ₀ + τs) := by
  have : τ₀ + τs ≠ 0 := by positivity
  unfold mse weight
  field_simp
  ring

/-- The Bayesian weight is the unique minimizer of the mean squared error. -/
theorem mse_bayes_lt {τ₀ τs : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) {w : ℝ} (hw : w ≠ weight τ₀ τs) :
    mse τ₀ τs (weight τ₀ τs) < mse τ₀ τs w := by
  have h := mse_sub_mse_bayes h₀ hs w
  have : 0 < (w - weight τ₀ τs) ^ 2 * (τ₀ + τs) / (τ₀ * τs) := by
    have : w - weight τ₀ τs ≠ 0 := sub_ne_zero.2 hw
    positivity
  linarith

/-- **Overconfident agents overweight private signals.** -/
theorem weight_overconfident_gt {τ₀ τs k : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (hk : 1 < k) :
    weight τ₀ τs < weight τ₀ (k * τs) := by
  unfold weight
  rw [div_lt_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_pos h₀ hs]

/-- **Overconfidence is costly**: it strictly raises the actual error. -/
theorem mse_overconfident_gt {τ₀ τs k : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (hk : 1 < k) :
    mse τ₀ τs (weight τ₀ τs) < mse τ₀ τs (weight τ₀ (k * τs)) :=
  mse_bayes_lt h₀ hs (weight_overconfident_gt h₀ hs hk).ne'

/-- **Overprecision.** The overconfident agent believes its posterior variance
is `1/(τ₀ + k τ_s)`, but the actual mean squared error of its estimate is
strictly larger. -/
theorem overprecision {τ₀ τs k : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (hk : 1 < k) :
    1 / (τ₀ + k * τs) < mse τ₀ τs (weight τ₀ (k * τs)) := by
  have h1 := mse_overconfident_gt h₀ hs hk
  rw [mse_bayes h₀ hs] at h1
  have : 1 / (τ₀ + k * τs) < 1 / (τ₀ + τs) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  linarith

/-- Non-vacuity: with `τ₀ = τ_s = 1` and `k = 3`, the Bayesian weight is `1/2`,
the overconfident weight is `3/4`, and the errors are `1/2 < 5/8`. -/
example : weight 1 1 = 1 / 2 ∧ weight 1 (3 * 1) = 3 / 4 ∧ mse 1 1 (1 / 2) = 1 / 2 ∧
    mse 1 1 (3 / 4) = 5 / 8 := by
  norm_num [weight, mse]

end Overconfidence

end Econ
