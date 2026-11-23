/-
# The New Keynesian Phillips curve from Calvo pricing

Calvo (1983), J. Monetary Econ.; Galí, *Monetary Policy, Inflation, and the
Business Cycle*, ch. 3.2 (log-linear, perfect foresight).

**Setting.** Each period a firm can reset its price with probability `1 − θ`,
`θ ∈ (0,1)`. In log-linear terms, with log price level `pₜ` and log real
marginal cost `mcₜ`:
* the price level is `p_{t+1} = θ pₜ + (1 − θ) x_{t+1}` (non-resetters keep
  their price; resetters choose `x`) (`PriceDynamics`);
* the optimal reset price is the discounted average of future nominal
  marginal costs over the expected life of the price,
  `xₜ = (1 − βθ) Σ_k (βθ)^k (p_{t+k} + mc_{t+k})` (`reset`).

**Results.**
* `reset_rec`: `xₜ = (1 − βθ)(pₜ + mcₜ) + βθ x_{t+1}` (for bounded paths).
* `nkpc`: inflation `π_{t+1} = p_{t+1} − pₜ` satisfies the New Keynesian
  Phillips curve `π_{t+1} = β π_{t+2} + κ mc_{t+1}` with
  `κ = (1 − θ)(1 − βθ)/θ`.

**Deviations.** Perfect foresight (expectations replaced by realized paths),
first-order approximation taken as the model. `mc` is log real marginal cost
net of the steady-state markup, constant returns (Galí eq. 3.19 without the
decreasing-returns factor). The hypothesis that `p + mc` is bounded rules
out trend inflation; summability would only need growth below `1/(βθ)`.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace Calvo

variable {β θ : ℝ}

/-- The optimal reset price. -/
def reset (β θ : ℝ) (p mc : ℕ → ℝ) (t : ℕ) : ℝ :=
  (1 - β * θ) * ∑' k : ℕ, (β * θ) ^ k * (p (t + k) + mc (t + k))

/-- Calvo price-level dynamics. -/
def PriceDynamics (β θ : ℝ) (p mc : ℕ → ℝ) : Prop :=
  ∀ t, p (t + 1) = θ * p t + (1 - θ) * reset β θ p mc (t + 1)

theorem summable_terms (hb0 : 0 ≤ β * θ) (hb1 : β * θ < 1) {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ t, |a t| ≤ C) : Summable fun k : ℕ => (β * θ) ^ k * a k := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hb0 hb1).mul_left C) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hb0 _)]
  calc (β * θ) ^ k * |a k| ≤ (β * θ) ^ k * C := mul_le_mul_of_nonneg_left (ha k) (pow_nonneg hb0 _)
    _ = C * (β * θ) ^ k := mul_comm _ _

/-- **Recursive form of the reset price.** -/
theorem reset_rec (hb0 : 0 ≤ β * θ) (hb1 : β * θ < 1) {p mc : ℕ → ℝ} {C : ℝ}
    (hC : ∀ t, |p t + mc t| ≤ C) (t : ℕ) :
    reset β θ p mc t = (1 - β * θ) * (p t + mc t) + β * θ * reset β θ p mc (t + 1) := by
  have hs := summable_terms hb0 hb1 (a := fun k => p (t + k) + mc (t + k)) (C := C) fun k => hC _
  rw [reset, reset, hs.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, add_zero, pow_succ]
  have : ∑' k : ℕ, (β * θ) ^ k * (β * θ) * (p (t + (k + 1)) + mc (t + (k + 1))) =
      β * θ * ∑' k : ℕ, (β * θ) ^ k * (p (t + 1 + k) + mc (t + 1 + k)) := by
    rw [← tsum_mul_left]
    congr 1; funext k
    rw [show t + (k + 1) = t + 1 + k by omega]; ring
  rw [this]; ring

/-- **The New Keynesian Phillips curve.** -/
theorem nkpc (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1) {p mc : ℕ → ℝ} {C : ℝ}
    (hC : ∀ t, |p t + mc t| ≤ C) (h : PriceDynamics β θ p mc) (t : ℕ) :
    p (t + 1) - p t = β * (p (t + 2) - p (t + 1)) +
      (1 - θ) * (1 - β * θ) / θ * mc (t + 1) := by
  have hb0 : 0 ≤ β * θ := by positivity
  have hb1 : β * θ < 1 := by nlinarith
  have hr := reset_rec hb0 hb1 hC (t + 1)
  have h1 := h t
  have h2 := h (t + 1)
  have hθ' : 1 - θ ≠ 0 := by linarith
  -- `x_s − p_s = θ/(1−θ) (p_s − p_{s−1})`
  have e1 : reset β θ p mc (t + 1) = (p (t + 1) - θ * p t) / (1 - θ) := by
    field_simp; linarith
  have e2 : reset β θ p mc (t + 1 + 1) = (p (t + 2) - θ * p (t + 1)) / (1 - θ) := by
    field_simp; linarith
  rw [e1, e2] at hr
  field_simp at hr ⊢
  linear_combination hr

end Calvo
end Econ

end
