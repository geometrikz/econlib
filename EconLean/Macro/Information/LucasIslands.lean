/-
# The Lucas islands model: signal extraction and the Phillips curve

Lucas (1972), "Expectations and the Neutrality of Money", JET; Lucas (1973),
"Some International Evidence on Output–Inflation Tradeoffs", AER;
Romer, *Advanced Macroeconomics*, §6.9.

**Setting.** A producer on island `z` sees only her local price
`p_z = p + z`, the sum of the aggregate price level `p` (mean `p̄`, variance
`V_p > 0`) and an independent island-specific relative shock `z` (mean `0`,
variance `V_z > 0`). She supplies `y_z = b ẑ` with `b > 0`, where `ẑ` is
her estimate of her relative price `z = p_z − p`. With linear estimates
`ẑ = θ (p_z − p̄)`, the mean squared error is
`E[(z − θ(p − p̄ + z))²] = θ² V_p + (1 − θ)² V_z` (`mse`).

**Results.**
* `mse_theta_lt`: the error is uniquely minimized at the signal-to-noise
  weight `θ* = V_z/(V_p + V_z)` (the linear projection), with
  `mse θ − mse θ* = (V_p + V_z)(θ − θ*)²`.
* `theta_mem`: `0 < θ* < 1`: producers attribute part of any price change
  to aggregate inflation.
* `aggregate_supply`: averaging over islands (`E z = 0`), aggregate output
  is the Lucas supply curve `Y = b θ* (p − p̄)`.
* Closing the model with aggregate demand `y = m − p` (`IsEqPrice`):
  `isEqPrice_iff`, `output_eq` give `p = p̄ + (m − p̄)/(1 + bθ*)` and
  `y = bθ*/(1 + bθ*)(m − p̄)`; `rational_expectations`: expected prices equal
  `p̄` iff `p̄ = E m`; `output_zero_iff`: output is zero iff `m = E m`, so
  only unanticipated money has real effects.
* `slope_anti`: the output–inflation slope `b θ*` is strictly decreasing in
  aggregate price variance `V_p` (Lucas 1973: output responds less to price
  surprises where inflation is more volatile), so exploiting the trade-off
  systematically erodes it (the Lucas critique).

**Deviations.** Estimates are restricted to linear rules; the best linear
predictor coincides with `E[z | p_z]` under independent Gaussian shocks
(not formalized). Moments are taken as given rather than derived from a
probability space, and `V_p` is a primitive rather than derived from the
variance of money (in equilibrium `V_p = V_m/(1 + bθ*)²`).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace LucasIslands

/-- Parameters: aggregate and relative price variances, supply slope, expected price. -/
structure Params where
  Vp : ℝ
  Vz : ℝ
  b : ℝ
  pbar : ℝ
  hVp : 0 < Vp
  hVz : 0 < Vz
  hb : 0 < b

namespace Params

variable (P : Params)

/-- Mean squared error of the linear estimate `ẑ = θ (p_z − p̄)`. -/
def mse (θ : ℝ) : ℝ := θ ^ 2 * P.Vp + (1 - θ) ^ 2 * P.Vz

/-- The signal-extraction weight. -/
def theta : ℝ := P.Vz / (P.Vp + P.Vz)

theorem mse_sub (θ : ℝ) : P.mse θ - P.mse P.theta = (P.Vp + P.Vz) * (θ - P.theta) ^ 2 := by
  have h : P.Vp + P.Vz ≠ 0 := by linarith [P.hVp, P.hVz]
  simp only [mse, theta]; field_simp; ring

/-- **Optimal signal extraction**: `θ*` uniquely minimizes the error. -/
theorem mse_theta_lt {θ : ℝ} (hθ : θ ≠ P.theta) : P.mse P.theta < P.mse θ := by
  have h1 := P.mse_sub θ
  have h2 : 0 < (θ - P.theta) ^ 2 := by
    have := sub_ne_zero.2 hθ; positivity
  have h3 : 0 < (P.Vp + P.Vz) * (θ - P.theta) ^ 2 := mul_pos (by linarith [P.hVp, P.hVz]) h2
  linarith

theorem theta_mem : 0 < P.theta ∧ P.theta < 1 := by
  have h : 0 < P.Vp + P.Vz := by linarith [P.hVp, P.hVz]
  exact ⟨div_pos P.hVz h, (div_lt_one h).2 (by linarith [P.hVp])⟩

/-- Island supply `b ẑ = b θ* (p_z − p̄)` at aggregate price `p` and island shock `z`. -/
def supply (p z : ℝ) : ℝ := P.b * (P.theta * (p + z - P.pbar))

/-- **The Lucas supply curve.** For islands `i ∈ s` with weights `w ≥ 0`
summing to one and relative shocks averaging to zero, aggregate output is
`b θ* (p − p̄)`. -/
theorem aggregate_supply {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (hw : ∑ i ∈ s, w i = 1)
    (hz : ∑ i ∈ s, w i * z i = 0) (p : ℝ) :
    ∑ i ∈ s, w i * P.supply p (z i) = P.b * P.theta * (p - P.pbar) := by
  have : ∑ i ∈ s, w i * P.supply p (z i) =
      P.b * P.theta * ((∑ i ∈ s, w i) * (p - P.pbar) + ∑ i ∈ s, w i * z i) := by
    simp only [supply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hw, hz]; ring

/-- Aggregate demand `y = m − p` closes the model: an equilibrium price level
equates Lucas supply `b θ* (p − p̄)` with demand. -/
def IsEqPrice (m p : ℝ) : Prop := P.b * P.theta * (p - P.pbar) = m - p

theorem one_add_pos : 0 < 1 + P.b * P.theta := by
  have := mul_pos P.hb P.theta_mem.1; linarith

/-- **Equilibrium price**: `p = p̄ + (m − p̄)/(1 + bθ*)`. -/
theorem isEqPrice_iff (m p : ℝ) :
    P.IsEqPrice m p ↔ p = P.pbar + (m - P.pbar) / (1 + P.b * P.theta) := by
  have h := P.one_add_pos.ne'
  unfold IsEqPrice
  rw [← sub_eq_iff_eq_add', eq_div_iff h]
  constructor <;> intro h' <;> linarith

/-- **Equilibrium output**: `y = bθ*/(1 + bθ*) · (m − p̄)`. -/
theorem output_eq {m p : ℝ} (h : P.IsEqPrice m p) :
    m - p = P.b * P.theta / (1 + P.b * P.theta) * (m - P.pbar) := by
  rw [(P.isEqPrice_iff m p).1 h]
  have := P.one_add_pos.ne'
  field_simp; ring

/-- **Rational expectations.** Over money-supply states `m_i` with weights
`w ≥ 0` summing to one, the expected equilibrium price equals `p̄` iff
`p̄ = E m`. -/
theorem rational_expectations {ι : Type*} (s : Finset ι) (w m p : ι → ℝ) (hw : ∑ i ∈ s, w i = 1)
    (hp : ∀ i ∈ s, P.IsEqPrice (m i) (p i)) :
    ∑ i ∈ s, w i * p i = P.pbar ↔ P.pbar = ∑ i ∈ s, w i * m i := by
  have h := P.one_add_pos
  have hsum : ∑ i ∈ s, w i * p i =
      P.pbar + ((∑ i ∈ s, w i * m i) - P.pbar) / (1 + P.b * P.theta) := by
    have hc := h.ne'
    rw [Finset.sum_congr rfl fun i hi => by rw [(P.isEqPrice_iff _ _).1 (hp i hi)]]
    rw [Finset.sum_congr rfl fun i _ => (show w i * (P.pbar + (m i - P.pbar) / (1 + P.b * P.theta))
      = w i * P.pbar * (1 - (1 + P.b * P.theta)⁻¹) + w i * m i * (1 + P.b * P.theta)⁻¹ by
        field_simp; ring)]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hw]
    field_simp; ring
  rw [hsum]
  constructor
  · intro h'
    have : ((∑ i ∈ s, w i * m i) - P.pbar) / (1 + P.b * P.theta) = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h1 | h1
    · linarith
    · linarith
  · intro h'; rw [← h']; simp

/-- **Only money surprises are real.** Under rational expectations (`p̄ = E m`),
equilibrium output is zero iff the money supply equals its expected value:
anticipated money is neutral, unanticipated money is not. -/
theorem output_zero_iff {m p : ℝ} (h : P.IsEqPrice m p) : m - p = 0 ↔ m = P.pbar := by
  rw [P.output_eq h]
  have h1 : 0 < P.b * P.theta / (1 + P.b * P.theta) :=
    div_pos (mul_pos P.hb P.theta_mem.1) P.one_add_pos
  constructor
  · intro h'
    rcases mul_eq_zero.1 h' with h2 | h2
    · linarith
    · linarith
  · intro h'; rw [h']; ring

/-- **More volatile inflation flattens the output response.** If aggregate
price variance rises from `V_p` to `V_p' > V_p` (all else equal), the slope
`b θ*` strictly falls. -/
theorem slope_anti (P' : Params) (hz : P'.Vz = P.Vz) (hb : P'.b = P.b) (hp : P.Vp < P'.Vp) :
    P'.b * P'.theta < P.b * P.theta := by
  rw [hb]
  apply mul_lt_mul_of_pos_left _ P.hb
  simp only [theta, hz]
  apply div_lt_div_of_pos_left P.hVz (by linarith [P.hVp, P.hVz]) (by linarith)

end Params
end LucasIslands
end Econ

end
