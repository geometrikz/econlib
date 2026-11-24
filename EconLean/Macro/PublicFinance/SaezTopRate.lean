/-
# The optimal top income tax rate (Saez)

Saez (2001), "Using Elasticities to Derive Optimal Income Tax Rates",
REStud; Diamond and Saez (2011), JEP; Piketty–Saez (2013), Handbook of
Public Economics, §3.

**Setting.** Above a threshold `z* > 0` incomes are Pareto distributed with
tail parameter `a > 1` (density `a z*^a z^{−a−1}`), so the mean income above
the threshold is `z̄ = a z*/(a − 1)` (`mean_pareto`). A linear top rate `τ`
applies to income above `z*`. Raising it by `dτ` has (per top taxpayer)
* a **mechanical** revenue gain `(z̄ − z*) dτ`,
* a **behavioral** revenue loss `e z̄ τ/(1 − τ) dτ`, where `e > 0` is the
  elasticity of top incomes with respect to the net-of-tax rate `1 − τ`,
* a **welfare** loss `ḡ (z̄ − z*) dτ` for the top taxpayers, with social
  marginal welfare weight `ḡ ∈ [0, 1)` (relative to public funds).
The net effect is `dSW(τ) = (1 − ḡ)(z̄ − z*) − e z̄ τ/(1 − τ)` (`dSW`).

**Results.**
* `mean_pareto`: `∫_{z*}^∞ z · a z*^a z^{−a−1} dz = a z*/(a − 1)`.
* `dSW_eq_zero_iff`: the first-order condition holds iff
  `τ = τ* = (1 − ḡ)/(1 − ḡ + a e)` (the Saez formula).
* `dSW_pos_iff`: on `[0, 1)`, raising the rate improves welfare iff
  `τ < τ*`, so `τ*` is the unique optimum of the single-peaked problem;
  `revenue_max`: with `ḡ = 0` the revenue-maximizing rate is `1/(1 + a e)`.
* `topRate_mem`: `0 < τ* < 1`; it falls with the elasticity `e` and with the
  tail parameter `a` (thinner tails), and with the welfare weight `ḡ`
  (`topRate_anti_e`, `topRate_anti_a`).

* `welfare_hasDerivAt`, `welfare_hasDerivAt_dSW`: `dSW` is the derivative of
  top-bracket welfare `τ (Z − z*) + ḡ V` when `Z` has elasticity `e` and
  `V' = −(Z − z*)` (envelope theorem), evaluated where `Z = z̄`.
* `hasDerivAt_welfare`, `topRate_isMaxOn`: with `a` and `e` constant,
  welfare `W` has `W' = dSW` and `τ*` maximizes `W` on `[0, 1)`.
* `zbar_eq_integral`: `z̄` is the Pareto tail mean.

**Deviations.** Treating `a` and `e` as constant in `τ` is Saez's local
approximation; the envelope step `V' = −(Z − z*)` is a hypothesis. No income
effects; `e > 0` (with `e = 0` the optimum is `τ = 1`).
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section

namespace Econ
namespace Saez

open Real MeasureTheory Set

/-- **Mean of a Pareto tail.** -/
theorem mean_pareto {a zs : ℝ} (ha : 1 < a) (hz : 0 < zs) :
    ∫ z in Ioi zs, z * (a * zs ^ a * z ^ (-a - 1)) = a * zs / (a - 1) := by
  have h1 : -a < -1 := by linarith
  have hcongr : EqOn (fun z => z * (a * zs ^ a * z ^ (-a - 1))) (fun z => a * zs ^ a * z ^ (-a))
      (Ioi zs) := by
    intro z hz'
    have hz0 : 0 < z := hz.trans hz'
    simp only
    rw [show -a = 1 + (-a - 1) by ring, rpow_add hz0, rpow_one]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_Ioi_rpow_of_lt h1 hz, show -a + 1 = 1 - a by ring, rpow_sub hz, rpow_one]
  have : 0 < zs ^ a := rpow_pos_of_pos hz _
  have : a - 1 ≠ 0 := by linarith
  have : 1 - a ≠ 0 := by linarith
  field_simp
  ring

/-- Parameters of the top-tax problem. -/
structure Params where
  a : ℝ
  e : ℝ
  zs : ℝ
  g : ℝ
  ha : 1 < a
  he : 0 < e
  hzs : 0 < zs
  hg : 0 ≤ g ∧ g < 1

namespace Params

variable (P : Params)

/-- Mean top income. -/
def zbar : ℝ := P.a * P.zs / (P.a - 1)

/-- `z̄` is the mean of the Pareto tail. -/
theorem zbar_eq_integral :
    P.zbar = ∫ z in Ioi P.zs, z * (P.a * P.zs ^ P.a * z ^ (-P.a - 1)) :=
  (mean_pareto P.ha P.hzs).symm

/-- Net welfare effect of raising the top rate, per unit `dτ`. -/
def dSW (τ : ℝ) : ℝ := (1 - P.g) * (P.zbar - P.zs) - P.e * P.zbar * τ / (1 - τ)

/-- The Saez top rate. -/
def topRate : ℝ := (1 - P.g) / (1 - P.g + P.a * P.e)

theorem zbar_sub : P.zbar - P.zs = P.zbar / P.a := by
  have : P.a - 1 ≠ 0 := by linarith [P.ha]
  have : P.a ≠ 0 := by linarith [P.ha]
  simp only [zbar]; field_simp; ring

theorem zbar_pos : 0 < P.zbar := by
  have := P.hzs; have : 0 < P.a - 1 := by linarith [P.ha]
  exact div_pos (mul_pos (by linarith [P.ha]) P.hzs) this

theorem den_pos : 0 < 1 - P.g + P.a * P.e := by
  have := mul_pos (show 0 < P.a by linarith [P.ha]) P.he; linarith [P.hg.2]

theorem topRate_mem : 0 < P.topRate ∧ P.topRate < 1 := by
  have h1 : 0 < 1 - P.g := by linarith [P.hg.2]
  have := mul_pos (show 0 < P.a by linarith [P.ha]) P.he
  exact ⟨div_pos h1 P.den_pos, (div_lt_one P.den_pos).2 (by linarith)⟩

/-- `dSW(τ) (1 − τ) a / z̄ = (1 − ḡ) − τ (1 − ḡ + a e)`. -/
theorem dSW_scaled {τ : ℝ} (hτ : τ < 1) :
    P.dSW τ * ((1 - τ) * P.a / P.zbar) = (1 - P.g) - τ * (1 - P.g + P.a * P.e) := by
  have h1 : 1 - τ ≠ 0 := by linarith
  have hz := P.zbar_pos.ne'
  have ha : P.a ≠ 0 := by linarith [P.ha]
  rw [dSW, P.zbar_sub]
  field_simp
  ring

theorem scale_pos {τ : ℝ} (hτ : τ < 1) : 0 < (1 - τ) * P.a / P.zbar :=
  div_pos (mul_pos (by linarith) (by linarith [P.ha])) P.zbar_pos

/-- **The Saez formula.** -/
theorem dSW_eq_zero_iff {τ : ℝ} (hτ : τ < 1) : P.dSW τ = 0 ↔ τ = P.topRate := by
  have hs := P.scale_pos hτ
  rw [topRate, eq_div_iff P.den_pos.ne']
  constructor
  · intro h
    have := P.dSW_scaled hτ
    rw [h, zero_mul] at this
    linarith
  · intro h
    have := P.dSW_scaled hτ
    have h0 : P.dSW τ * ((1 - τ) * P.a / P.zbar) = 0 := by rw [this]; linarith
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact h'
    · linarith

/-- **Raising the rate helps iff `τ < τ*`.** -/
theorem dSW_pos_iff {τ : ℝ} (hτ : τ < 1) : 0 < P.dSW τ ↔ τ < P.topRate := by
  have hs := P.scale_pos hτ
  have key := P.dSW_scaled hτ
  rw [topRate, lt_div_iff₀ P.den_pos]
  constructor
  · intro h
    have := mul_pos h hs
    linarith
  · intro h
    have h1 : 0 < P.dSW τ * ((1 - τ) * P.a / P.zbar) := by rw [key]; linarith
    exact pos_of_mul_pos_left h1 hs.le

/-- **Revenue-maximizing rate** (`ḡ = 0`). -/
theorem revenue_max (h : P.g = 0) : P.topRate = 1 / (1 + P.a * P.e) := by
  simp [topRate, h]

/-- The top rate falls with the elasticity. -/
theorem topRate_anti_e (P' : Params) (ha : P'.a = P.a) (hg : P'.g = P.g) (he : P.e < P'.e) :
    P'.topRate < P.topRate := by
  simp only [topRate, ha, hg]
  have h1 : 0 < 1 - P.g := by linarith [P.hg.2]
  apply div_lt_div_of_pos_left h1 P.den_pos
  have : 0 < P.a := by linarith [P.ha]
  nlinarith

/-- The top rate falls with the Pareto parameter (thinner tails). -/
theorem topRate_anti_a (P' : Params) (he : P'.e = P.e) (hg : P'.g = P.g) (ha : P.a < P'.a) :
    P'.topRate < P.topRate := by
  simp only [topRate, he, hg]
  have h1 : 0 < 1 - P.g := by linarith [P.hg.2]
  apply div_lt_div_of_pos_left h1 P.den_pos
  nlinarith [P.he]

/-! ### Deriving `dSW` from a welfare objective -/

omit P in
/-- **Envelope decomposition.** Let `Z(τ)` be mean top income with
elasticity `e` with respect to `1 − τ` (`Z' = −e Z/(1 − τ)`), and `V(τ)` the
top taxpayers' indirect utility in money units (envelope theorem:
`V' = −(Z − z*)`). Social welfare from the top bracket, revenue
`τ (Z − z*)` plus `ḡ V`, has derivative
`(1 − ḡ)(Z − z*) − e Z τ/(1 − τ)`. -/
theorem welfare_hasDerivAt {Z V : ℝ → ℝ} {τ e g zs : ℝ}
    (hZ : HasDerivAt Z (-(e * Z τ / (1 - τ))) τ) (hV : HasDerivAt V (-(Z τ - zs)) τ) :
    HasDerivAt (fun t => t * (Z t - zs) + g * V t)
      ((1 - g) * (Z τ - zs) - e * Z τ * τ / (1 - τ)) τ := by
  have := ((hasDerivAt_id' τ).mul (hZ.sub_const zs)).add (hV.const_mul g)
  convert this using 1
  ring

/-- At a point where mean top income equals the Pareto mean `z̄`, the
welfare derivative is exactly `dSW`. -/
theorem welfare_hasDerivAt_dSW {Z V : ℝ → ℝ} {τ : ℝ} (hZτ : Z τ = P.zbar)
    (hZ : HasDerivAt Z (-(P.e * Z τ / (1 - τ))) τ) (hV : HasDerivAt V (-(Z τ - P.zs)) τ) :
    HasDerivAt (fun t => t * (Z t - P.zs) + P.g * V t) (P.dSW τ) τ := by
  have := welfare_hasDerivAt (g := P.g) hZ hV
  rw [hZτ] at this
  exact this

/-- Social welfare as a function of the top rate when the Pareto parameter
and the elasticity are constant (Saez's local approximation):
`W(τ) = (1 − ḡ)(z̄ − z*) τ + e z̄ (τ + log(1 − τ))`, so that `W' = dSW`. -/
def welfare (τ : ℝ) : ℝ := (1 - P.g) * (P.zbar - P.zs) * τ + P.e * P.zbar * (τ + log (1 - τ))

theorem hasDerivAt_welfare {τ : ℝ} (hτ : τ < 1) : HasDerivAt P.welfare (P.dSW τ) τ := by
  have hl : HasDerivAt (fun t => log (1 - t)) ((-1) / (1 - τ)) τ := by
    have := ((hasDerivAt_id τ).const_sub 1).log (by simp; linarith)
    simpa using this
  have := ((hasDerivAt_id τ).const_mul ((1 - P.g) * (P.zbar - P.zs))).add
    (((hasDerivAt_id τ).add hl).const_mul (P.e * P.zbar))
  convert this using 1
  · rfl
  · have : 1 - τ ≠ 0 := by linarith
    simp only [dSW]
    field_simp
    ring

/-- **The Saez rate is the welfare optimum.** `τ*` maximizes `W` over
`[0, 1)`. -/
theorem topRate_isMaxOn : IsMaxOn P.welfare (Ico 0 1) P.topRate := by
  obtain ⟨h0, h1⟩ := P.topRate_mem
  have hcont : ContinuousOn P.welfare (Ico 0 1) := fun τ hτ =>
    (P.hasDerivAt_welfare hτ.2).continuousAt.continuousWithinAt
  have hmono : MonotoneOn P.welfare (Icc 0 P.topRate) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (hcont.mono fun x hx => ⟨hx.1, hx.2.trans_lt h1⟩)
    · intro x hx
      rw [interior_Icc] at hx
      exact (P.hasDerivAt_welfare (hx.2.trans h1)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(P.hasDerivAt_welfare (hx.2.trans h1)).deriv]
      exact ((P.dSW_pos_iff (hx.2.trans h1)).2 hx.2).le
  have hanti : AntitoneOn P.welfare (Ico P.topRate 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico _ _)
      (hcont.mono fun x hx => ⟨h0.le.trans hx.1, hx.2⟩)
    · intro x hx
      rw [interior_Ico] at hx
      exact (P.hasDerivAt_welfare hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(P.hasDerivAt_welfare hx.2).deriv]
      exact not_lt.1 fun h => absurd ((P.dSW_pos_iff hx.2).1 h) (not_lt.2 hx.1.le)
  intro τ hτ
  rcases le_total τ P.topRate with h | h
  · exact hmono ⟨hτ.1, h⟩ ⟨h0.le, le_rfl⟩ h
  · exact hanti ⟨le_rfl, h1⟩ ⟨h, hτ.2⟩ h

end Params
end Saez
end Econ

end
