/-
# Optimal income taxation with two types (Stiglitz–Mirrlees)

Mirrlees (1971), "An Exploration in the Theory of Optimum Income Taxation",
REStud; Stiglitz (1982), "Self-Selection and Pareto Efficient Taxation",
JPubE; Salanié, *The Economics of Taxation*, ch. 4.

**Setting.** Two skill types `θ_L < θ_H` with population shares
`π_L, π_H > 0` (`π_L + π_H = 1`). A type-`θ` worker who earns pre-tax income
`y` and consumes `c` gets quasilinear utility `c − v(y/θ)`, with `v` the
disutility of effort. A utilitarian-with-weights planner puts welfare weights
`g_L > g_H` on the two types (normalized: `π_L g_L + π_H g_H = 1`, so the
planner values redistribution toward the low type). It chooses an allocation
`(c_L, y_L, c_H, y_H)` subject to
* the **resource constraint** `π_L c_L + π_H c_H = π_L y_L + π_H y_H`,
* the high type's **incentive constraint**
  `c_H − v(y_H/θ_H) ≥ c_L − v(y_L/θ_H)` (the high type must not mimic).
By the taxation principle any such allocation is implemented by a nonlinear
income tax `T(y_i) = y_i − c_i`, and the implicit **marginal tax rate** at
`y` for type `θ` is the wedge `τ(θ, y) = 1 − v'(y/θ)/θ`.

**Results.**
* `welfare_eq`: on the resource constraint, weighted welfare equals
  `S(y_L, y_H) − κ (U_H − U_L)` with `S` total surplus and
  `κ = π_L π_H (g_L − g_H) > 0`.
* `welfare_le`, `welfare_eq_W`, `exists_alloc`: every feasible incentive
  compatible allocation has welfare at most
  `W(y_L, y_H) = S − κ Φ(y_L)` with information rent
  `Φ(y) = v(y/θ_L) − v(y/θ_H)`, with equality exactly when the high type's
  incentive constraint binds; and every `(y_L, y_H)` with
  `Φ(y_L) ≤ Φ(y_H)` is attained by an allocation that also satisfies the low
  type's incentive constraint. So the optimal tax problem reduces to
  maximizing `W`.
* `no_distortion_top`: at an optimum, `v'(y_H/θ_H)/θ_H = 1`: the high type
  faces a **zero marginal tax rate**.
* `bottom_foc`, `bottom_tax_pos`: at an optimum,
  `π_L τ(θ_L, y_L) = κ Φ'(y_L)`, and if `v'` is nonnegative and strictly
  increasing the low type faces a **strictly positive marginal tax rate**
  (its effort is distorted downward to cut the high type's information rent).

* `IsOptimum`, `optimum_welfare_eq`, `optimum_isLocalMax_top`,
  `optimum_isLocalMax_bottom`: at a solution of the **full** program the
  high type's constraint binds and, without bunching
  (`Φ(y_L) < Φ(y_H)`), `(y_L, y_H)` is a local maximum of `W` in each
  argument; `optimum_no_distortion_top` and `optimum_bottom_tax_pos` state
  the two results for solutions of the full program, with `v` differentiable
  on `(0, ∞)` (and strictly convex for the bottom).

**Deviations.** Two types and quasilinear utility (no income effects);
first-order conditions at interior, non-bunching optima.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

noncomputable section

namespace Econ
namespace Mirrlees2

/-- Primitives of the two-type economy. -/
structure Params where
  πL : ℝ
  πH : ℝ
  θL : ℝ
  θH : ℝ
  gL : ℝ
  gH : ℝ
  hπL : 0 < πL
  hπH : 0 < πH
  hπ : πL + πH = 1
  hθL : 0 < θL
  hθ : θL < θH
  hg : πL * gL + πH * gH = 1
  hgLH : gH < gL
  hgH : 0 ≤ gH

namespace Params

variable (P : Params) (v : ℝ → ℝ)

/-- Utility of type `θ` from `(c, y)`. -/
def U (θ c y : ℝ) : ℝ := c - v (y / θ)

/-- Total surplus `Σ π_i (y_i − v(y_i/θ_i))`. -/
def S (yL yH : ℝ) : ℝ := P.πL * (yL - v (yL / P.θL)) + P.πH * (yH - v (yH / P.θH))

/-- The high type's information rent from mimicking at `y`. -/
def Φ (y : ℝ) : ℝ := v (y / P.θL) - v (y / P.θH)

/-- Weight of the information rent in the planner's objective. -/
def κ : ℝ := P.πL * P.πH * (P.gL - P.gH)

/-- Reduced objective. -/
def W (yL yH : ℝ) : ℝ := P.S v yL yH - P.κ * P.Φ v yL

/-- Weighted welfare of an allocation. -/
def welfare (cL yL cH yH : ℝ) : ℝ :=
  P.gL * P.πL * U v P.θL cL yL + P.gH * P.πH * U v P.θH cH yH

/-- The resource constraint. -/
def Feasible (cL yL cH yH : ℝ) : Prop := P.πL * cL + P.πH * cH = P.πL * yL + P.πH * yH

/-- The high type's incentive constraint. -/
def ICH (cL yL cH yH : ℝ) : Prop := U v P.θH cL yL ≤ U v P.θH cH yH

/-- The low type's incentive constraint. -/
def ICL (cL yL cH yH : ℝ) : Prop := U v P.θL cH yH ≤ U v P.θL cL yL

theorem κ_pos : 0 < P.κ := mul_pos (mul_pos P.hπL P.hπH) (by linarith [P.hgLH])

/-- **Welfare decomposition** on the resource constraint. -/
theorem welfare_eq {cL yL cH yH : ℝ} (hF : P.Feasible cL yL cH yH) :
    P.welfare v cL yL cH yH =
      P.S v yL yH - P.κ * (U v P.θH cH yH - U v P.θL cL yL) := by
  have hπ := P.hπ; have hg := P.hg
  simp only [welfare, S, κ, U, Feasible] at *
  linear_combination hF + ((cL - v (yL / P.θL)) * P.πL + (cH - v (yH / P.θH)) * P.πH) * hg -
    ((cL - v (yL / P.θL)) * P.πL * P.gL + (cH - v (yH / P.θH)) * P.πH * P.gH) * hπ

/-- **Upper bound.** Every feasible allocation satisfying the high type's
incentive constraint has welfare at most `W(y_L, y_H)`. -/
theorem welfare_le {cL yL cH yH : ℝ} (hF : P.Feasible cL yL cH yH)
    (hIC : P.ICH v cL yL cH yH) : P.welfare v cL yL cH yH ≤ P.W v yL yH := by
  rw [P.welfare_eq v hF, W]
  have : P.Φ v yL ≤ U v P.θH cH yH - U v P.θL cL yL := by
    simp only [ICH, U, Φ] at hIC ⊢; linarith
  nlinarith [P.κ_pos]

/-- The bound is attained exactly when the high type's incentive constraint
binds. -/
theorem welfare_eq_W_iff {cL yL cH yH : ℝ} (hF : P.Feasible cL yL cH yH) :
    P.welfare v cL yL cH yH = P.W v yL yH ↔ U v P.θH cH yH = U v P.θH cL yL := by
  rw [P.welfare_eq v hF, W]
  have hk := P.κ_pos
  constructor
  · intro h
    have : P.κ * (U v P.θH cH yH - U v P.θL cL yL - P.Φ v yL) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · simp only [U, Φ] at h0 ⊢; linarith
  · intro h
    simp only [U, Φ] at h ⊢
    have : cH - v (yH / P.θH) - (cL - v (yL / P.θL)) = v (yL / P.θL) - v (yL / P.θH) := by
      linarith
    rw [this]

/-- **Attainment.** For any incomes with `Φ(y_L) ≤ Φ(y_H)` there is a
feasible allocation in which the high type's incentive constraint binds and
the low type's holds; it attains `W(y_L, y_H)`. -/
theorem exists_alloc (yL yH : ℝ) (hΦ : P.Φ v yL ≤ P.Φ v yH) :
    ∃ cL cH, P.Feasible cL yL cH yH ∧ P.ICH v cL yL cH yH ∧ P.ICL v cL yL cH yH ∧
      P.welfare v cL yL cH yH = P.W v yL yH := by
  -- `c_H = c_L + v(y_H/θ_H) − v(y_L/θ_H)` (binding), `c_L` from the budget
  set d := v (yH / P.θH) - v (yL / P.θH)
  refine ⟨P.πL * yL + P.πH * yH - P.πH * d, P.πL * yL + P.πH * yH - P.πH * d + d, ?_, ?_, ?_, ?_⟩
  · simp only [Feasible]; have := P.hπ; linear_combination (P.πL * yL + P.πH * yH - P.πH * d) * this
  · simp only [ICH, U, d]; linarith
  · simp only [ICL, U, d]; simp only [Φ] at hΦ; linarith
  · have hF : P.Feasible (P.πL * yL + P.πH * yH - P.πH * d) yL
        (P.πL * yL + P.πH * yH - P.πH * d + d) yH := by
      simp only [Feasible]; have := P.hπ; linear_combination (P.πL * yL + P.πH * yH - P.πH * d) * this
    exact (P.welfare_eq_W_iff v hF).2 (by simp only [U, d]; ring)

/-! ### First-order conditions -/

/-- The implicit marginal tax rate (labour wedge) of type `θ` at income `y`. -/
def wedge (v' : ℝ → ℝ) (θ y : ℝ) : ℝ := 1 - v' (y / θ) / θ

omit P in
theorem hasDerivAt_comp_div {v v' : ℝ → ℝ} {θ y : ℝ}
    (hv : HasDerivAt v (v' (y / θ)) (y / θ)) :
    HasDerivAt (fun x => v (x / θ)) (v' (y / θ) / θ) y := by
  have := hv.comp y ((hasDerivAt_id y).div_const θ)
  simpa [Function.comp_def, div_eq_mul_inv] using this

/-- **No distortion at the top.** -/
theorem no_distortion_top {v' : ℝ → ℝ} {yL yH : ℝ}
    (hv : HasDerivAt v (v' (yH / P.θH)) (yH / P.θH))
    (hmax : IsLocalMax (fun y => P.W v yL y) yH) : wedge v' P.θH yH = 0 := by
  have hD : HasDerivAt (fun y => P.W v yL y) (P.πH * (1 - v' (yH / P.θH) / P.θH)) yH := by
    have := (((hasDerivAt_id yH).sub (hasDerivAt_comp_div hv)).const_mul P.πH).const_add
      (P.πL * (yL - v (yL / P.θL)))
    have := this.sub_const (P.κ * P.Φ v yL)
    simpa [W, S] using this
  have h0 := hmax.hasDerivAt_eq_zero hD
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h P.hπH.ne'
  · simpa [wedge] using h

/-- **The bottom first-order condition**:
`π_L τ(θ_L, y_L) = κ Φ'(y_L)`. -/
theorem bottom_foc {v' : ℝ → ℝ} {yL yH : ℝ}
    (hvL : HasDerivAt v (v' (yL / P.θL)) (yL / P.θL))
    (hvH : HasDerivAt v (v' (yL / P.θH)) (yL / P.θH))
    (hmax : IsLocalMax (fun y => P.W v y yH) yL) :
    P.πL * wedge v' P.θL yL = P.κ * (v' (yL / P.θL) / P.θL - v' (yL / P.θH) / P.θH) := by
  have dL := hasDerivAt_comp_div hvL
  have dH := hasDerivAt_comp_div hvH
  have hD : HasDerivAt (fun y => P.W v y yH)
      (P.πL * (1 - v' (yL / P.θL) / P.θL) -
        P.κ * (v' (yL / P.θL) / P.θL - v' (yL / P.θH) / P.θH)) yL := by
    have := ((((hasDerivAt_id yL).sub dL).const_mul P.πL).add_const
      (P.πH * (yH - v (yH / P.θH)))).sub ((dL.sub dH).const_mul P.κ)
    convert this using 1
    funext y; simp [W, S, Φ]
  have h0 := hmax.hasDerivAt_eq_zero hD
  simp only [wedge]
  linarith

/-- **A positive marginal tax at the bottom.** If `v'` is nonnegative and
strictly increasing on `(0, ∞)` and `y_L > 0`, the low type's marginal tax
rate is strictly positive at an optimum. -/
theorem bottom_tax_pos {v' : ℝ → ℝ} {yL yH : ℝ} (hyL : 0 < yL)
    (hmono : StrictMonoOn v' (Set.Ioi 0)) (hnn : ∀ x, 0 < x → 0 ≤ v' x)
    (hvL : HasDerivAt v (v' (yL / P.θL)) (yL / P.θL))
    (hvH : HasDerivAt v (v' (yL / P.θH)) (yL / P.θH))
    (hmax : IsLocalMax (fun y => P.W v y yH) yL) : 0 < wedge v' P.θL yL := by
  have hfoc := P.bottom_foc v hvL hvH hmax
  have hθL := P.hθL
  have hθH : 0 < P.θH := by linarith [P.hθ]
  have hxH : 0 < yL / P.θH := div_pos hyL hθH
  have hlt : yL / P.θH < yL / P.θL := div_lt_div_of_pos_left hyL hθL P.hθ
  have h1 : v' (yL / P.θH) < v' (yL / P.θL) := hmono hxH (hxH.trans hlt) hlt
  have h2 := hnn _ hxH
  have hΦ' : 0 < v' (yL / P.θL) / P.θL - v' (yL / P.θH) / P.θH := by
    have : v' (yL / P.θH) / P.θH ≤ v' (yL / P.θH) / P.θL :=
      div_le_div_of_nonneg_left h2 hθL P.hθ.le
    have : v' (yL / P.θH) / P.θL < v' (yL / P.θL) / P.θL := div_lt_div_of_pos_right h1 hθL
    linarith
  have := mul_pos P.κ_pos hΦ'
  rw [← hfoc] at this
  exact pos_of_mul_pos_right this P.hπL.le

/-! ### From the full program to the reduced problem -/

/-- A solution of the full optimal tax program. -/
def IsOptimum (cL yL cH yH : ℝ) : Prop :=
  P.Feasible cL yL cH yH ∧ P.ICH v cL yL cH yH ∧ P.ICL v cL yL cH yH ∧
    ∀ cL' yL' cH' yH', P.Feasible cL' yL' cH' yH' → P.ICH v cL' yL' cH' yH' →
      P.ICL v cL' yL' cH' yH' → P.welfare v cL' yL' cH' yH' ≤ P.welfare v cL yL cH yH

/-- The two incentive constraints together imply `Φ(y_L) ≤ Φ(y_H)`. -/
theorem Φ_le_of_IC {cL yL cH yH : ℝ} (hH : P.ICH v cL yL cH yH) (hL : P.ICL v cL yL cH yH) :
    P.Φ v yL ≤ P.Φ v yH := by
  simp only [ICH, ICL, U, Φ] at *; linarith

/-- Every `(y_L', y_H')` with `Φ(y_L') ≤ Φ(y_H')` gives `W` at most the
optimal welfare. -/
theorem W_le_of_optimum {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH) {yL' yH' : ℝ}
    (h : P.Φ v yL' ≤ P.Φ v yH') : P.W v yL' yH' ≤ P.welfare v cL yL cH yH := by
  obtain ⟨cL', cH', hF, hH, hL, hW⟩ := P.exists_alloc v yL' yH' h
  rw [← hW]; exact hopt.2.2.2 _ _ _ _ hF hH hL

/-- At an optimum, welfare equals `W(y_L, y_H)` (the high type's incentive
constraint binds). -/
theorem optimum_welfare_eq {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH) :
    P.welfare v cL yL cH yH = P.W v yL yH :=
  le_antisymm (P.welfare_le v hopt.1 hopt.2.1)
    (P.W_le_of_optimum v hopt (P.Φ_le_of_IC v hopt.2.1 hopt.2.2.1))

/-- At an optimum without bunching (`Φ(y_L) < Φ(y_H)`), `y_H` locally
maximizes `W(y_L, ·)`. -/
theorem optimum_isLocalMax_top {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH)
    (hs : P.Φ v yL < P.Φ v yH) (hc : ContinuousAt (P.Φ v) yH) :
    IsLocalMax (fun y => P.W v yL y) yH := by
  filter_upwards [hc.eventually (Ioi_mem_nhds hs)] with y hy
  rw [← P.optimum_welfare_eq v hopt]
  exact P.W_le_of_optimum v hopt (le_of_lt hy)

/-- At an optimum without bunching, `y_L` locally maximizes `W(·, y_H)`. -/
theorem optimum_isLocalMax_bottom {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH)
    (hs : P.Φ v yL < P.Φ v yH) (hc : ContinuousAt (P.Φ v) yL) :
    IsLocalMax (fun y => P.W v y yH) yL := by
  filter_upwards [hc.eventually (Iio_mem_nhds hs)] with y hy
  rw [← P.optimum_welfare_eq v hopt]
  exact P.W_le_of_optimum v hopt (le_of_lt hy)

theorem continuousAt_Φ {v' : ℝ → ℝ} (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {y : ℝ}
    (hy : 0 < y) : ContinuousAt (P.Φ v) y := by
  have hθH : 0 < P.θH := by linarith [P.hθL, P.hθ]
  exact (hasDerivAt_comp_div (hv _ (div_pos hy P.hθL))).continuousAt.sub
    (hasDerivAt_comp_div (hv _ (div_pos hy hθH))).continuousAt

/-- **No distortion at the top**, for a solution of the full program with
positive incomes and no bunching, `v` differentiable on `(0, ∞)`. -/
theorem optimum_no_distortion_top {v' : ℝ → ℝ} (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH) (hyH : 0 < yH)
    (hs : P.Φ v yL < P.Φ v yH) : wedge v' P.θH yH = 0 := by
  have hθH : 0 < P.θH := by linarith [P.hθL, P.hθ]
  exact P.no_distortion_top v (hv _ (div_pos hyH hθH))
    (P.optimum_isLocalMax_top v hopt hs (P.continuousAt_Φ v hv hyH))

/-- **A positive marginal tax at the bottom**, for a solution of the full
program with positive incomes and no bunching, when `v` is differentiable on
`(0, ∞)` with nonnegative, strictly increasing derivative (strictly convex
disutility). -/
theorem optimum_bottom_tax_pos {v' : ℝ → ℝ} (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hmono : StrictMonoOn v' (Set.Ioi 0)) (hnn : ∀ x, 0 < x → 0 ≤ v' x)
    {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH) (hyL : 0 < yL)
    (hs : P.Φ v yL < P.Φ v yH) : 0 < wedge v' P.θL yL := by
  have hθH : 0 < P.θH := by linarith [P.hθL, P.hθ]
  exact P.bottom_tax_pos v hyL hmono hnn (hv _ (div_pos hyL P.hθL)) (hv _ (div_pos hyL hθH))
    (P.optimum_isLocalMax_bottom v hopt hs (P.continuousAt_Φ v hv hyL))

end Params
end Mirrlees2
end Econ

end
