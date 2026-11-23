/-
# Pratt's theorem: the Arrow–Pratt clause

MWG Prop. 6.C.2, (i) ⟺ (ii) ⟺ (iii).

`RiskAversion.lean` proves (ii) ⟺ (iii): `u₂` has lower certainty
equivalents than `u₁` for every lottery iff `u₂ = ψ ∘ u₁` with `ψ`
increasing and concave. Here we add the local, calculus clause
(i): `r_A(x, u₂) ≥ r_A(x, u₁)` for every `x`.

**Proof idea.** Let `g = u₂' / u₁'`. A short computation gives
`g' = u₁' u₂' (r_A(u₁) - r_A(u₂)) / u₁'²`, so (i) ⟺ `g` is nonincreasing.
* `g` nonincreasing ⟹ `ψ` concave: by Cauchy's mean value theorem the
  slope of `ψ` between `u₁(x)` and `u₁(y)` is
  `(u₂ y - u₂ x)/(u₁ y - u₁ x) = g(ξ)` for some `ξ ∈ (x, y)`, so slopes of
  `ψ` decrease (Mathlib's `concaveOn_of_slope_anti_adjacent`).
* `ψ` concave ⟹ `g` nonincreasing: slopes of a concave function decrease,
  and `g(x)` is the limit of those slopes as the interval shrinks to `x`.

Standing assumptions (as in MWG): `u₁, u₂` twice differentiable with
`u₁' > 0` and `u₂' > 0`.
-/
module

public import EconLean.Uncertainty.RiskAversion
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Convex.Slope

@[expose] public section

namespace Econ

open Set Filter Topology

section Pratt

variable {u₁ u₂ : ℝ → ℝ}

/-- The ratio of marginal utilities `u₂'/u₁'`. -/
noncomputable def marginalRatio (u₁ u₂ : ℝ → ℝ) (x : ℝ) : ℝ := deriv u₂ x / deriv u₁ x

/-- The "relative slope" `(u₂ y - u₂ x)/(u₁ y - u₁ x)`: the slope of
`ψ = u₂ ∘ u₁⁻¹` between `u₁ x` and `u₁ y`. -/
noncomputable def relSlope (u₁ u₂ : ℝ → ℝ) (x y : ℝ) : ℝ := (u₂ y - u₂ x) / (u₁ y - u₁ x)

theorem relSlope_comm (x y : ℝ) : relSlope u₁ u₂ x y = relSlope u₁ u₂ y x := by
  unfold relSlope; rw [← neg_sub, ← neg_sub (u₁ x), neg_div_neg_eq]

variable (hd₁ : Differentiable ℝ u₁) (hd₁' : Differentiable ℝ (deriv u₁))
  (hd₂ : Differentiable ℝ u₂) (hd₂' : Differentiable ℝ (deriv u₂))
  (hp₁ : ∀ x, 0 < deriv u₁ x) (hp₂ : ∀ x, 0 < deriv u₂ x)

include hd₁' hd₂' hp₁ hp₂ in
/-- **Step 1.** Comparing Arrow–Pratt coefficients everywhere is the same
as `u₂'/u₁'` being nonincreasing. -/
theorem arrowPratt_le_iff_antitone_marginalRatio :
    (∀ x, arrowPratt u₁ x ≤ arrowPratt u₂ x) ↔ Antitone (marginalRatio u₁ u₂) := by
  have hg : ∀ x, HasDerivAt (marginalRatio u₁ u₂)
      ((deriv (deriv u₂) x * deriv u₁ x - deriv u₂ x * deriv (deriv u₁) x) / deriv u₁ x ^ 2) x :=
    fun x => ((hd₂' x).hasDerivAt.div (hd₁' x).hasDerivAt (hp₁ x).ne')
  have hgd : Differentiable ℝ (marginalRatio u₁ u₂) := fun x => (hg x).differentiableAt
  -- The pointwise equivalence `r₁ ≤ r₂ ⟺ g' ≤ 0`.
  have key : ∀ x, arrowPratt u₁ x ≤ arrowPratt u₂ x ↔ deriv (marginalRatio u₁ u₂) x ≤ 0 := by
    intro x
    rw [(hg x).deriv, div_nonpos_iff, arrowPratt, arrowPratt, neg_div, neg_div, neg_le_neg_iff,
      div_le_div_iff₀ (hp₂ x) (hp₁ x)]
    have hsq : 0 < deriv u₁ x ^ 2 := pow_pos (hp₁ x) 2
    constructor
    · intro h; right; exact ⟨by nlinarith, hsq.le⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_le.2 hsq)
      · nlinarith
  simp only [key]
  exact ⟨fun h => antitone_of_deriv_nonpos hgd h, fun h x => h.deriv_nonpos⟩

include hd₁ hd₂ hp₁ in
/-- **Cauchy MVT.** Between `x < y`, the relative slope equals `g(ξ)`. -/
theorem exists_relSlope_eq {x y : ℝ} (hxy : x < y) :
    ∃ ξ ∈ Ioo x y, relSlope u₁ u₂ x y = marginalRatio u₁ u₂ ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_ratio_hasDerivAt_eq_ratio_slope u₂ (deriv u₂) hxy
    hd₂.continuous.continuousOn (fun z _ => (hd₂ z).hasDerivAt) u₁ (deriv u₁)
    hd₁.continuous.continuousOn (fun z _ => (hd₁ z).hasDerivAt)
  have hpos : 0 < u₁ y - u₁ x := sub_pos.2 (strictMono_of_deriv_pos hp₁ hxy)
  refine ⟨ξ, hξ, ?_⟩
  unfold relSlope marginalRatio
  rw [div_eq_div_iff hpos.ne' (hp₁ ξ).ne']
  linarith

include hd₁ hd₂ hp₁ in
/-- The relative slope tends to `g(x)` as `y → x`. -/
theorem tendsto_relSlope (x : ℝ) :
    Tendsto (relSlope u₁ u₂ x) (𝓝[≠] x) (𝓝 (marginalRatio u₁ u₂ x)) := by
  have h := ((hd₂ x).hasDerivAt.tendsto_slope).div ((hd₁ x).hasDerivAt.tendsto_slope)
    (hp₁ x).ne'
  refine h.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hy' : y - x ≠ 0 := sub_ne_zero.2 hy
  show slope u₂ x y / slope u₁ x y = (u₂ y - u₂ x) / (u₁ y - u₁ x)
  rw [slope_def_field, slope_def_field, div_div_div_cancel_right₀ hy']

include hd₁ hd₁' hd₂ hd₂' hp₁ hp₂ in
/-- **Pratt's theorem, Arrow–Pratt clause** (MWG Prop. 6.C.2, (i) ⟺ (iii)).
For twice differentiable Bernoulli utilities with positive marginal
utility, `r_A(x, u₂) ≥ r_A(x, u₁)` for all `x` iff `u₂` is more risk averse
than `u₁` (lower certainty equivalent for every lottery). -/
theorem arrowPratt_le_iff_moreRiskAverse :
    (∀ x, arrowPratt u₁ x ≤ arrowPratt u₂ x) ↔ MoreRiskAverse u₂ u₁ := by
  have hm₁ : StrictMono u₁ := strictMono_of_deriv_pos hp₁
  have hm₂ : StrictMono u₂ := strictMono_of_deriv_pos hp₂
  rw [arrowPratt_le_iff_antitone_marginalRatio hd₁' hd₂' hp₁ hp₂,
    moreRiskAverse_iff hd₁.continuous hm₁ hd₂.continuous hm₂]
  have hconv : Convex ℝ (range u₁) := (isPreconnected_range hd₁.continuous).ordConnected.convex
  constructor
  · -- `g` nonincreasing ⟹ `ψ = u₂ ∘ u₁⁻¹` concave.
    intro hanti
    set ψ : ℝ → ℝ := fun t => u₂ (Function.invFun u₁ t) with hψ
    have hψu : ∀ x, ψ (u₁ x) = u₂ x := fun x => by
      simp only [hψ, Function.leftInverse_invFun hm₁.injective x]
    refine ⟨ψ, ?_, ?_, fun x => (hψu x).symm⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      rw [hψu, hψu]; exact hm₂ (hm₁.lt_iff_lt.1 hxy)
    · refine concaveOn_of_slope_anti_adjacent hconv ?_
      rintro _ t _ ⟨x, rfl⟩ ⟨z, rfl⟩ hxt htz
      obtain ⟨y, rfl⟩ : t ∈ range u₁ := hconv.ordConnected.out ⟨x, rfl⟩ ⟨z, rfl⟩ ⟨hxt.le, htz.le⟩
      have hxy := hm₁.lt_iff_lt.1 hxt
      have hyz := hm₁.lt_iff_lt.1 htz
      rw [hψu, hψu, hψu]
      obtain ⟨ξ, hξ, e1⟩ := exists_relSlope_eq hd₁ hd₂ hp₁ hxy
      obtain ⟨η, hη, e2⟩ := exists_relSlope_eq hd₁ hd₂ hp₁ hyz
      change relSlope u₁ u₂ y z ≤ relSlope u₁ u₂ x y
      rw [e1, e2]
      exact hanti (hξ.2.trans hη.1).le
  · -- `ψ` concave ⟹ `g` nonincreasing.
    rintro ⟨ψ, -, hψc, hψ⟩ x z hxz
    rcases hxz.eq_or_lt with rfl | hxz
    · exact le_rfl
    -- Relative slopes are slopes of `ψ`, which decrease for concave `ψ`.
    have hrel : ∀ a b, a < b → relSlope u₁ u₂ a b = (ψ (u₁ b) - ψ (u₁ a)) / (u₁ b - u₁ a) :=
      fun a b _ => by rw [relSlope, hψ a, hψ b]
    have hchain : ∀ a b c, a < b → b < c →
        relSlope u₁ u₂ b c ≤ relSlope u₁ u₂ a c ∧ relSlope u₁ u₂ a c ≤ relSlope u₁ u₂ a b := by
      intro a b c hab hbc
      have h := hψc.slope_anti_adjacent (mem_range_self a) (mem_range_self c)
        (hm₁ hab) (hm₁ hbc)
      rw [← hrel b c hbc, ← hrel a b hab] at h
      have d1 : 0 < u₁ b - u₁ a := sub_pos.2 (hm₁ hab)
      have d2 : 0 < u₁ c - u₁ b := sub_pos.2 (hm₁ hbc)
      have hac : relSlope u₁ u₂ a c =
          ((u₂ b - u₂ a) + (u₂ c - u₂ b)) / ((u₁ b - u₁ a) + (u₁ c - u₁ b)) := by
        rw [relSlope]; congr 1 <;> ring
      unfold relSlope at h ⊢
      rw [show u₂ c - u₂ a = (u₂ b - u₂ a) + (u₂ c - u₂ b) by ring,
        show u₁ c - u₁ a = (u₁ b - u₁ a) + (u₁ c - u₁ b) by ring]
      rw [div_le_div_iff₀ d2 d1] at h
      constructor
      · rw [div_le_div_iff₀ d2 (by linarith)]; nlinarith
      · rw [div_le_div_iff₀ (by linarith) d1]; nlinarith
    -- `g(x) ≥ relSlope x z ≥ g(z)` by passing to the limit.
    have h1 : relSlope u₁ u₂ x z ≤ marginalRatio u₁ u₂ x := by
      refine ge_of_tendsto ((tendsto_relSlope hd₁ hd₂ hp₁ x).mono_left
        (nhdsWithin_mono _ fun y (hy : y ∈ Ioi x) => (ne_of_gt hy : y ≠ x))) ?_
      filter_upwards [Ioo_mem_nhdsGT hxz] with y hy
      exact (hchain x y z hy.1 hy.2).2
    have h2 : marginalRatio u₁ u₂ z ≤ relSlope u₁ u₂ x z := by
      refine le_of_tendsto ((tendsto_relSlope hd₁ hd₂ hp₁ z).mono_left
        (nhdsWithin_mono _ fun y (hy : y ∈ Iio z) => (ne_of_lt hy : y ≠ z))) ?_
      filter_upwards [Ioo_mem_nhdsLT hxz] with y hy
      rw [relSlope_comm]
      exact (hchain x y z hy.1 hy.2).1
    exact h2.trans h1

end Pratt

/-! ### Non-vacuity -/

/-- **Witness: CARA utilities are ranked by their coefficient.** For
`0 < a₁ ≤ a₂`, `u_a(x) = -e^{-a x}` satisfies all hypotheses of Pratt's
theorem, so `u_{a₂}` is more risk averse than `u_{a₁}`. -/
example (a₁ a₂ : ℝ) (h₁ : 0 < a₁) (h₁₂ : a₁ ≤ a₂) :
    MoreRiskAverse (fun x => -Real.exp (-a₂ * x)) (fun x => -Real.exp (-a₁ * x)) := by
  have cara : ∀ a : ℝ, 0 < a →
      (∀ x, HasDerivAt (fun x => -Real.exp (-a * x)) (a * Real.exp (-a * x)) x) ∧
      (∀ x, HasDerivAt (fun x => a * Real.exp (-a * x)) (-(a * a) * Real.exp (-a * x)) x) := by
    intro a _
    have hl : ∀ x : ℝ, HasDerivAt (fun y => -a * y) (-a) x := fun x => by
      simpa using (hasDerivAt_id x).const_mul (-a)
    exact ⟨fun x => by convert (hl x).exp.neg using 1; ring,
      fun x => by convert ((hl x).exp).const_mul a using 1; ring⟩
  have hdd : ∀ a : ℝ, 0 < a → deriv (fun x => -Real.exp (-a * x)) = fun x => a * Real.exp (-a * x) :=
    fun a ha => funext fun x => ((cara a ha).1 x).deriv
  have hAP : ∀ a : ℝ, 0 < a → ∀ x, arrowPratt (fun x => -Real.exp (-a * x)) x = a := by
    intro a ha x
    rw [arrowPratt, hdd a ha, ((cara a ha).2 x).deriv]
    have := Real.exp_pos (-a * x)
    field_simp
  have h₂ : 0 < a₂ := h₁.trans_le h₁₂
  refine (arrowPratt_le_iff_moreRiskAverse
    (fun x => ((cara a₁ h₁).1 x).differentiableAt)
    (by rw [hdd a₁ h₁]; exact fun x => ((cara a₁ h₁).2 x).differentiableAt)
    (fun x => ((cara a₂ h₂).1 x).differentiableAt)
    (by rw [hdd a₂ h₂]; exact fun x => ((cara a₂ h₂).2 x).differentiableAt)
    (fun x => by rw [hdd a₁ h₁]; exact mul_pos h₁ (Real.exp_pos _))
    (fun x => by rw [hdd a₂ h₂]; exact mul_pos h₂ (Real.exp_pos _))).1 fun x => ?_
  rw [hAP a₁ h₁, hAP a₂ h₂]
  exact h₁₂

end Econ
