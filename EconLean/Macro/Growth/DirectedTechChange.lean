/-
# Directed technical change: weak and strong equilibrium bias

Acemoglu (2002), "Directed Technical Change", REStud;
Acemoglu, *Introduction to Modern Economic Growth*, ch. 15.

**Setting (reduced form).** Skilled (`H`) and unskilled (`L`) labor are
combined with CES elasticity `σ > 0` (the derived elasticity of substitution
in Acemoglu's lab-equipment model). Write `x = H/L > 0` for relative supply
and `N = N_H/N_L > 0` for relative technology. Relative profitability of
innovating for the skilled sector combines the price effect and the market
size effect: `π_H/π_L = N^{−1/σ} x^{(σ−1)/σ}` (`relProfit`). With relative
innovation-possibilities `η = η_H/η_L > 0`, free entry in both research
sectors requires `η π_H/π_L = 1` (`IsFreeEntry`). Relative wages are
`w_H/w_L = N^{(σ−1)/σ} x^{−1/σ}` (`relWage`).

**Results.**
* `isFreeEntry_iff`: the equilibrium technology ratio is
  `N* = η^σ x^{σ−1}`.
* `relWage_eq`: in equilibrium `w_H/w_L = η^{σ−1} x^{σ−2}`.
* `weak_bias`: **weak equilibrium bias**: the induced technology change is
  always biased toward the factor that becomes more abundant, i.e. the
  relative productivity term `N*^{(σ−1)/σ}` is (weakly) increasing in `x`,
  strictly when `σ ≠ 1`.
* `strong_bias_iff`: **strong equilibrium bias**: the equilibrium relative
  wage is strictly increasing in relative supply iff `σ > 2`, so the
  long-run relative demand curve slopes up (Acemoglu's explanation of the
  rising skill premium).

**Notation.** `σ` is the *derived* elasticity `σ = ε − (ε − 1)(1 − β)`
(Acemoglu 2002), not the elasticity `ε` between the skilled- and
unskilled-intensive goods; the distribution parameter `γ^ε` is normalized
to one.

**Deviations.** The relative-profit and relative-wage expressions are taken
in their reduced form (the monopoly pricing and the derived elasticity
`σ = ε − (ε − 1)(1 − β)` are not derived here); balanced-growth dynamics are
not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

namespace Econ
namespace DirectedTech

open Real Set

variable {σ η : ℝ}

/-- Relative profitability of skill-biased vs. labor-biased innovation. -/
def relProfit (σ N x : ℝ) : ℝ := N ^ (-1 / σ) * x ^ ((σ - 1) / σ)

/-- Free entry into both research sectors. -/
def IsFreeEntry (σ η N x : ℝ) : Prop := η * relProfit σ N x = 1

/-- Relative wage given relative technology and supply. -/
def relWage (σ N x : ℝ) : ℝ := N ^ ((σ - 1) / σ) * x ^ (-1 / σ)

/-- Equilibrium relative technology. -/
def nStar (σ η x : ℝ) : ℝ := η ^ σ * x ^ (σ - 1)

theorem nStar_pos (hη : 0 < η) {x : ℝ} (hx : 0 < x) : 0 < nStar σ η x :=
  mul_pos (rpow_pos_of_pos hη _) (rpow_pos_of_pos hx _)

theorem isFreeEntry_iff (hσ : 0 < σ) (hη : 0 < η) {N x : ℝ} (hN : 0 < N) (hx : 0 < x) :
    IsFreeEntry σ η N x ↔ N = nStar σ η x := by
  unfold IsFreeEntry relProfit nStar
  have hσ' := hσ.ne'
  constructor
  · intro h
    -- `N^{1/σ} = η x^{(σ−1)/σ}`; raise to the power `σ`
    have h1 : N ^ (1 / σ) = η * x ^ ((σ - 1) / σ) := by
      have hN1 : N ^ (-1 / σ) = (N ^ (1 / σ))⁻¹ := by
        rw [neg_div, rpow_neg hN.le]
      rw [hN1] at h
      have hpos : 0 < N ^ (1 / σ) := rpow_pos_of_pos hN _
      field_simp at h
      linarith
    have h2 : (N ^ (1 / σ)) ^ σ = N := by
      rw [← rpow_mul hN.le, one_div_mul_cancel hσ', rpow_one]
    rw [← h2, h1, mul_rpow hη.le (rpow_nonneg hx.le _), ← rpow_mul hx.le,
      div_mul_cancel₀ _ hσ']
  · intro h
    subst h
    rw [mul_rpow (rpow_nonneg hη.le _) (rpow_nonneg hx.le _), ← rpow_mul hη.le,
      ← rpow_mul hx.le, mul_assoc, ← rpow_add hx]
    have e1 : σ * (-1 / σ) = -1 := by field_simp
    have e2 : (σ - 1) * (-1 / σ) + (σ - 1) / σ = 0 := by field_simp; ring
    rw [e1, e2, rpow_zero, mul_one, rpow_neg_one, mul_inv_cancel₀ hη.ne']

theorem relWage_eq (hσ : 0 < σ) (hη : 0 < η) {x : ℝ} (hx : 0 < x) :
    relWage σ (nStar σ η x) x = η ^ (σ - 1) * x ^ (σ - 2) := by
  unfold relWage nStar
  have hσ' := hσ.ne'
  rw [mul_rpow (rpow_nonneg hη.le _) (rpow_nonneg hx.le _), ← rpow_mul hη.le,
    ← rpow_mul hx.le, mul_assoc, ← rpow_add hx]
  have e1 : σ * ((σ - 1) / σ) = σ - 1 := by field_simp
  have e2 : (σ - 1) * ((σ - 1) / σ) + -1 / σ = σ - 2 := by field_simp; ring
  rw [e1, e2]

/-- The relative productivity term `N*^{(σ−1)/σ} = η^{σ−1} x^{(σ−1)²/σ}`. -/
theorem bias_eq (hσ : 0 < σ) (hη : 0 < η) {x : ℝ} (hx : 0 < x) :
    nStar σ η x ^ ((σ - 1) / σ) = η ^ (σ - 1) * x ^ ((σ - 1) ^ 2 / σ) := by
  unfold nStar
  rw [mul_rpow (rpow_nonneg hη.le _) (rpow_nonneg hx.le _), ← rpow_mul hη.le, ← rpow_mul hx.le]
  congr 2
  · field_simp
  · ring

/-- **Weak equilibrium bias.** -/
theorem weak_bias (hσ : 0 < σ) (hη : 0 < η) :
    MonotoneOn (fun x => nStar σ η x ^ ((σ - 1) / σ)) (Ioi 0) ∧
      (σ ≠ 1 → StrictMonoOn (fun x => nStar σ η x ^ ((σ - 1) / σ)) (Ioi 0)) := by
  have hc : 0 < η ^ (σ - 1) := rpow_pos_of_pos hη _
  have he : 0 ≤ (σ - 1) ^ 2 / σ := div_nonneg (sq_nonneg _) hσ.le
  refine ⟨fun x hx y hy hxy => ?_, fun h1 x hx y hy hxy => ?_⟩
  · simp only [bias_eq hσ hη hx, bias_eq hσ hη hy]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow (le_of_lt hx) hxy he) hc.le
  · simp only [bias_eq hσ hη hx, bias_eq hσ hη hy]
    have he' : 0 < (σ - 1) ^ 2 / σ := div_pos (by have := sub_ne_zero.2 h1; positivity) hσ
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow (le_of_lt hx) hxy he') hc

/-- **Strong equilibrium bias** iff `σ > 2`. -/
theorem strong_bias_iff (hσ : 0 < σ) (hη : 0 < η) :
    StrictMonoOn (fun x => relWage σ (nStar σ η x) x) (Ioi 0) ↔ 2 < σ := by
  have hc : 0 < η ^ (σ - 1) := rpow_pos_of_pos hη _
  constructor
  · intro h
    by_contra hle; push Not at hle
    have h12 := h (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
      (by norm_num)
    simp only at h12
    rw [relWage_eq hσ hη one_pos, relWage_eq hσ hη two_pos, one_rpow, mul_one] at h12
    have : (2 : ℝ) ^ (σ - 2) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    nlinarith
  · intro h x hx y hy hxy
    simp only
    rw [relWage_eq hσ hη hx, relWage_eq hσ hη hy]
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow (le_of_lt hx) hxy (by linarith)) hc

end DirectedTech
end Econ

end
