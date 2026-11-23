/-
# The two-period household with log utility

The building block of the overlapping-generations models (Acemoglu §9.2–9.3,
Ljungqvist–Sargent ch. 9).

**The economics.** A household lives two periods, consumes `c₁` when young and
`c₂` when old, and has lifetime utility `log c₁ + β log c₂` (`β > 0` is the
discount factor). Saving earns gross return `R > 0`, so with lifetime wealth
`W` (measured in first-period goods) the budget constraint is

    c₁ + c₂ / R ≤ W.

The optimum spends the fraction `1/(1+β)` of wealth when young:

    c₁* = W / (1 + β),   c₂* = β R W / (1 + β).

`logU_le_opt` proves `(c₁*, c₂*)` is optimal and `logU_lt_opt` that it is the
*unique* optimum. The saving form (`saving_isOptimal_iff`): a young agent with
endowments `(ω₁, ω₂)` who saves `a` consumes `ω₁ − a` and `ω₂ + R a`; the
optimal saving is `a* = (β ω₁ − ω₂ / R) / (1 + β)`.

**The Lean.** The proof avoids calculus: the inequality `log x ≤ x − 1`
(strict for `x ≠ 1`) applied to `c₁ / c₁*` and `c₂ / c₂*`, weighted by `1`
and `β`, sums to `(1 + β)(c₁ + c₂/R)/W − (1 + β) ≤ 0`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace OLG

open Real

/-- Lifetime utility `log c₁ + β log c₂`. -/
def logU (β c₁ c₂ : ℝ) : ℝ := log c₁ + β * log c₂

/-- Optimality of `(W/(1+β), β R W/(1+β))` among all affordable positive
bundles. -/
theorem logU_le_opt {β R W c₁ c₂ : ℝ} (hβ : 0 < β) (hR : 0 < R) (hW : 0 < W)
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (hbud : c₁ + c₂ / R ≤ W) :
    logU β c₁ c₂ ≤ logU β (W / (1 + β)) (β * R * W / (1 + β)) := by
  have hb1 : 0 < 1 + β := by linarith
  have ho1 : 0 < W / (1 + β) := div_pos hW hb1
  have ho2 : 0 < β * R * W / (1 + β) := by positivity
  have l1 := log_le_sub_one_of_pos (div_pos h₁ ho1)
  have l2 := log_le_sub_one_of_pos (div_pos h₂ ho2)
  rw [log_div h₁.ne' ho1.ne'] at l1
  rw [log_div h₂.ne' ho2.ne'] at l2
  -- `c₁/c₁* + β c₂/c₂* = (1+β)(c₁ + c₂/R)/W ≤ 1 + β`
  have key : c₁ / (W / (1 + β)) + β * (c₂ / (β * R * W / (1 + β))) ≤ 1 + β := by
    have : c₁ / (W / (1 + β)) + β * (c₂ / (β * R * W / (1 + β)))
        = (1 + β) * (c₁ + c₂ / R) / W := by
      field_simp
    rw [this, div_le_iff₀ hW]
    nlinarith
  unfold logU
  nlinarith

/-- The optimum is unique: any other affordable bundle gives strictly lower
utility. -/
theorem logU_lt_opt {β R W c₁ c₂ : ℝ} (hβ : 0 < β) (hR : 0 < R) (hW : 0 < W)
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (hbud : c₁ + c₂ / R ≤ W)
    (hne : c₁ ≠ W / (1 + β) ∨ c₂ ≠ β * R * W / (1 + β)) :
    logU β c₁ c₂ < logU β (W / (1 + β)) (β * R * W / (1 + β)) := by
  have hb1 : 0 < 1 + β := by linarith
  have ho1 : 0 < W / (1 + β) := div_pos hW hb1
  have ho2 : 0 < β * R * W / (1 + β) := by positivity
  have l1 := log_le_sub_one_of_pos (div_pos h₁ ho1)
  have l2 := log_le_sub_one_of_pos (div_pos h₂ ho2)
  have key : c₁ / (W / (1 + β)) + β * (c₂ / (β * R * W / (1 + β))) ≤ 1 + β := by
    have : c₁ / (W / (1 + β)) + β * (c₂ / (β * R * W / (1 + β)))
        = (1 + β) * (c₁ + c₂ / R) / W := by
      field_simp
    rw [this, div_le_iff₀ hW]
    nlinarith
  rw [log_div h₁.ne' ho1.ne'] at l1
  rw [log_div h₂.ne' ho2.ne'] at l2
  unfold logU
  rcases hne with h | h
  · have s1 := log_lt_sub_one_of_pos (div_pos h₁ ho1)
      (fun e => h ((div_eq_one_iff_eq ho1.ne').1 e))
    rw [log_div h₁.ne' ho1.ne'] at s1
    nlinarith
  · have s2 := log_lt_sub_one_of_pos (div_pos h₂ ho2)
      (fun e => h ((div_eq_one_iff_eq ho2.ne').1 e))
    rw [log_div h₂.ne' ho2.ne'] at s2
    nlinarith

/-! ## The saving problem -/

/-- `a` is an optimal saving choice for a young agent with endowments
`(ω₁, ω₂)` facing gross return `R`: consumption stays positive, and no other
saving level with positive consumption gives higher utility. -/
def IsOptimalSaving (β ω₁ ω₂ R a : ℝ) : Prop :=
  0 < ω₁ - a ∧ 0 < ω₂ + R * a ∧
    ∀ a', 0 < ω₁ - a' → 0 < ω₂ + R * a' → logU β (ω₁ - a') (ω₂ + R * a') ≤ logU β (ω₁ - a) (ω₂ + R * a)

/-- **Optimal saving with log utility:** `a` is optimal iff
`a = (β ω₁ − ω₂ / R) / (1 + β)`. -/
theorem saving_isOptimal_iff {β ω₁ ω₂ R a : ℝ} (hβ : 0 < β) (hR : 0 < R) (hω₁ : 0 < ω₁)
    (hω₂ : 0 ≤ ω₂) :
    IsOptimalSaving β ω₁ ω₂ R a ↔ a = (β * ω₁ - ω₂ / R) / (1 + β) := by
  have hb1 : 0 < 1 + β := by linarith
  set W := ω₁ + ω₂ / R with hWdef
  have hW : 0 < W := by positivity
  set aS := (β * ω₁ - ω₂ / R) / (1 + β)
  have hc1 : ω₁ - aS = W / (1 + β) := by
    simp only [aS, hWdef]; field_simp; ring
  have hc2 : ω₂ + R * aS = β * R * W / (1 + β) := by
    simp only [aS, hWdef]; field_simp; ring
  have hbud : ∀ a', (ω₁ - a') + (ω₂ + R * a') / R = W := by
    intro a'; simp only [hWdef]; field_simp; ring
  have hopt1 : 0 < ω₁ - aS := by rw [hc1]; positivity
  have hopt2 : 0 < ω₂ + R * aS := by rw [hc2]; positivity
  constructor
  · rintro ⟨h1, h2, hmax⟩
    by_contra hne
    have hlt := logU_lt_opt hβ hR hW h1 h2 (hbud a).le (by
      left
      rw [← hc1]
      intro e
      exact hne (by linarith))
    have := hmax aS hopt1 hopt2
    rw [hc1, hc2] at this
    linarith
  · rintro rfl
    refine ⟨hopt1, hopt2, fun a' h1 h2 => ?_⟩
    rw [hc1, hc2]
    exact logU_le_opt hβ hR hW h1 h2 (hbud a').le

end OLG
end Econ

end
