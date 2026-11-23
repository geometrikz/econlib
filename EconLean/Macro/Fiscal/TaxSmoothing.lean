/-
# Tax smoothing

Barro (1979), "On the Determination of the Public Debt", JPE; Ljungqvist–
Sargent ch. 16 (deterministic case).

**Setting.** Over `T ≥ 1` periods the government must raise present-value
revenue `B` (the present value of spending minus initial assets). Distortion
costs are quadratic, `Σ_t βᵗ τ_t²`, and the interest rate satisfies
`βR = 1`, so the budget constraint is `Σ_t βᵗ τ_t = B` (`Feasible`).

**Results.**
* `smooth_optimal`: the constant tax `τ̄ = B / Σ_t βᵗ` minimizes the
  distortion cost among all feasible tax paths.
* `smooth_unique`: it is the unique minimizer.
* Consequently the optimal tax rate does not depend on the timing of
  spending (only on its present value `B`): temporary spending is financed by
  debt, not by temporary taxes.

**Deviations.** Deterministic spending, quadratic deadweight losses in the
tax rate, `βR = 1`; the stochastic martingale result is not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace TaxSmoothing

open Finset

variable {β : ℝ} {T : ℕ}

/-- Discounted distortion cost. -/
def cost (β : ℝ) (T : ℕ) (τ : ℕ → ℝ) : ℝ := ∑ t ∈ range T, β ^ t * τ t ^ 2

/-- The budget constraint (with `βR = 1`). -/
def Feasible (β : ℝ) (T : ℕ) (B : ℝ) (τ : ℕ → ℝ) : Prop := ∑ t ∈ range T, β ^ t * τ t = B

/-- Annuity factor `Σ_{t<T} βᵗ`. -/
def ann (β : ℝ) (T : ℕ) : ℝ := ∑ t ∈ range T, β ^ t

theorem ann_pos (hβ : 0 < β) (hT : 0 < T) : 0 < ann β T :=
  sum_pos (fun t _ => pow_pos hβ t) (nonempty_range_iff.2 hT.ne')

/-- The smooth tax. -/
def smooth (β : ℝ) (T : ℕ) (B : ℝ) : ℕ → ℝ := fun _ => B / ann β T

theorem smooth_feasible (hβ : 0 < β) (hT : 0 < T) (B : ℝ) :
    Feasible β T B (smooth β T B) := by
  have h := (ann_pos hβ hT).ne'
  simp only [Feasible, smooth, ← sum_mul]
  rw [← ann]; field_simp

/-- Cost of a feasible path = cost of the smooth path + cost of the deviation. -/
theorem cost_decomp (hβ : 0 < β) (hT : 0 < T) {B : ℝ} {τ : ℕ → ℝ} (hτ : Feasible β T B τ) :
    cost β T τ = cost β T (smooth β T B) + cost β T fun t => τ t - B / ann β T := by
  have h := (ann_pos hβ hT).ne'
  have hcross : ∑ t ∈ range T, β ^ t * (τ t - B / ann β T) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [hτ, ← ann]; field_simp; ring
  simp only [cost, smooth]
  have : ∀ t, β ^ t * τ t ^ 2 = β ^ t * (B / ann β T) ^ 2 + β ^ t * (τ t - B / ann β T) ^ 2 +
      2 * (B / ann β T) * (β ^ t * (τ t - B / ann β T)) := fun t => by ring
  simp only [this, sum_add_distrib, ← mul_sum, hcross, mul_zero, add_zero]

/-- **Tax smoothing is optimal.** -/
theorem smooth_optimal (hβ : 0 < β) (hT : 0 < T) {B : ℝ} {τ : ℕ → ℝ}
    (hτ : Feasible β T B τ) : cost β T (smooth β T B) ≤ cost β T τ := by
  rw [cost_decomp hβ hT hτ]
  have : 0 ≤ cost β T fun t => τ t - B / ann β T :=
    sum_nonneg fun t _ => mul_nonneg (pow_pos hβ t).le (sq_nonneg _)
  linarith

/-- **Uniqueness**: any other feasible path is strictly costlier. -/
theorem smooth_unique (hβ : 0 < β) (hT : 0 < T) {B : ℝ} {τ : ℕ → ℝ}
    (hτ : Feasible β T B τ) (hc : cost β T τ ≤ cost β T (smooth β T B)) :
    ∀ t < T, τ t = B / ann β T := by
  rw [cost_decomp hβ hT hτ] at hc
  have h0 : cost β T (fun t => τ t - B / ann β T) = 0 :=
    le_antisymm (by linarith) (sum_nonneg fun t _ => mul_nonneg (pow_pos hβ t).le (sq_nonneg _))
  intro t ht
  have := (sum_eq_zero_iff_of_nonneg fun t _ => mul_nonneg (pow_pos hβ t).le (sq_nonneg _)).1 h0 t
    (mem_range.2 ht)
  have := (mul_eq_zero.1 this).resolve_left (pow_pos hβ t).ne'
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

end TaxSmoothing
end Econ

end
