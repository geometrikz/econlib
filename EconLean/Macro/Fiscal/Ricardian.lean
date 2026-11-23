/-
# Ricardian equivalence

Barro (1974), "Are Government Bonds Net Wealth?", JPE; Ljungqvist–Sargent
ch. 10.

**Setting.** A household lives `T` periods, has income `y_t`, pays lump-sum
taxes `τ_t`, and can borrow and lend at the gross interest rate `R > 0`. Its
budget set is `Σ_t R^{-t} c_t ≤ Σ_t R^{-t} (y_t − τ_t)` (`budget`). The
government finances spending `g` with taxes and debt, so its intertemporal
budget constraint is `Σ_t R^{-t} τ_t = Σ_t R^{-t} g_t` (`GovBudget`).

**Results.**
* `budget_eq`: two tax paths that both satisfy the government's budget
  constraint give the household the same budget set.
* `ricardian`: hence any consumption plan optimal under one tax path is
  optimal under the other (debt-financed tax cuts do not change consumption).
* `not_ricardian_of_constraint`: with a no-borrowing constraint the result
  fails: in a two-period example (`R = 1`), a debt-financed tax cut today
  raises the constrained household's attainable utility, so its optimal
  consumption changes.

**Deviations.** Finite horizon (or dynastic altruism collapsed into one
household), lump-sum taxes, deterministic income, and a common interest rate
for household and government.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace Ricardian

open Finset

/-- Present value at gross interest rate `R` over `T` periods. -/
def pv (R : ℝ) (T : ℕ) (x : ℕ → ℝ) : ℝ := ∑ t ∈ range T, x t / R ^ t

/-- The household's intertemporal budget set. -/
def budget (R : ℝ) (T : ℕ) (y τ : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {c | pv R T c ≤ pv R T fun t => y t - τ t}

/-- The government's intertemporal budget constraint. -/
def GovBudget (R : ℝ) (T : ℕ) (g τ : ℕ → ℝ) : Prop := pv R T τ = pv R T g

theorem pv_sub (R : ℝ) (T : ℕ) (x z : ℕ → ℝ) :
    pv R T (fun t => x t - z t) = pv R T x - pv R T z := by
  simp only [pv, sub_div, sum_sub_distrib]

/-- **Tax timing does not change the budget set.** -/
theorem budget_eq {R : ℝ} {T : ℕ} {y g τ τ' : ℕ → ℝ} (h : GovBudget R T g τ)
    (h' : GovBudget R T g τ') : budget R T y τ = budget R T y τ' := by
  ext c
  simp only [budget, Set.mem_ofPred_eq, pv_sub]
  rw [h, h']

/-- **Ricardian equivalence.** -/
theorem ricardian {R : ℝ} {T : ℕ} {y g τ τ' : ℕ → ℝ} (U : (ℕ → ℝ) → ℝ)
    (h : GovBudget R T g τ) (h' : GovBudget R T g τ') {c : ℕ → ℝ}
    (hc : c ∈ budget R T y τ ∧ ∀ c' ∈ budget R T y τ, U c' ≤ U c) :
    c ∈ budget R T y τ' ∧ ∀ c' ∈ budget R T y τ', U c' ≤ U c := by
  rw [← budget_eq h h']; exact hc

/-- Budget set with a **no-borrowing** constraint (assets never negative),
in a two-period economy with `R = 1`. -/
def budgetNB (y τ : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {c | c 0 ≤ y 0 - τ 0 ∧ c 0 + c 1 ≤ (y 0 - τ 0) + (y 1 - τ 1)}

/-- **Borrowing constraints break Ricardian equivalence.** Income `(0, 2)`,
no spending; a debt-financed tax cut `τ' = (−1, 1)` satisfies the
government's budget constraint like `τ = 0`. With utility
`U(c) = −(c₀ − 1)² − (c₁ − 1)²`, the constrained household attains `U = 0`
(at `c = (1, 1)`) after the tax cut, strictly more than any plan affordable
without it: the tax cut changes optimal consumption. -/
theorem not_ricardian_of_constraint :
    let y : ℕ → ℝ := fun t => if t = 0 then 0 else 2
    let τ : ℕ → ℝ := fun _ => 0
    let τ' : ℕ → ℝ := fun t => if t = 0 then -1 else 1
    let U : (ℕ → ℝ) → ℝ := fun c => -(c 0 - 1) ^ 2 - (c 1 - 1) ^ 2
    GovBudget 1 2 (fun _ => 0) τ ∧ GovBudget 1 2 (fun _ => 0) τ' ∧
      ∃ c ∈ budgetNB y τ', ∀ c' ∈ budgetNB y τ, U c' < U c := by
  intro y τ τ' U
  refine ⟨by simp [GovBudget, pv, τ], by simp [GovBudget, pv, τ', Finset.sum_range_succ],
    fun _ => 1, ?_, fun c' hc' => ?_⟩
  · simp only [budgetNB, Set.mem_ofPred_eq, y, τ']; norm_num
  · simp only [budgetNB, Set.mem_ofPred_eq, y, τ] at hc'
    simp only [U]
    norm_num at hc' ⊢
    nlinarith [sq_nonneg (c' 1 - 1)]

end Ricardian
end Econ

end
