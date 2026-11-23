/-
# Money lotteries with finite support

MWG §6.C–6.D work with distribution functions `F` on monetary outcomes.
We use the finite-support case: a **simple money lottery** is a finitely
supported probability distribution on `ℝ`, stored as a finitely supported
function `ℝ →₀ ℝ` (Mathlib's `Finsupp`) of nonnegative probabilities that
sum to one. Expected utility is `E_F[u] = ∑ₓ F(x) u(x)`.

Finite support keeps the analysis elementary (no measure theory) while
covering the definitions and proofs of MWG §6.C–6.D: every
characterization there is tested on two-point and finitely supported
lotteries. Extending to general distributions is future work.
-/
module

public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ

open Finset

/-- A **simple money lottery**: a finitely supported probability
distribution on monetary outcomes. -/
structure SimpleLottery where
  /-- `prob x` is the probability of receiving `x`. -/
  prob : ℝ →₀ ℝ
  nonneg : ∀ x, 0 ≤ prob x
  total : prob.sum (fun _ q => q) = 1

namespace SimpleLottery

/-- The expected value `E_F[u] = ∑ₓ F(x) u(x)` of a payoff function `u`. -/
def expect (F : SimpleLottery) (u : ℝ → ℝ) : ℝ := F.prob.sum fun x q => q * u x

/-- The mean `E_F[x]`. -/
def mean (F : SimpleLottery) : ℝ := F.expect id

/-- The cumulative distribution function `F(t) = P(X ≤ t)`. -/
noncomputable def cdf (F : SimpleLottery) (t : ℝ) : ℝ := F.expect fun x => if x ≤ t then 1 else 0

variable (F : SimpleLottery)

theorem expect_eq_sum (u : ℝ → ℝ) : F.expect u = ∑ x ∈ F.prob.support, F.prob x * u x := rfl

/-- Expectations can be computed over any finite superset of the support. -/
theorem expect_eq_sum_of_subset {s : Finset ℝ} (hs : F.prob.support ⊆ s) (u : ℝ → ℝ) :
    F.expect u = ∑ x ∈ s, F.prob x * u x := by
  rw [expect_eq_sum]
  refine Finset.sum_subset hs fun x _ hx => ?_
  rw [Finsupp.notMem_support_iff.1 hx, zero_mul]

theorem sum_prob : ∑ x ∈ F.prob.support, F.prob x = 1 := F.total

theorem support_nonempty : F.prob.support.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have := F.sum_prob
  rw [h, Finset.sum_empty] at this
  exact zero_ne_one this

theorem expect_const (c : ℝ) : F.expect (fun _ => c) = c := by
  rw [expect_eq_sum, ← Finset.sum_mul, sum_prob, one_mul]

theorem expect_add (u v : ℝ → ℝ) : F.expect (fun x => u x + v x) = F.expect u + F.expect v := by
  simp only [expect_eq_sum, mul_add, Finset.sum_add_distrib]

theorem expect_sub (u v : ℝ → ℝ) : F.expect (fun x => u x - v x) = F.expect u - F.expect v := by
  simp only [expect_eq_sum, mul_sub, Finset.sum_sub_distrib]

theorem expect_const_mul (c : ℝ) (u : ℝ → ℝ) : F.expect (fun x => c * u x) = c * F.expect u := by
  simp only [expect_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Expectations only depend on `u` on (a superset of) the support. -/
theorem expect_congr {s : Finset ℝ} (hs : F.prob.support ⊆ s) {u v : ℝ → ℝ}
    (h : ∀ x ∈ s, u x = v x) : F.expect u = F.expect v := by
  rw [F.expect_eq_sum_of_subset hs, F.expect_eq_sum_of_subset hs]
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

theorem expect_mono {u v : ℝ → ℝ} (h : ∀ x ∈ F.prob.support, u x ≤ v x) :
    F.expect u ≤ F.expect v :=
  Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (h x hx) (F.nonneg x)

theorem expect_nonneg {u : ℝ → ℝ} (h : ∀ x ∈ F.prob.support, 0 ≤ u x) : 0 ≤ F.expect u := by
  simpa [expect_const] using F.expect_mono (u := fun _ => 0) h

/-! ### Two-point lotteries -/

/-- The lottery paying `x` with probability `a` and `y` with probability `1 - a`. -/
noncomputable def twoPoint (x y a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : SimpleLottery where
  prob := Finsupp.single x a + Finsupp.single y (1 - a)
  nonneg z := by
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    have : 0 ≤ 1 - a := by linarith
    split_ifs <;> linarith
  total := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    ring

theorem expect_twoPoint (x y a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ → ℝ) :
    (twoPoint x y a ha0 ha1).expect u = a * u x + (1 - a) * u y := by
  simp only [expect, twoPoint]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_single_index (zero_mul _), Finsupp.sum_single_index (zero_mul _)]

theorem support_twoPoint_subset (x y a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ((twoPoint x y a ha0 ha1).prob.support : Set ℝ) ⊆ {x, y} := by
  intro z hz
  have := Finsupp.support_add (Finset.mem_coe.1 hz)
  rcases Finset.mem_union.1 this with h | h
  · exact Or.inl (Finset.mem_singleton.1 (Finsupp.support_single_subset h))
  · exact Or.inr (Finset.mem_singleton.1 (Finsupp.support_single_subset h))

/-- The degenerate lottery `δₓ`. -/
noncomputable def pure (x : ℝ) : SimpleLottery where
  prob := Finsupp.single x 1
  nonneg z := by simp only [Finsupp.single_apply]; split_ifs <;> norm_num
  total := Finsupp.sum_single_index rfl

theorem expect_pure (x : ℝ) (u : ℝ → ℝ) : (pure x).expect u = u x := by
  simp only [expect, pure]
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]

/-! ### Linearity in the distribution -/

/-- Integrating `u` against a finitely supported signed measure. -/
def integral (g : ℝ →₀ ℝ) (u : ℝ → ℝ) : ℝ := g.sum fun x q => q * u x

theorem integral_add (g h : ℝ →₀ ℝ) (u : ℝ → ℝ) :
    integral (g + h) u = integral g u + integral h u :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem integral_smul (c : ℝ) (g : ℝ →₀ ℝ) (u : ℝ → ℝ) :
    integral (c • g) u = c * integral g u := by
  unfold integral
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by simp [smul_eq_mul, mul_assoc]

theorem integral_finset_sum {β : Type*} (s : Finset β) (g : β → ℝ →₀ ℝ) (u : ℝ → ℝ) :
    integral (∑ b ∈ s, g b) u = ∑ b ∈ s, integral (g b) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [integral]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, integral_add, ih]

theorem expect_eq_integral (u : ℝ → ℝ) : F.expect u = integral F.prob u := rfl

end SimpleLottery

end Econ
