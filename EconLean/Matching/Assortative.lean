/-
# Positive assortative matching (Becker 1973)

Becker (1973); Legros–Newman (2007); Chiappori, *Matching with Transfers*, Ch. 3. Men of
types `x₀ ≤ x₁ ≤ … ≤ x_{n−1}` are matched one-to-one with women of types
`y₀ ≤ … ≤ y_{n−1}`; a match between types `x` and `y` produces surplus `f x y`. A matching is
a permutation `σ` (man `i` marries woman `σ i`), and its total surplus is `∑ᵢ f(xᵢ, y_{σ i})`.

The surplus has **increasing differences** (is supermodular) if
`f x y' + f x' y ≤ f x y + f x' y'` whenever `x ≤ x'` and `y ≤ y'`: types are complements.

* `becker_pam`: with supermodular surplus, positive assortative matching (the identity: the
  `i`-th lowest man marries the `i`-th lowest woman) maximizes total surplus. In the
  transferable-utility matching market, surplus-maximizing matchings are exactly the stable
  ones (Shapley–Shubik 1971), which turns this into Becker's assortative-mating result; that
  equivalence, transfers and stability are not formalized here, nor are uniqueness under
  strict supermodularity and the negative-assortative (submodular) counterpart.
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Finset

/-- **Increasing differences** (supermodularity on `ℝ × ℝ`). -/
def HasIncreasingDifferences (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x x' y y', x ≤ x' → y ≤ y' → f x y' + f x' y ≤ f x y + f x' y'

/-- Total surplus of the matching `σ`. -/
def matchingSurplus {n : ℕ} (f : ℝ → ℝ → ℝ) (x y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, f (x i) (y (σ i))

/-- The players a permutation moves. -/
def movedSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n) := univ.filter fun i => σ i ≠ i

/-- **Becker's theorem.** With increasing differences and types sorted on both sides, the
positive assortative matching maximizes total surplus. -/
theorem becker_pam {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : HasIncreasingDifferences f)
    {x y : Fin n → ℝ} (hx : Monotone x) (hy : Monotone y) (σ : Equiv.Perm (Fin n)) :
    matchingSurplus f x y σ ≤ matchingSurplus f x y 1 := by
  induction hk : (movedSet σ).card using Nat.strong_induction_on generalizing σ with
  | _ k ih =>
  by_cases hne : (movedSet σ).Nonempty
  swap
  · -- `σ` moves nobody, so it is the identity.
    have : σ = 1 := Equiv.ext fun i => by
      by_contra h
      exact hne ⟨i, by simpa [movedSet] using h⟩
    rw [this]
  -- `c`: the highest moved man; everybody above `c` is fixed.
  set c := (movedSet σ).max' hne
  have hc : σ c ≠ c := by
    exact (mem_filter.1 ((movedSet σ).max'_mem hne)).2
  have hfix : ∀ i, c < i → σ i = i := fun i hi => by
    by_contra h
    exact absurd ((movedSet σ).le_max' i (by simp [movedSet, h])) (not_le.2 hi)
  have hσc : σ c < c := by
    rcases lt_or_gt_of_ne hc with h | h
    · exact h
    · exact absurd (σ.injective (hfix _ h)) hc
  -- `j`: the man matched with woman `c`; `j < c`.
  set j := σ.symm c
  have hj : σ j = c := σ.apply_symm_apply c
  have hjc : j ≠ c := fun h => hc (by rw [← h, hj, h])
  have hjlt : j < c := by
    rcases lt_or_gt_of_ne hjc with h | h
    · exact h
    · exact absurd (by rw [← hfix j h, hj]) hjc
  -- Swap the partners of `j` and `c`.
  set τ := σ * Equiv.swap j c
  have hτc : τ c = c := by simp [τ, hj]
  have hτj : τ j = σ c := by simp [τ]
  have hτo : ∀ i, i ≠ j → i ≠ c → τ i = σ i := fun i h1 h2 => by
    simp [τ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  -- The swap weakly raises surplus.
  have hgain : matchingSurplus f x y σ ≤ matchingSurplus f x y τ := by
    have hd : matchingSurplus f x y τ - matchingSurplus f x y σ =
        (f (x j) (y (τ j)) - f (x j) (y (σ j))) + (f (x c) (y (τ c)) - f (x c) (y (σ c))) := by
      rw [matchingSurplus, matchingSurplus, ← sum_sub_distrib]
      refine Fintype.sum_eq_add j c hjc fun i hi => ?_
      rw [hτo i hi.1 hi.2, sub_self]
    rw [hτj, hτc, hj] at hd
    have := hf (x j) (x c) (y (σ c)) (y c) (hx hjlt.le) (hy hσc.le)
    linarith
  -- `τ` moves fewer people.
  have hsub : movedSet τ ⊂ movedSet σ := by
    refine (ssubset_iff_of_subset fun i hi => ?_).2 ⟨c, ?_, ?_⟩
    · simp only [movedSet, mem_filter, mem_univ, true_and] at hi ⊢
      by_cases h1 : i = j
      · rw [h1, hj]; exact hjc.symm
      by_cases h2 : i = c
      · rw [h2, hτc] at hi; exact absurd rfl hi
      rwa [hτo i h1 h2] at hi
    · simp [movedSet, hc]
    · simp [movedSet, hτc]
  exact hgain.trans (ih _ (hk ▸ card_lt_card hsub) τ rfl)

/-- Witness: with `f x y = x y` (increasing differences) and types `0, 1`, the assortative
matching produces `1`, the reverse matching `0`. -/
example : matchingSurplus (fun a b => a * b) (fun i : Fin 2 => (i : ℝ)) (fun i => (i : ℝ))
      (Equiv.swap 0 1) = 0 ∧
    matchingSurplus (fun a b => a * b) (fun i : Fin 2 => (i : ℝ)) (fun i => (i : ℝ)) 1 = 1 := by
  simp [matchingSurplus, Fin.sum_univ_two]

end Econ
