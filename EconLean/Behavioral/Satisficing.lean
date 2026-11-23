/-
# Satisficing (Simon 1955)

References. H. Simon (1955), "A Behavioral Model of Rational Choice",
*QJE* 69(1); A. Rubinstein (2012), *Lecture Notes in Microeconomic Theory*,
Lecture 3 ("satisficing is consistent with rational choice").

A satisficer examines the alternatives in a fixed search order (here the
natural order on `Fin n`; any fixed search order reduces to this by
relabeling) and picks the first one whose utility reaches an aspiration
level `v`; if none does, it picks the last alternative examined.

**Results.**
* `satisfice_mem`: the choice belongs to the menu.
* `satisfice_isMax` (Rubinstein, Lecture 3): the satisficing choice function is
  **rationalizable**: it maximizes the injective ranking `rank`, which puts
  every satisfactory alternative above every unsatisfactory one, earlier
  satisfactory alternatives first and later unsatisfactory ones first.
  So satisficing, although procedurally very different from optimization, is
  observationally equivalent to maximizing a strict preference.
* `satisfice_warp`: hence it satisfies WARP.
* `satisfice_ne_argmax`: the choice need not maximize `u`: an earlier,
  worse but satisfactory alternative is chosen (so the rationalizing
  preference is not the utility ranking).
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace Econ

namespace Satisficing

variable {n : ℕ}

/-- Satisfactory alternatives in a menu. -/
def sat (u : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) : Finset (Fin n) := S.filter fun x => v ≤ u x

/-- The satisficing choice from a nonempty menu: the first satisfactory
alternative in the search order, or the last alternative if none is
satisfactory. -/
def satisfice (u : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) : Fin n :=
  if h : (sat u v S).Nonempty then (sat u v S).min' h else S.max' hS

theorem satisfice_mem (u : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    satisfice u v S hS ∈ S := by
  unfold satisfice
  split_ifs with h
  · exact (Finset.mem_filter.1 ((sat u v S).min'_mem h)).1
  · exact S.max'_mem hS

/-- The rationalizing ranking: satisfactory alternatives score `2n − x`
(earlier is better), unsatisfactory ones score `x` (later is better). -/
def rank (u : Fin n → ℝ) (v : ℝ) (x : Fin n) : ℕ := if v ≤ u x then 2 * n - x else x

theorem rank_injective (u : Fin n → ℝ) (v : ℝ) : Function.Injective (rank u v) := by
  intro x y h
  have hx := x.isLt; have hy := y.isLt
  unfold rank at h
  split_ifs at h with h1 h2 h2 <;> apply Fin.ext <;> omega

/-- **Satisficing is rationalizable.** The satisficing choice is the unique
`rank`-maximizer of the menu. -/
theorem satisfice_isMax (u : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {y : Fin n} (hy : y ∈ S) (hne : y ≠ satisfice u v S hS) :
    rank u v y < rank u v (satisfice u v S hS) := by
  have hlt : ∀ a : Fin n, (a : ℕ) < n := fun a => a.isLt
  by_cases h : (sat u v S).Nonempty
  · rw [satisfice, dite_eq_left h] at hne ⊢
    set c := (sat u v S).min' h
    have hc : v ≤ u c := (Finset.mem_filter.1 ((sat u v S).min'_mem h)).2
    by_cases hyv : v ≤ u y
    · have hcy : c ≤ y := (sat u v S).min'_le y (Finset.mem_filter.2 ⟨hy, hyv⟩)
      have hcy' : c < y := lt_of_le_of_ne hcy (Ne.symm hne)
      simp only [rank, hc, hyv, ite_true]
      have : (c : ℕ) < y := hcy'
      have := hlt y
      omega
    · simp only [rank, hc, hyv, ite_true, ite_false]
      have := hlt y; have := hlt c
      omega
  · rw [satisfice, dite_eq_right h] at hne ⊢
    set c := S.max' hS
    have hyv : ¬ v ≤ u y := fun hyv => h ⟨y, Finset.mem_filter.2 ⟨hy, hyv⟩⟩
    have hcv : ¬ v ≤ u c := fun hcv => h ⟨c, Finset.mem_filter.2 ⟨S.max'_mem hS, hcv⟩⟩
    have hyc : y < c := lt_of_le_of_ne (S.le_max' y hy) hne
    simp only [rank, hyv, hcv, ite_false]
    exact hyc

/-- **WARP.** If `x` is chosen from `S` while `y ∈ S`, then `y` is never chosen
from a menu containing `x`. -/
theorem satisfice_warp (u : Fin n → ℝ) (v : ℝ) {S T : Finset (Fin n)} (hS : S.Nonempty)
    (hT : T.Nonempty) {x y : Fin n} (hxy : x ≠ y) (hyS : y ∈ S) (hxT : x ∈ T)
    (hx : satisfice u v S hS = x) : satisfice u v T hT ≠ y := by
  intro hy
  have h1 := satisfice_isMax u v S hS hyS (by rw [hx]; exact Ne.symm hxy)
  have h2 := satisfice_isMax u v T hT hxT (by rw [hy]; exact hxy)
  rw [hx] at h1; rw [hy] at h2
  omega

/-- **The rationalizing preference is not the utility ranking.** With search
order `0, 1`, aspiration `1` and utilities `u 0 = 1 < 2 = u 1`, the
satisficer chooses `0` from `{0, 1}`. -/
theorem satisfice_ne_argmax :
    satisfice (n := 2) ![1, 2] 1 Finset.univ Finset.univ_nonempty = 0 ∧
      (![1, 2] : Fin 2 → ℝ) 0 < ![1, 2] 1 := by
  refine ⟨?_, by norm_num⟩
  have h : (sat (n := 2) ![1, 2] 1 Finset.univ).Nonempty := ⟨0, by simp [sat]⟩
  rw [satisfice, dite_eq_left h]
  apply le_antisymm (Finset.min'_le _ _ (by simp [sat])) (Fin.zero_le _)

end Satisficing

end Econ
