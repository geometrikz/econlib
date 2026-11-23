/-
# The second-price (Vickrey) auction

Vickrey (1961); Krishna, *Auction Theory*, Prop. 2.1; MWG Example 23.C.4. Bidders `i ∈ I`
(at least two) submit sealed bids `bᵢ ∈ ℝ`. The highest bidder wins, ties going to the
lowest-indexed tied bidder, and pays the highest competing bid. Bidder `i` with value `vᵢ`
gets `vᵢ − maxⱼ≠ᵢ bⱼ` if she wins and `0` otherwise.

* `spa_truthful_dominant`: bidding one's value is a **weakly dominant strategy** in the sense
  of MWG Def. 8.B.5 (never worse, and strictly better against some bids of the others).
* `spa_truthful_nash`: truthful bidding is therefore a Nash equilibrium.
* `spa_efficient`: under truthful bidding the object goes to a bidder with the highest
  value.
-/
module

public import EconLean.Games.Strategic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Function Finset

variable {I : Type*} [Fintype I] [LinearOrder I] [Nontrivial I]

/-- Bidder `i` wins at the bids `b`: every other bid is lower, or equal with a higher index. -/
def spaWins (b : I → ℝ) (i : I) : Prop := ∀ j, j ≠ i → b j < b i ∨ (b j = b i ∧ i < j)

lemma erase_nonempty (i : I) : (univ.erase i).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩⟩

/-- The highest competing bid. -/
noncomputable def highestOther (b : I → ℝ) (i : I) : ℝ := (univ.erase i).sup' (erase_nonempty i) b

/-- Bidder `i`'s payoff in the second-price auction. -/
noncomputable def spaPayoff (v : I → ℝ) (i : I) (b : I → ℝ) : ℝ := by
  classical exact if spaWins b i then v i - highestOther b i else 0

lemma highestOther_update (b : I → ℝ) (i : I) (β : ℝ) :
    highestOther (update b i β) i = highestOther b i := by
  unfold highestOther
  refine sup'_congr _ rfl fun j hj => ?_
  rw [update_of_ne (mem_erase.1 hj).1]

lemma le_highestOther {b : I → ℝ} {i j : I} (hj : j ≠ i) : b j ≤ highestOther b i :=
  le_sup' b (mem_erase.2 ⟨hj, mem_univ _⟩)

lemma highestOther_le_of_wins {b : I → ℝ} {i : I} (h : spaWins b i) : highestOther b i ≤ b i :=
  sup'_le _ _ fun j hj => by
    rcases h j (mem_erase.1 hj).1 with h | h
    · exact h.le
    · exact h.1.le

lemma le_highestOther_of_not_wins {b : I → ℝ} {i : I} (h : ¬ spaWins b i) :
    b i ≤ highestOther b i := by
  simp only [spaWins, not_forall, not_or, not_and, not_lt] at h
  obtain ⟨j, hj, h1, -⟩ := h
  exact h1.trans (le_highestOther hj)

lemma wins_of_lt {b : I → ℝ} {i : I} (h : highestOther b i < b i) : spaWins b i :=
  fun _ hj => Or.inl ((le_highestOther hj).trans_lt h)

lemma not_wins_of_lt {b : I → ℝ} {i : I} (h : b i < highestOther b i) : ¬ spaWins b i :=
  fun hw => absurd (highestOther_le_of_wins hw) (not_le.2 h)

/-- Truthful bidding does at least as well as any other bid, whatever the others bid. -/
theorem spa_truthful_le (v : I → ℝ) (i : I) (b : I → ℝ) (β : ℝ) :
    spaPayoff v i (update b i β) ≤ spaPayoff v i (update b i (v i)) := by
  classical
  have h1 := highestOther_update b i β
  have h2 := highestOther_update b i (v i)
  set h := highestOther b i
  have A : spaWins (update b i (v i)) i → h ≤ v i := fun hw => by
    have := highestOther_le_of_wins hw
    rwa [h2, update_self] at this
  have B : ¬ spaWins (update b i (v i)) i → v i ≤ h := fun hw => by
    have := le_highestOther_of_not_wins hw
    rwa [h2, update_self] at this
  unfold spaPayoff
  by_cases hw : spaWins (update b i (v i)) i <;> by_cases hw' : spaWins (update b i β) i <;>
    simp only [hw, hw', ↓reduceIte, h1, h2, le_refl]
  · linarith [A hw]
  · linarith [B hw]

/-- **Truthful bidding is weakly dominant** in the second-price auction (Vickrey 1961). -/
theorem spa_truthful_dominant (v : I → ℝ) (i : I) :
    IsDominant (fun j => spaPayoff v j) i (v i) := by
  refine ⟨fun b β => spa_truthful_le v i b β, fun β hβ => ?_⟩
  -- Let all others bid halfway between `β` and `v i`.
  set m := (β + v i) / 2
  have hm : ∀ β', highestOther (update (fun _ : I => m) i β') i = m := fun β' => by
    rw [highestOther_update]
    exact le_antisymm (sup'_le _ _ fun _ _ => le_rfl)
      (le_highestOther (b := fun _ => m) (exists_ne i).choose_spec)
  refine ⟨fun _ => m, ?_⟩
  simp only
  classical
  unfold spaPayoff
  rcases lt_or_gt_of_ne hβ with hlt | hlt
  · -- Underbidding loses when truthful bidding wins at a positive surplus.
    have hw : spaWins (update (fun _ => m) i (v i)) i := wins_of_lt (by
      rw [hm, update_self]; simp only [m]; linarith)
    have hw' : ¬ spaWins (update (fun _ => m) i β) i := not_wins_of_lt (by
      rw [hm, update_self]; simp only [m]; linarith)
    simp only [hw, hw', ↓reduceIte, hm, m]
    linarith
  · -- Overbidding wins at a loss when truthful bidding loses.
    have hw : ¬ spaWins (update (fun _ => m) i (v i)) i := not_wins_of_lt (by
      rw [hm, update_self]; simp only [m]; linarith)
    have hw' : spaWins (update (fun _ => m) i β) i := wins_of_lt (by
      rw [hm, update_self]; simp only [m]; linarith)
    simp only [hw, hw', ↓reduceIte, hm, m]
    linarith

/-- Truthful bidding is a Nash equilibrium of the second-price auction. -/
theorem spa_truthful_nash (v : I → ℝ) : IsNash (fun j => spaPayoff v j) v :=
  isNash_of_dominant fun i => spa_truthful_dominant v i

omit [Fintype I] [Nontrivial I] in
/-- **Efficiency**: under truthful bidding the winner has a highest value. -/
theorem spa_efficient {v : I → ℝ} {i : I} (hw : spaWins v i) (j : I) : v j ≤ v i := by
  by_cases hj : j = i
  · rw [hj]
  · rcases hw j hj with h | h
    · exact h.le
    · exact h.1.le

/-- **Someone wins**: the highest bidder with the lowest index. -/
theorem spa_exists_winner (b : I → ℝ) : ∃ i, spaWins b i := by
  classical
  obtain ⟨M, -, hM⟩ := exists_max_image (univ : Finset I) b univ_nonempty
  set T := univ.filter fun j => b j = b M
  obtain ⟨i, hiT, hi⟩ := exists_min_image T id ⟨M, by simp [T]⟩
  have hbi : b i = b M := (mem_filter.1 hiT).2
  refine ⟨i, fun j hj => ?_⟩
  rcases lt_or_eq_of_le (hM j (mem_univ _)) with h | h
  · left; rw [hbi]; exact h
  · right
    refine ⟨h.trans hbi.symm, lt_of_le_of_ne (hi j (by simp [T, h])) (Ne.symm hj)⟩

end Econ
