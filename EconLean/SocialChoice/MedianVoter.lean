/-
# The median voter theorem (Black 1948)

MWG §21.D (Prop. 21.D.1); Black (1948). Alternatives are real numbers (e.g. a tax rate).
Voter `i` has **single-peaked** preferences: utility `u i` strictly increases up to the voter's
peak `peak i` and strictly decreases after it.

Main results:
* `median_condorcet` (Black's theorem): an alternative `m` that is a **median** of the peaks
  (more than half of the voters have peak `≤ m` and more than half have peak `≥ m`) defeats
  every other alternative by a strict majority in pairwise voting: it is a Condorcet winner.
* `exists_median`: with an odd number of voters such a median exists (one of the peaks).
* `median_not_defeated` (MWG Prop. 21.D.1 as stated there): for any number of voters, a
  **weak** median (at least half the peaks on each side, `IsWeakMedianPeak`) is not defeated
  by any alternative; `exists_weakMedian`: a weak median peak always exists.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Econ

open Finset

/-- `u` is **single-peaked** with peak `x`. -/
def SinglePeaked (u : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ y z, y < z → z ≤ x → u y < u z) ∧ (∀ y z, x ≤ y → y < z → u z < u y)

variable {I : Type*} [Fintype I]

/-- `m` is a **median** of the peaks: strictly more than half of the voters have their peak
weakly below `m`, and strictly more than half weakly above. -/
def IsMedianPeak (peak : I → ℝ) (m : ℝ) : Prop :=
  Fintype.card I < 2 * (univ.filter fun i => peak i ≤ m).card ∧
    Fintype.card I < 2 * (univ.filter fun i => m ≤ peak i).card

/-- **Black's median voter theorem, strict form** (Black 1948; compare MWG Prop. 21.D.1). With
single-peaked preferences, a strict median `m` of the peaks (which exists for an odd number of
voters, `exists_median`) beats every other alternative `y` by a strict majority. For any
number of voters see `median_not_defeated`. -/
theorem median_condorcet {peak : I → ℝ} {u : I → ℝ → ℝ} (hsp : ∀ i, SinglePeaked (u i) (peak i))
    {m : ℝ} (hm : IsMedianPeak peak m) (y : ℝ) (hy : y ≠ m) :
    Fintype.card I < 2 * (univ.filter fun i => u i y < u i m).card := by
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · -- Everyone with peak `≥ m` prefers `m` to `y < m`.
    refine hm.2.trans_le (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact (hsp i).1 y m hlt hi
  · -- Everyone with peak `≤ m` prefers `m` to `y > m`.
    refine hm.1.trans_le (Nat.mul_le_mul_left 2 (card_le_card fun i hi => ?_))
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact (hsp i).2 m y hi hgt

/-- **A median peak exists** when the number of voters is odd. -/
theorem exists_median (peak : I → ℝ) (hodd : Odd (Fintype.card I)) :
    ∃ i₀, IsMedianPeak peak (peak i₀) := by
  classical
  set n := Fintype.card I
  have hne : (univ : Finset I).Nonempty := by
    rw [univ_nonempty_iff, ← Fintype.card_pos_iff]; exact hodd.pos
  -- Candidates: peaks with more than half of the peaks weakly below.
  set C := univ.filter fun i => n < 2 * (univ.filter fun j => peak j ≤ peak i).card
  have hCne : C.Nonempty := by
    obtain ⟨i, -, hi⟩ := exists_max_image univ peak hne
    refine ⟨i, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have : (univ.filter fun j => peak j ≤ peak i) = univ := filter_true_of_mem fun j _ => hi j (mem_univ j)
    rw [this, card_univ]
    have := hodd.pos
    omega
  obtain ⟨i₀, hi₀C, hmin⟩ := exists_min_image C peak hCne
  refine ⟨i₀, (mem_filter.1 hi₀C).2, ?_⟩
  -- Strictly fewer than half of the peaks lie strictly below `peak i₀`.
  have hbelow : 2 * (univ.filter fun j => peak j < peak i₀).card < n := by
    by_cases hB : (univ.filter fun j => peak j < peak i₀).Nonempty
    · obtain ⟨k, hk, hkmax⟩ := exists_max_image _ peak hB
      have hk' := (mem_filter.1 hk).2
      have heq : (univ.filter fun j => peak j < peak i₀) = univ.filter fun j => peak j ≤ peak k := by
        ext j
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro hj; exact hkmax j (mem_filter.2 ⟨mem_univ _, hj⟩)
        · intro hj; exact lt_of_le_of_lt hj hk'
      rw [heq]
      have hkC : k ∉ C := fun hkC => absurd (hmin k hkC) (not_le.2 hk')
      have : ¬ n < 2 * (univ.filter fun j => peak j ≤ peak k).card := fun h =>
        hkC (mem_filter.2 ⟨mem_univ _, h⟩)
      push Not at this
      -- `n` is odd, so equality is impossible.
      rcases this.lt_or_eq with h | h
      · exact h
      · exact absurd (show Even n from ⟨(univ.filter fun j => peak j ≤ peak k).card, by omega⟩)
          (Nat.not_even_iff_odd.2 hodd)
    · rw [not_nonempty_iff_eq_empty.1 hB, card_empty]; exact hodd.pos
  have hsplit := card_filter_add_card_filter_not (s := univ) (fun j => peak j < peak i₀)
  have hcomp : (univ.filter fun j => ¬ peak j < peak i₀) = univ.filter fun j => peak i₀ ≤ peak j := by
    ext j; simp
  rw [hcomp, card_univ] at hsplit
  omega

/-! ### The weak median (any number of voters) -/

/-- `m` is a **weak median** of the peaks (MWG Def. 21.D.2): at least half of the voters
have their peak weakly below `m`, and at least half weakly above. -/
def IsWeakMedianPeak (peak : I → ℝ) (m : ℝ) : Prop :=
  Fintype.card I ≤ 2 * (univ.filter fun i => peak i ≤ m).card ∧
    Fintype.card I ≤ 2 * (univ.filter fun i => m ≤ peak i).card

/-- **The median voter theorem, weak form** (MWG Prop. 21.D.1). With single-peaked
preferences, a weak median `m` of the peaks is not defeated by any alternative: the voters who
strictly prefer `y` to `m` are at most half of the electorate, and no more numerous than those
who strictly prefer `m` to `y` (`#{y ≻ m} ≤ #{m ≻ y}`, so `m` wins or ties every pairwise
majority vote, indifferent voters abstaining). -/
theorem median_not_defeated {peak : I → ℝ} {u : I → ℝ → ℝ}
    (hsp : ∀ i, SinglePeaked (u i) (peak i)) {m : ℝ} (hm : IsWeakMedianPeak peak m) (y : ℝ) :
    2 * (univ.filter fun i => u i m < u i y).card ≤ Fintype.card I ∧
      (univ.filter fun i => u i m < u i y).card ≤
        (univ.filter fun i => u i y < u i m).card := by
  rcases lt_trichotomy y m with hlt | rfl | hgt
  · -- Voters with peak `≥ m` strictly prefer `m`, and they are at least half.
    have hA : (univ.filter fun i => m ≤ peak i) ⊆ univ.filter fun i => u i y < u i m :=
      fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact (hsp i).1 y m hlt hi
    have hB : (univ.filter fun i => u i m < u i y) ⊆ univ.filter fun i => ¬ (m ≤ peak i) :=
      fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact fun h => lt_asymm hi ((hsp i).1 y m hlt h)
    have h1 := card_le_card hA
    have h2 := card_le_card hB
    have h3 := card_filter_add_card_filter_not (s := univ) (fun i => m ≤ peak i)
    have := hm.2
    rw [card_univ] at h3
    omega
  · simp
  · have hA : (univ.filter fun i => peak i ≤ m) ⊆ univ.filter fun i => u i y < u i m :=
      fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact (hsp i).2 m y hi hgt
    have hB : (univ.filter fun i => u i m < u i y) ⊆ univ.filter fun i => ¬ (peak i ≤ m) :=
      fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact fun h => lt_asymm hi ((hsp i).2 m y h hgt)
    have h1 := card_le_card hA
    have h2 := card_le_card hB
    have h3 := card_filter_add_card_filter_not (s := univ) (fun i => peak i ≤ m)
    have := hm.1
    rw [card_univ] at h3
    omega

/-- **A weak median peak exists** whenever there is at least one voter. -/
theorem exists_weakMedian [Nonempty I] (peak : I → ℝ) : ∃ i₀, IsWeakMedianPeak peak (peak i₀) := by
  classical
  set n := Fintype.card I
  have hne : (univ : Finset I).Nonempty := univ_nonempty
  set C := univ.filter fun i => n ≤ 2 * (univ.filter fun j => peak j ≤ peak i).card
  have hCne : C.Nonempty := by
    obtain ⟨i, -, hi⟩ := exists_max_image univ peak hne
    refine ⟨i, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have : (univ.filter fun j => peak j ≤ peak i) = univ :=
      filter_true_of_mem fun j _ => hi j (mem_univ j)
    rw [this, card_univ]
    omega
  obtain ⟨i₀, hi₀C, hmin⟩ := exists_min_image C peak hCne
  refine ⟨i₀, (mem_filter.1 hi₀C).2, ?_⟩
  have hbelow : 2 * (univ.filter fun j => peak j < peak i₀).card < n := by
    by_cases hB : (univ.filter fun j => peak j < peak i₀).Nonempty
    · obtain ⟨k, hk, hkmax⟩ := exists_max_image _ peak hB
      have hk' := (mem_filter.1 hk).2
      have heq : (univ.filter fun j => peak j < peak i₀) =
          univ.filter fun j => peak j ≤ peak k := by
        ext j
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro hj; exact hkmax j (mem_filter.2 ⟨mem_univ _, hj⟩)
        · intro hj; exact lt_of_le_of_lt hj hk'
      rw [heq]
      have hkC : k ∉ C := fun hkC => absurd (hmin k hkC) (not_le.2 hk')
      have : ¬ n ≤ 2 * (univ.filter fun j => peak j ≤ peak k).card := fun h =>
        hkC (mem_filter.2 ⟨mem_univ _, h⟩)
      omega
    · rw [not_nonempty_iff_eq_empty.1 hB, card_empty]
      exact Fintype.card_pos
  have hsplit := card_filter_add_card_filter_not (s := univ) (fun j => peak j < peak i₀)
  have hcomp : (univ.filter fun j => ¬ peak j < peak i₀) =
      univ.filter fun j => peak i₀ ≤ peak j := by
    ext j; simp
  rw [hcomp, card_univ] at hsplit
  omega

/-- Witness that the weak form is not vacuous for an even electorate: with two voters whose
peaks are `0` and `1`, the peak `0` is a weak median (no strict median exists). -/
example : IsWeakMedianPeak (fun i : Fin 2 => (i : ℝ)) 0 ∧
    ¬ ∃ m, IsMedianPeak (fun i : Fin 2 => (i : ℝ)) m := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [card_filter]
  · simp
  · rintro ⟨m, h1, h2⟩
    simp only [card_filter, Fin.sum_univ_two, Fintype.card_fin] at h1 h2
    norm_num at h1 h2
    split_ifs at h1 h2 with ha hb hc hd <;> first | omega | linarith

end Econ
