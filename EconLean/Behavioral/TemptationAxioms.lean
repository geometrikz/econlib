/-
# Menu preferences from axioms: set betweenness and strategic rationality

References. F. Gul and W. Pesendorfer (2001), "Temptation and Self-Control",
*Econometrica* 69(6); D. Kreps (1979), "A Representation Theorem for
'Preference for Flexibility'", *Econometrica* 47(3).

This file gives a finite-menu route towards sufficiency for menu-preference
representations: an alternative to Gul–Pesendorfer's own proof (which builds
a linear utility on menus of lotteries and then applies set betweenness), not
a step of it. It works with a preference on finite menus (nonempty `Finset`s)
of an arbitrary alternative set `X` that is represented by a real utility
`W`. All axioms used are ordinal. A complete transitive preference on menus
of an uncountable `X` need not have such a representation, so a
relation-valued version would be more general. `W ∅` is unconstrained; the
examples assign it arbitrarily.

**Results.**
* `SetBetweenness W`: `W B ≤ W A` implies `W B ≤ W (A ∪ B) ≤ W A`.
* `between_biUnion`: under set betweenness, the value of a finite nonempty
  union of nonempty menus lies between the smallest and largest values of the
  pieces.
* `eq_maxmin_pairs` (**pair reduction**): under set betweenness alone,
  `W A = max_{x ∈ A} min_{y ∈ A} W {x, y}`, so a set-betweenness preference is
  determined by its values on menus with at most two elements.
* `eq_of_pairs`: two set-betweenness utilities that agree on all menus with at
  most two elements agree on all nonempty menus.
* `eq_GP_of_pairs` (**GP extension**): a set-betweenness utility that agrees
  with a Gul–Pesendorfer utility `max (u + v) − max v` on menus with at most two
  elements is that Gul–Pesendorfer utility on every nonempty finite menu.
* `StrategicRational W`: `W B ≤ W A` implies `W (A ∪ B) = W A`, the
  strategic-rationality special case of Kreps (no preference for flexibility;
  Kreps' main axiom, preference for flexibility, is not treated).
  `eq_sup_singleton` (**Kreps' indirect utility**): then
  `W A = max_{x ∈ A} W {x}`; `strategicRational_sup` is the converse.
* `GP_setBetweenness`, `W_eq_maxmin_pairs`: non-vacuity, the Gul–Pesendorfer
  utility (extended by `0` to the empty menu as `GP`) satisfies set
  betweenness and the pair reduction.
* `sbExample_setBetweenness`, `sbExample_not_GP`: set betweenness alone does
  not give the GP form. A menu utility on three alternatives satisfies set
  betweenness but its values on menus with at most two elements are not
  those of `max (u + v) − max v` for any `u`, `v`. Set betweenness places no
  restriction across different pairs; GP obtain such restrictions from
  independence over lotteries.

**Scope.** Gul–Pesendorfer's full sufficiency theorem works with compact sets
of lotteries and uses independence and continuity to make the pair values
themselves of the form `max (u + v) − max v` with linear `u`, `v`. That step
is not formalized: here the pair values are an input. What is shown is that
set betweenness, with no other axiom (not even continuity), reduces any
finite menu to its pairs. Which pair data arise from some set-betweenness
utility is not characterized.
-/
module

public import EconLean.Behavioral.Temptation
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace Econ

namespace Temptation

variable {X : Type*} [DecidableEq X]

open Finset

/-- **Set betweenness** (Gul–Pesendorfer): `A ≽ B` implies `A ≽ A ∪ B ≽ B`. -/
def SetBetweenness (W : Finset X → ℝ) : Prop :=
  ∀ A B : Finset X, A.Nonempty → B.Nonempty → W B ≤ W A → W B ≤ W (A ∪ B) ∧ W (A ∪ B) ≤ W A

/-- **Strategic rationality** (Kreps): `A ≽ B` implies `A ∼ A ∪ B`. -/
def StrategicRational (W : Finset X → ℝ) : Prop :=
  ∀ A B : Finset X, A.Nonempty → B.Nonempty → W B ≤ W A → W (A ∪ B) = W A

theorem union_between {W : Finset X → ℝ} (hW : SetBetweenness W) {A B : Finset X}
    (hA : A.Nonempty) (hB : B.Nonempty) : min (W A) (W B) ≤ W (A ∪ B) ∧ W (A ∪ B) ≤ max (W A) (W B) := by
  rcases le_total (W B) (W A) with h | h
  · obtain ⟨h1, h2⟩ := hW A B hA hB h
    exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · obtain ⟨h1, h2⟩ := hW B A hB hA h
    rw [union_comm]
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩

/-- Under set betweenness, the value of a finite nonempty union of nonempty
menus lies between the smallest and the largest value of the pieces. -/
theorem between_biUnion {ι : Type*} [DecidableEq ι] {W : Finset X → ℝ} (hW : SetBetweenness W)
    {s : Finset ι} (hs : s.Nonempty) {F : ι → Finset X} (hF : ∀ i ∈ s, (F i).Nonempty) :
    s.inf' hs (fun i => W (F i)) ≤ W (s.biUnion F) ∧ W (s.biUnion F) ≤ s.sup' hs (fun i => W (F i)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    have hF' : ∀ j ∈ s, (F j).Nonempty := fun j hj => hF j (mem_cons.2 (Or.inr hj))
    obtain ⟨ih1, ih2⟩ := ih hF'
    have hFi : (F i).Nonempty := hF i (mem_cons_self i s)
    have hU : (s.biUnion F).Nonempty := by
      obtain ⟨j, hj⟩ := hs
      obtain ⟨x, hx⟩ := hF' j hj
      exact ⟨x, mem_biUnion.2 ⟨j, hj, hx⟩⟩
    have e : (cons i s hi).biUnion F = F i ∪ s.biUnion F := by rw [cons_eq_insert, biUnion_insert]
    rw [e, inf'_cons hs, sup'_cons hs]
    obtain ⟨h1, h2⟩ := union_between hW hFi hU
    constructor
    · exact le_trans (min_le_min le_rfl ih1) h1
    · exact h2.trans (max_le_max le_rfl ih2)

/-- **Pair reduction.** Under set betweenness alone, the value of a finite
menu is `max_{x ∈ A} min_{y ∈ A} W {x, y}`. -/
theorem eq_maxmin_pairs {W : Finset X → ℝ} (hW : SetBetweenness W) {A : Finset X}
    (hA : A.Nonempty) : W A = A.sup' hA (fun x => A.inf' hA (fun y => W {x, y})) := by
  apply le_antisymm
  · -- for each `x`, pick a worst partner `y x`; `A` is the union of the pairs
    have hy : ∀ x ∈ A, ∃ y ∈ A, A.inf' hA (fun y => W {x, y}) = W {x, y} := fun x _ => by
      obtain ⟨y, hy, h⟩ := exists_mem_eq_inf' hA (fun y => W {x, y})
      exact ⟨y, hy, h⟩
    choose! y hyA hyeq using hy
    have hcover : A.biUnion (fun x => ({x, y x} : Finset X)) = A := by
      ext z
      simp only [mem_biUnion, mem_insert, mem_singleton]
      constructor
      · rintro ⟨x, hx, rfl | rfl⟩
        · exact hx
        · exact hyA x hx
      · exact fun hz => ⟨z, hz, Or.inl rfl⟩
    have := (between_biUnion hW hA (F := fun x => ({x, y x} : Finset X))
      fun x _ => insert_nonempty _ _).2
    rw [hcover] at this
    refine this.trans (sup'_le _ _ fun x hx => ?_)
    rw [← hyeq x hx]
    exact le_sup' (fun x => A.inf' hA (fun y => W {x, y})) hx
  · obtain ⟨x, hx, hmax⟩ := exists_mem_eq_sup' hA (fun x => A.inf' hA (fun y => W {x, y}))
    rw [hmax]
    have hcover : A.biUnion (fun y => ({x, y} : Finset X)) = A := by
      ext z
      simp only [mem_biUnion, mem_insert, mem_singleton]
      constructor
      · rintro ⟨y, hy, rfl | rfl⟩
        · exact hx
        · exact hy
      · exact fun hz => ⟨z, hz, Or.inr rfl⟩
    have := (between_biUnion hW hA (F := fun y => ({x, y} : Finset X))
      fun y _ => insert_nonempty _ _).1
    rwa [hcover] at this

/-- Set-betweenness utilities are determined by their values on menus with at
most two elements. -/
theorem eq_of_pairs {W W' : Finset X → ℝ} (hW : SetBetweenness W) (hW' : SetBetweenness W')
    (h : ∀ x y : X, W {x, y} = W' {x, y}) {A : Finset X} (hA : A.Nonempty) : W A = W' A := by
  rw [eq_maxmin_pairs hW hA, eq_maxmin_pairs hW' hA]
  simp only [h]

omit [DecidableEq X] in
/-- The Gul–Pesendorfer utility as a function on all finite menus (its value
on the empty menu is irrelevant and set to `0`). -/
noncomputable def GP (u v : X → ℝ) (A : Finset X) : ℝ :=
  if h : A.Nonempty then W u v A h else 0

omit [DecidableEq X] in
theorem GP_of_nonempty (u v : X → ℝ) {A : Finset X} (hA : A.Nonempty) : GP u v A = W u v A hA := by
  simp [GP, hA]

theorem GP_setBetweenness (u v : X → ℝ) : SetBetweenness (GP u v) := by
  intro A B hA hB h
  rw [GP_of_nonempty u v hA, GP_of_nonempty u v hB] at h
  rw [GP_of_nonempty u v hA, GP_of_nonempty u v hB,
    GP_of_nonempty u v (hA.mono subset_union_left)]
  exact (setBetweenness u v hA hB h).symm

/-- Non-vacuity: the Gul–Pesendorfer utility satisfies the pair reduction. -/
theorem W_eq_maxmin_pairs (u v : X → ℝ) {A : Finset X} (hA : A.Nonempty) :
    W u v A hA = A.sup' hA (fun x => A.inf' hA (fun y => W u v {x, y} (insert_nonempty x {y}))) := by
  rw [← GP_of_nonempty u v hA, eq_maxmin_pairs (GP_setBetweenness u v) hA]
  simp only [GP_of_nonempty u v (insert_nonempty _ _)]

/-- **GP extension.** A set-betweenness utility that agrees with a
Gul–Pesendorfer utility on menus with at most two elements is that
Gul–Pesendorfer utility on every nonempty finite menu. -/
theorem eq_GP_of_pairs {W' : Finset X → ℝ} (hW : SetBetweenness W') (u v : X → ℝ)
    (h : ∀ x y : X, W' {x, y} = W u v {x, y} (insert_nonempty x {y})) {A : Finset X}
    (hA : A.Nonempty) : W' A = W u v A hA := by
  rw [← GP_of_nonempty u v hA]
  exact eq_of_pairs hW (GP_setBetweenness u v)
    (fun x y => by rw [h, GP_of_nonempty u v (insert_nonempty _ _)]) hA

theorem StrategicRational.setBetweenness {W : Finset X → ℝ} (hW : StrategicRational W) :
    SetBetweenness W := fun A B hA hB h => by
  rw [hW A B hA hB h]; exact ⟨h, le_rfl⟩

/-- **Kreps' indirect utility.** A strategically rational menu utility is the
best singleton value in the menu. -/
theorem eq_sup_singleton {W : Finset X → ℝ} (hW : StrategicRational W) {A : Finset X}
    (hA : A.Nonempty) : W A = A.sup' hA (fun x => W {x}) := by
  apply le_antisymm
  · have := (between_biUnion hW.setBetweenness hA (F := fun x => ({x} : Finset X))
      fun x _ => singleton_nonempty x).2
    rwa [biUnion_singleton_eq_self] at this
  · refine sup'_le _ _ fun x hx => ?_
    rcases le_total (W {x}) (W A) with h | h
    · exact h
    · have := hW {x} A (singleton_nonempty x) hA h
      rw [singleton_union, insert_eq_of_mem hx] at this
      exact this.ge

/-- Converse: an indirect utility `max_{x∈A} f x` is strategically rational. -/
theorem strategicRational_sup (f : X → ℝ) :
    StrategicRational (fun A => if h : A.Nonempty then A.sup' h f else 0) := by
  intro A B hA hB h
  simp only [hA, hB, hA.mono subset_union_left, dite_true] at h ⊢
  rw [sup'_union hA hB]
  exact sup_of_le_left h

/-! ### Set betweenness alone does not give the GP form -/

/-- A set-betweenness menu utility on three alternatives `0, 1, 2` (values
doubled to stay in `ℕ`): singletons `0, 2, 4`, pairs `{0,1} ↦ 1`,
`{1,2} ↦ 3`, `{0,2} ↦ 3`, the full menu `↦ 3`. -/
def sbNat (A : Finset (Fin 3)) : ℕ :=
  if A = {0} then 0 else if A = {1} then 2 else if A = {2} then 4 else
  if A = {0, 1} then 1 else if A = {1, 2} then 3 else if A = {0, 2} then 3 else 3

/-- The example as a real-valued menu utility. -/
noncomputable def sbExample (A : Finset (Fin 3)) : ℝ := (sbNat A : ℝ)

theorem sbNat_setBetweenness : ∀ A B : Finset (Fin 3), A.Nonempty → B.Nonempty →
    sbNat B ≤ sbNat A → sbNat B ≤ sbNat (A ∪ B) ∧ sbNat (A ∪ B) ≤ sbNat A := by
  decide

theorem sbExample_setBetweenness : SetBetweenness sbExample := fun A B hA hB h => by
  simp only [sbExample, Nat.cast_le] at h ⊢
  exact sbNat_setBetweenness A B hA hB h

/-- **Set betweenness is not sufficient on its own**: the example satisfies
set betweenness but is not a Gul–Pesendorfer utility `max (u + v) − max v`
for any `u`, `v`: already its values on menus with at most two elements
are not of that form. -/
theorem sbExample_not_GP : ¬ ∃ u v : Fin 3 → ℝ, ∀ x y : Fin 3,
    sbExample {x, y} = W u v {x, y} (insert_nonempty x {y}) := by
  rintro ⟨u, v, h⟩
  have e0 := h 0 0
  have e1 := h 1 1
  have e2 := h 2 2
  have e01 := h 0 1
  have e12 := h 1 2
  have e02 := h 0 2
  simp only [W, sup'_pair, max_self, add_sub_cancel_right] at e0 e1 e2 e01 e12 e02
  simp only [sbExample, sbNat] at e0 e1 e2 e01 e12 e02
  norm_num [Finset.ext_iff, Fin.forall_fin_succ] at e0 e1 e2 e01 e12 e02
  rcases le_total (u 0 + v 0) (u 1 + v 1) with h1 | h1 <;>
  rcases le_total (v 0) (v 1) with h2 | h2 <;>
  rcases le_total (u 1 + v 1) (u 2 + v 2) with h3 | h3 <;>
  rcases le_total (v 1) (v 2) with h4 | h4 <;>
  rcases le_total (u 0 + v 0) (u 2 + v 2) with h5 | h5 <;>
  rcases le_total (v 0) (v 2) with h6 | h6 <;>
  simp only [max_eq_left, max_eq_right, h1, h2, h3, h4, h5, h6] at e01 e12 e02 <;>
  linarith

end Temptation

end Econ
