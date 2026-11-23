/-
# Transferable-utility games and the Shapley value

Shapley (1953); MWG §18.AA; Osborne–Rubinstein, *A Course in Game Theory*, §14.4;
Peleg–Sudhölter, Ch. 6. A **transferable-utility (TU) game** on a finite set of players `N`
assigns a worth `v S` to every coalition `S ⊆ N`. (The usual normalization `v ∅ = 0` is not
built in; the efficiency axiom below is stated as `∑ φᵢ = v N − v ∅`, which is `v N` for
normalized games.)

The **Shapley value** of player `i` is `i`'s expected marginal contribution
`v (Pᵢ ∪ {i}) − v Pᵢ` when the players arrive in a uniformly random order and `Pᵢ` is the set
of players who arrived before `i` (Shapley's random-order formula).

Shapley's axioms on a value `φ : TUGame N → N → ℝ`:
* **efficiency**: `∑ᵢ φ v i = v N − v ∅`;
* **symmetry**: if `i` and `j` are interchangeable in `v`
  (`v (S ∪ {i}) = v (S ∪ {j})` whenever `i, j ∉ S`) then `φ v i = φ v j`;
* **null player**: if `v (S ∪ {i}) = v S` for all `S` then `φ v i = 0`;
* **additivity**: `φ (v + w) = φ v + φ w`.

Main results:
* `shapley_efficient`, `shapley_symmetric`, `shapley_null`, `shapley_add`: the Shapley
  value satisfies the four axioms.
* `eq_shapley_of_axioms` (Shapley 1953): it is the only value satisfying them. The proof
  writes every game as a combination of unanimity games (`game_eq_sum_unanimity`, Möbius
  inversion on the subset lattice) and computes any axiomatic value on each.
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Finset

/-- A **transferable-utility game**: the worth of each coalition. -/
abbrev TUGame (N : Type*) := Finset N → ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- An **arrival order** of the players: `σ i` is player `i`'s position in the queue. -/
abbrev PlayerOrder (N : Type*) [Fintype N] := N ≃ Fin (Fintype.card N)

/-- The players who arrive before `i` in the order `σ`. -/
def predSet (σ : PlayerOrder N) (i : N) : Finset N := univ.filter fun j => σ j < σ i

/-- Player `i`'s **marginal contribution** in the order `σ`. -/
def marginalContribution (v : TUGame N) (σ : PlayerOrder N) (i : N) : ℝ :=
  v (insert i (predSet σ i)) - v (predSet σ i)

/-- The **Shapley value**: the average marginal contribution over all arrival orders. -/
noncomputable def shapley (v : TUGame N) (i : N) : ℝ :=
  (∑ σ : PlayerOrder N, marginalContribution v σ i) / Fintype.card (PlayerOrder N)

/-- `i` and `j` are **symmetric** (interchangeable) in `v`. -/
def IsSymmetricPair (v : TUGame N) (i j : N) : Prop :=
  ∀ S, i ∉ S → j ∉ S → v (insert i S) = v (insert j S)

/-- `i` is a **null player** in `v`: `i` adds nothing to any coalition. -/
def IsNullPlayer (v : TUGame N) (i : N) : Prop := ∀ S, v (insert i S) = v S

/-- Shapley's four axioms for a value `φ`. -/
def IsShapleyAxioms (φ : TUGame N → N → ℝ) : Prop :=
  (∀ v, ∑ i, φ v i = v univ - v ∅) ∧
    (∀ v i j, IsSymmetricPair v i j → φ v i = φ v j) ∧
    (∀ v i, IsNullPlayer v i → φ v i = 0) ∧
    ∀ v w, φ (v + w) = φ v + φ w

/-! ### The Shapley value satisfies the axioms -/

/-- Marginal contributions along one order telescope to `v N − v ∅`. -/
lemma sum_marginal (v : TUGame N) (σ : PlayerOrder N) :
    ∑ i, marginalContribution v σ i = v univ - v ∅ := by
  set g : ℕ → ℝ := fun k => v (univ.filter fun j => (σ j : ℕ) < k)
  have hi : ∀ i, marginalContribution v σ i = g (σ i + 1) - g (σ i) := by
    intro i
    have h1 : insert i (predSet σ i) = univ.filter fun j => (σ j : ℕ) < σ i + 1 := by
      ext j
      simp only [predSet, mem_insert, mem_filter, mem_univ, true_and, Fin.lt_def]
      constructor
      · rintro (rfl | h) <;> omega
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
        · exact Or.inr h
        · exact Or.inl (σ.injective (Fin.ext h))
    have h2 : predSet σ i = univ.filter fun j => (σ j : ℕ) < σ i := by
      ext j; simp only [predSet, mem_filter, mem_univ, true_and, Fin.lt_def]
    simp only [marginalContribution]
    rw [h1, h2]
  simp only [hi]
  rw [Equiv.sum_comp σ (fun k : Fin _ => g (k + 1) - g k),
    Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k), sum_range_sub]
  simp only [g]
  congr 2
  · ext j; simp
  · ext j; simp

/-- **Efficiency.** -/
theorem shapley_efficient (v : TUGame N) : ∑ i, shapley v i = v univ - v ∅ := by
  have : Nonempty (PlayerOrder N) := ⟨Fintype.equivFin N⟩
  have hK : (Fintype.card (PlayerOrder N) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [shapley, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [sum_marginal, sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Fintype N] in
/-- Swapping two players fixes any coalition containing both or neither. -/
lemma map_swap_of_iff {i j : N} {S : Finset N} (h : i ∈ S ↔ j ∈ S) :
    S.map (Equiv.swap i j).toEmbedding = S := by
  ext k
  rw [mem_map_equiv, Equiv.symm_swap]
  rcases eq_or_ne k i with rfl | hki
  · rw [Equiv.swap_apply_left]; exact h.symm
  · rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

omit [Fintype N] in
/-- If `i` and `j` are symmetric, relabelling them does not change any worth. -/
lemma IsSymmetricPair.map_swap {v : TUGame N} {i j : N} (h : IsSymmetricPair v i j)
    (S : Finset N) : v (S.map (Equiv.swap i j).toEmbedding) = v S := by
  by_cases hij : (i ∈ S ↔ j ∈ S)
  · rw [map_swap_of_iff hij]
  by_cases hi : i ∈ S
  · have hj : j ∉ S := fun hj => hij ⟨fun _ => hj, fun _ => hi⟩
    have hiT : i ∉ S.erase i := notMem_erase i S
    have hjT : j ∉ S.erase i := fun h => hj (mem_of_mem_erase h)
    rw [← insert_erase hi, map_insert, Equiv.coe_toEmbedding, Equiv.swap_apply_left,
      map_swap_of_iff (iff_of_false hiT hjT)]
    exact (h _ hiT hjT).symm
  · have hj : j ∈ S := by tauto
    have hjT : j ∉ S.erase j := notMem_erase j S
    have hiT : i ∉ S.erase j := fun h => hi (mem_of_mem_erase h)
    rw [← insert_erase hj, map_insert, Equiv.coe_toEmbedding, Equiv.swap_apply_right,
      map_swap_of_iff (iff_of_false hiT hjT)]
    exact h _ hiT hjT

/-- **Symmetry.** -/
theorem shapley_symmetric {v : TUGame N} {i j : N} (h : IsSymmetricPair v i j) :
    shapley v i = shapley v j := by
  unfold shapley
  congr 1
  let E : PlayerOrder N ≃ PlayerOrder N :=
    { toFun := fun σ => (Equiv.swap i j).trans σ
      invFun := fun σ => (Equiv.swap i j).trans σ
      left_inv := fun σ => Equiv.ext fun k => by simp [Equiv.swap_apply_self]
      right_inv := fun σ => Equiv.ext fun k => by simp [Equiv.swap_apply_self] }
  refine Fintype.sum_equiv E _ _ fun σ => ?_
  have hp : predSet ((Equiv.swap i j).trans σ) j =
      (predSet σ i).map (Equiv.swap i j).toEmbedding := by
    ext k
    rw [mem_map_equiv, Equiv.symm_swap]
    simp [predSet, Equiv.swap_apply_right]
  have hins : insert j ((predSet σ i).map (Equiv.swap i j).toEmbedding) =
      (insert i (predSet σ i)).map (Equiv.swap i j).toEmbedding := by
    rw [map_insert]; simp
  simp only [marginalContribution, E, Equiv.coe_fn_mk, hp]
  rw [hins, h.map_swap, h.map_swap]

/-- **Null player.** -/
theorem shapley_null {v : TUGame N} {i : N} (h : IsNullPlayer v i) : shapley v i = 0 := by
  have h' : ∀ S, v (insert i S) = v S := h
  simp only [shapley, marginalContribution, h', sub_self, sum_const_zero, zero_div]

/-- **Additivity.** -/
theorem shapley_add (v w : TUGame N) : shapley (v + w) = shapley v + shapley w := by
  funext i
  simp only [shapley, marginalContribution, Pi.add_apply, ← add_div, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun σ _ => by ring

theorem shapley_axioms : IsShapleyAxioms (shapley (N := N)) :=
  ⟨shapley_efficient, fun _ _ _ h => shapley_symmetric h, fun _ _ h => shapley_null h,
    shapley_add⟩

/-! ### Uniqueness -/

/-- The **unanimity game** of `T`: a coalition is worth `1` if it contains `T`. -/
def unanimity (T : Finset N) : TUGame N := fun S => if T ⊆ S then 1 else 0

/-- The **Möbius coefficients** (Harsanyi dividends) of `v`. -/
def dividend (v : TUGame N) (T : Finset N) : ℝ :=
  ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * v R

lemma sum_alternating {R S : Finset N} (hRS : R ⊆ S) :
    ∑ T ∈ S.powerset.filter (R ⊆ ·), (-1 : ℝ) ^ (T.card - R.card) = if R = S then 1 else 0 := by
  have e : ∑ T ∈ S.powerset.filter (R ⊆ ·), (-1 : ℝ) ^ (T.card - R.card) =
      ∑ U ∈ (S \ R).powerset, (-1 : ℝ) ^ U.card := by
    refine sum_nbij' (fun T => T \ R) (fun U => U ∪ R) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      simp only [mem_powerset]
      exact sdiff_subset_sdiff hT.1 le_rfl
    · intro U hU
      simp only [mem_powerset] at hU
      simp only [mem_filter, mem_powerset]
      exact ⟨union_subset (hU.trans sdiff_subset) hRS, subset_union_right⟩
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      exact sdiff_union_of_subset hT.2
    · intro U hU
      simp only [mem_powerset] at hU
      rw [union_sdiff_right]
      exact sdiff_eq_self_of_disjoint (disjoint_of_subset_left hU disjoint_sdiff_self_left)
    · intro T hT
      simp only [mem_filter, mem_powerset] at hT
      rw [card_sdiff_of_subset hT.2]
  rw [e]
  have := congrArg (fun z : ℤ => (z : ℝ)) (sum_powerset_neg_one_pow_card (x := S \ R))
  push_cast at this
  rw [this]
  have hiff : S \ R = ∅ ↔ R = S := by
    rw [sdiff_eq_empty_iff_subset]
    exact ⟨fun h => subset_antisymm hRS h, fun h => h ▸ subset_rfl⟩
  by_cases h : R = S
  · simp [h]
  · simp only [mt hiff.1 h, h, ↓reduceIte]

/-- **Every game is a combination of unanimity games** (Möbius inversion). -/
theorem game_eq_sum_unanimity (v : TUGame N) :
    v = ∑ T : Finset N, dividend v T • unanimity T := by
  funext S
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unanimity, mul_ite, mul_one,
    mul_zero]
  rw [← Finset.sum_filter]
  have hf : (univ.filter fun T : Finset N => T ⊆ S) = S.powerset := by ext; simp
  rw [hf]
  simp only [dividend]
  rw [Finset.sum_comm' (t' := S.powerset) (s' := fun R => S.powerset.filter (R ⊆ ·))]
  · simp only [← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun R hR => by rw [sum_alternating (mem_powerset.1 hR)]]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  · intro T R
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨hT, hR⟩; exact ⟨⟨hT, hR⟩, hR.trans hT⟩
    · rintro ⟨⟨hT, hR⟩, -⟩; exact ⟨hT, hR⟩

section Axioms

variable {φ : TUGame N → N → ℝ}

lemma IsShapleyAxioms.map_zero (hφ : IsShapleyAxioms φ) : φ 0 = 0 := by
  funext i
  have := congrFun (hφ.2.2.2 0 0) i
  simp only [add_zero, Pi.add_apply] at this
  simp only [Pi.zero_apply]
  linarith

lemma IsShapleyAxioms.map_sum (hφ : IsShapleyAxioms φ) {ι : Type*} (s : Finset ι)
    (g : ι → TUGame N) : φ (∑ k ∈ s, g k) = ∑ k ∈ s, φ (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hφ.map_zero
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hφ.2.2.2, ih]

/-- Any value satisfying the axioms is pinned down on scaled unanimity games:
`c / |T|` to each member of `T`, `0` to everybody else. -/
lemma IsShapleyAxioms.apply_unanimity (hφ : IsShapleyAxioms φ) (c : ℝ) (T : Finset N)
    (i : N) : φ (c • unanimity T) i = if i ∈ T then c / T.card else 0 := by
  -- Players outside `T` are null.
  have hnull : ∀ k ∉ T, φ (c • unanimity T) k = 0 := fun k hk => hφ.2.2.1 _ _ fun S => by
    simp only [Pi.smul_apply, unanimity, smul_eq_mul, subset_insert_iff_of_notMem hk]
  -- Members of `T` are symmetric.
  have hsym : ∀ k ∈ T, ∀ l ∈ T, φ (c • unanimity T) k = φ (c • unanimity T) l := by
    intro k hk l hl
    refine hφ.2.1 _ _ _ fun S hkS hlS => ?_
    rcases eq_or_ne k l with rfl | hkl
    · rfl
    have h1 : ¬ T ⊆ insert k S := fun h => by
      rcases mem_insert.1 (h hl) with h | h
      · exact hkl h.symm
      · exact hlS h
    have h2 : ¬ T ⊆ insert l S := fun h => by
      rcases mem_insert.1 (h hk) with h | h
      · exact hkl h
      · exact hkS h
    simp only [Pi.smul_apply, unanimity, smul_eq_mul, h1, h2, ↓reduceIte]
  by_cases hi : i ∈ T
  · simp only [hi, ↓reduceIte]
    have heff := hφ.1 (c • unanimity T)
    have hsum : ∑ k, φ (c • unanimity T) k = ∑ k, if k ∈ T then φ (c • unanimity T) i else 0 :=
      sum_congr rfl fun k _ => by
        by_cases hk : k ∈ T
        · simp only [hk, ↓reduceIte]; exact hsym k hk i hi
        · simp only [hk, ↓reduceIte]; exact hnull k hk
    rw [hsum, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul] at heff
    have hne : ¬ T ⊆ (∅ : Finset N) := fun h => by simpa using h hi
    simp only [Pi.smul_apply, unanimity, smul_eq_mul, subset_univ, ↓reduceIte, hne, mul_one,
      mul_zero, sub_zero] at heff
    have hT : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hi)
    rw [eq_div_iff hT]
    linarith
  · simp only [hi, ↓reduceIte]; exact hnull i hi

end Axioms

/-- **Uniqueness of the Shapley value** (Shapley 1953): any two values satisfying the four
axioms coincide. -/
theorem IsShapleyAxioms.unique {φ ψ : TUGame N → N → ℝ} (hφ : IsShapleyAxioms φ)
    (hψ : IsShapleyAxioms ψ) : φ = ψ := by
  funext v
  rw [game_eq_sum_unanimity v, hφ.map_sum, hψ.map_sum]
  refine sum_congr rfl fun T _ => funext fun i => ?_
  rw [hφ.apply_unanimity, hψ.apply_unanimity]

/-- **Shapley's theorem**: the Shapley value is the unique value that is efficient,
symmetric, additive and gives null players nothing. -/
theorem eq_shapley_of_axioms {φ : TUGame N → N → ℝ} (hφ : IsShapleyAxioms φ) :
    φ = shapley :=
  hφ.unique shapley_axioms

/-- Witness: in the three-player majority game (a coalition wins iff it has at least two
members) everybody gets `1/3`. -/
example (i : Fin 3) : shapley (fun S : Finset (Fin 3) => if 2 ≤ S.card then (1 : ℝ) else 0) i =
    1 / 3 := by
  have hsym : ∀ i j : Fin 3, shapley (fun S : Finset (Fin 3) => if 2 ≤ S.card then (1 : ℝ)
      else 0) i = shapley (fun S : Finset (Fin 3) => if 2 ≤ S.card then (1 : ℝ) else 0) j :=
    fun i j => shapley_symmetric fun S hi hj => by
      simp only [card_insert_of_notMem hi, card_insert_of_notMem hj]
  have heff := shapley_efficient (fun S : Finset (Fin 3) => if 2 ≤ S.card then (1 : ℝ) else 0)
  rw [Fin.sum_univ_three, ← hsym 0 1, ← hsym 0 2] at heff
  simp at heff
  rw [hsym i 0]
  linarith

end Econ
