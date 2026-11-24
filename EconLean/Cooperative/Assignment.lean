/-
# The assignment game (Shapley–Shubik 1971)

Shapley and Shubik (1971), *The assignment game I: The core*; Roth–Sotomayor, Ch. 8. There are finitely many buyers `B` and sellers `S`; a buyer–seller pair
`(b, s)` that trades creates surplus `a b s`. A coalition `T` of buyers and sellers (players
`B ⊕ S`) can earn the most valuable **matching** among its members: a set of pairs in which
every buyer and every seller appears at most once. This is the TU game `assignmentGame a`.

* `assignment_inCore_iff`: a payoff vector (buyers' payoffs `u_b`, sellers' payoffs `p_s`)
  is in the core iff it is nonnegative, every pair is covered (`u_b + p_s ≥ a b s`), and the
  total equals the value of an optimal assignment.
* `assignment_weak_duality`, `assignment_strong_duality`: every such dual-feasible vector pays
  at least the optimal assignment value, and the bound is attained; so, with the previous
  item, **the core is the set of optimal solutions of the dual linear program**.
* `assignment_isBalanced`: the assignment game is balanced. Given balanced weights, the
  weighted optimal matchings of the coalitions form a doubly substochastic buyer–seller matrix;
  embedded in a doubly stochastic matrix on `B ⊕ S`, the Birkhoff–von Neumann theorem writes it
  as a mixture of permutations, each of which induces a matching of everyone.
* `assignment_core_nonempty`: the core is nonempty (Shapley–Shubik 1971), by Bondareva–Shapley
  (the case with no players is handled directly).
* `shapley_shubik`: equivalently, there are nonnegative buyer and seller payoffs covering
  every pair whose total is the optimal assignment value.

No sign restriction on `a` is needed: a pair with negative surplus is simply never matched.
Not formalized: the lattice structure of the core and its buyer- and seller-optimal points;
the equality of the core with competitive-equilibrium price vectors; complementary slackness
(`u_b + p_s = a b s` on every optimal matching); the integrality of the assignment LP as a
stand-alone statement (it is used only inside the balancedness proof); the
Demange–Gale–Sotomayor auction.
-/
module

public import EconLean.Cooperative.Core
public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Data.Matrix.Block

@[expose] public section

namespace Econ

open Finset Matrix

variable {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]

/-- A set of buyer–seller pairs in which no buyer and no seller appears twice. -/
def IsPairMatching (M : Finset (B × S)) : Prop :=
  (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ ∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q

/-- `M` is a matching among the members of the coalition `T`. -/
def IsMatchingIn (T : Finset (B ⊕ S)) (M : Finset (B × S)) : Prop :=
  IsPairMatching M ∧ ∀ p ∈ M, Sum.inl p.1 ∈ T ∧ Sum.inr p.2 ∈ T

/-- Total surplus of a set of pairs. -/
def matchingValue (a : B → S → ℝ) (M : Finset (B × S)) : ℝ := ∑ p ∈ M, a p.1 p.2

omit [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] in
lemma isMatchingIn_empty (T : Finset (B ⊕ S)) : IsMatchingIn T (∅ : Finset (B × S)) :=
  ⟨⟨fun _ h => absurd h (notMem_empty _), fun _ h => absurd h (notMem_empty _)⟩,
    fun _ h => absurd h (notMem_empty _)⟩

open Classical in
/-- The **assignment game**: a coalition earns the value of its best internal matching. -/
noncomputable def assignmentGame (a : B → S → ℝ) : TUGame (B ⊕ S) := fun T =>
  ((univ : Finset (Finset (B × S))).filter (IsMatchingIn T)).sup'
    ⟨∅, mem_filter.2 ⟨mem_univ _, isMatchingIn_empty T⟩⟩ (matchingValue a)

omit [DecidableEq B] [DecidableEq S] in
lemma le_assignmentGame (a : B → S → ℝ) {T : Finset (B ⊕ S)} {M : Finset (B × S)}
    (hM : IsMatchingIn T M) : matchingValue a M ≤ assignmentGame a T := by
  classical
  exact le_sup' (matchingValue a) (mem_filter.2 ⟨mem_univ _, hM⟩)

omit [DecidableEq B] [DecidableEq S] in
lemma exists_optimal_matching (a : B → S → ℝ) (T : Finset (B ⊕ S)) :
    ∃ M, IsMatchingIn T M ∧ assignmentGame a T = matchingValue a M := by
  classical
  obtain ⟨M, hM, he⟩ := exists_mem_eq_sup' (⟨∅, mem_filter.2 ⟨mem_univ _, isMatchingIn_empty T⟩⟩ :
    ((univ : Finset (Finset (B × S))).filter (IsMatchingIn T)).Nonempty) (matchingValue a)
  refine ⟨M, (mem_filter.1 hM).2, ?_⟩
  unfold assignmentGame
  convert he

omit [Fintype B] [Fintype S] in
/-- A matching in `T` pays its pairs at most what the members of `T` receive, when payoffs
are nonnegative. -/
lemma matching_sum_le {T : Finset (B ⊕ S)} {M : Finset (B × S)} (hM : IsMatchingIn T M)
    {x : B ⊕ S → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∑ p ∈ M, (x (Sum.inl p.1) + x (Sum.inr p.2)) ≤ ∑ i ∈ T, x i := by
  rw [sum_add_distrib]
  have h1 : ∑ p ∈ M, x (Sum.inl p.1) = ∑ i ∈ M.image (fun p => (Sum.inl p.1 : B ⊕ S)), x i :=
    (sum_image fun p hp q hq h => hM.1.1 p hp q hq (Sum.inl_injective h)).symm
  have h2 : ∑ p ∈ M, x (Sum.inr p.2) = ∑ i ∈ M.image (fun p => (Sum.inr p.2 : B ⊕ S)), x i :=
    (sum_image fun p hp q hq h => hM.1.2 p hp q hq (Sum.inr_injective h)).symm
  have hdisj : Disjoint (M.image fun p => (Sum.inl p.1 : B ⊕ S))
      (M.image fun p => (Sum.inr p.2 : B ⊕ S)) := by
    rw [disjoint_left]
    intro i hi hi'
    obtain ⟨p, _, rfl⟩ := mem_image.1 hi
    obtain ⟨q, _, hq⟩ := mem_image.1 hi'
    exact Sum.inr_ne_inl hq
  rw [h1, h2, ← sum_union hdisj]
  refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => hx i
  rcases mem_union.1 hi with h | h
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 h; exact (hM.2 p hp).1
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 h; exact (hM.2 p hp).2

omit [DecidableEq B] [DecidableEq S] in
/-- A single player's coalition has worth zero. -/
lemma assignmentGame_singleton (a : B → S → ℝ) (i : B ⊕ S) : assignmentGame a {i} = 0 := by
  obtain ⟨M, hM, he⟩ := exists_optimal_matching a {i}
  have hempty : M = ∅ := by
    refine eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨h1, h2⟩ := hM.2 p hp
    rw [mem_singleton] at h1 h2
    exact Sum.inl_ne_inr (h1.trans h2.symm)
  rw [he, hempty, matchingValue, sum_empty]

/-- **Core characterization** (Shapley–Shubik 1971): the core consists of the nonnegative
payoff vectors that cover every pair and distribute exactly the optimal assignment value.
Together with `assignment_strong_duality`, these are the optimal dual solutions. -/
theorem assignment_inCore_iff (a : B → S → ℝ) (x : B ⊕ S → ℝ) :
    IsInCore (assignmentGame a) x ↔
      (∀ i, 0 ≤ x i) ∧ (∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) ∧
        ∑ i, x i = assignmentGame a univ := by
  constructor
  · rintro ⟨hsum, hcore⟩
    refine ⟨fun i => ?_, fun b s => ?_, hsum⟩
    · have := hcore {i}
      rwa [assignmentGame_singleton, sum_singleton] at this
    · have hpair : IsMatchingIn {Sum.inl b, Sum.inr s} {(b, s)} :=
        ⟨⟨fun p hp q hq _ => by rw [mem_singleton] at hp hq; rw [hp, hq],
          fun p hp q hq _ => by rw [mem_singleton] at hp hq; rw [hp, hq]⟩,
          fun p hp => by rw [mem_singleton] at hp; subst hp; simp⟩
      have h1 := le_assignmentGame a hpair
      have h2 := hcore {Sum.inl b, Sum.inr s}
      rw [sum_pair Sum.inl_ne_inr] at h2
      simp only [matchingValue, sum_singleton] at h1
      linarith
  · rintro ⟨hx, hpair, hsum⟩
    refine ⟨hsum, fun T => ?_⟩
    obtain ⟨M, hM, he⟩ := exists_optimal_matching a T
    rw [he, matchingValue]
    exact (sum_le_sum fun p _ => hpair p.1 p.2).trans (matching_sum_le hM hx)

/-- The buyer–seller block of the embedding matrix is read by this linear functional. -/
def assignLin (a : B → S → ℝ) (M : Matrix (B ⊕ S) (B ⊕ S) ℝ) : ℝ :=
  ∑ b, ∑ s, a b s * M (Sum.inl b) (Sum.inr s)

omit [DecidableEq B] [DecidableEq S] in
lemma assignLin_convexOn (a : B → S → ℝ) : ConvexOn ℝ Set.univ (assignLin a) := by
  refine ⟨convex_univ, fun M _ N _ α β _ _ _ => le_of_eq ?_⟩
  simp only [assignLin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun b _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun s _ => by ring

/-- A permutation of all players induces a matching of everyone, so its matrix is worth at
most the grand coalition. -/
lemma assignLin_perm_le (a : B → S → ℝ) (σ : Equiv.Perm (B ⊕ S)) :
    assignLin a (σ.permMatrix ℝ) ≤ assignmentGame a univ := by
  classical
  set M : Finset (B × S) := univ.filter fun p => σ (Sum.inl p.1) = Sum.inr p.2
  have hM : IsMatchingIn univ M := by
    refine ⟨⟨fun p hp q hq h => ?_, fun p hp q hq h => ?_⟩, fun _ _ => ⟨mem_univ _, mem_univ _⟩⟩
    · have e1 := (mem_filter.1 hp).2; have e2 := (mem_filter.1 hq).2
      rw [h] at e1
      exact Prod.ext h (Sum.inr_injective (e1.symm.trans e2))
    · have e1 := (mem_filter.1 hp).2; have e2 := (mem_filter.1 hq).2
      rw [h] at e1
      exact Prod.ext (Sum.inl_injective (σ.injective (e1.trans e2.symm))) h
  refine le_of_eq_of_le ?_ (le_assignmentGame a hM)
  simp only [assignLin, matchingValue, M, sum_filter, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, mul_ite, mul_one, mul_zero]
  rw [← Fintype.sum_prod_type']

/-- **The assignment game is balanced.** -/
theorem assignment_isBalanced (a : B → S → ℝ) : IsBalanced (assignmentGame a) := by
  classical
  intro w ⟨hw0, hw1⟩
  choose opt hopt hval using exists_optimal_matching a
  -- weighted frequency with which `(b, s)` is matched
  set X : Matrix B S ℝ := fun b s => ∑ T, w T * if (b, s) ∈ opt T then 1 else 0
  have hX0 : ∀ b s, 0 ≤ X b s := fun b s =>
    sum_nonneg fun T _ => mul_nonneg (hw0 T) (by split_ifs <;> norm_num)
  -- a buyer is matched at most once in each coalition she belongs to
  have hcountB : ∀ T b, ∑ s, (if (b, s) ∈ opt T then (1 : ℝ) else 0) ≤
      if Sum.inl b ∈ T then 1 else 0 := by
    intro T b
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    by_cases hb : ∃ s, (b, s) ∈ opt T
    · obtain ⟨s, hs⟩ := hb
      simp only [((hopt T).2 _ hs).1, ↓reduceIte]
      have : (univ.filter fun s' => (b, s') ∈ opt T) ⊆ {s} := fun s' hs' => by
        have := (hopt T).1.1 _ (mem_filter.1 hs').2 _ hs rfl
        rw [mem_singleton]; exact (Prod.ext_iff.1 this).2
      exact_mod_cast (card_le_card this).trans (card_singleton s).le
    · push Not at hb
      rw [filter_false_of_mem fun s _ => hb s, card_empty, Nat.cast_zero]
      split_ifs <;> norm_num
  have hcountS : ∀ T s, ∑ b, (if (b, s) ∈ opt T then (1 : ℝ) else 0) ≤
      if Sum.inr s ∈ T then 1 else 0 := by
    intro T s
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    by_cases hs : ∃ b, (b, s) ∈ opt T
    · obtain ⟨b, hb⟩ := hs
      simp only [((hopt T).2 _ hb).2, ↓reduceIte]
      have : (univ.filter fun b' => (b', s) ∈ opt T) ⊆ {b} := fun b' hb' => by
        have := (hopt T).1.2 _ (mem_filter.1 hb').2 _ hb rfl
        rw [mem_singleton]; exact (Prod.ext_iff.1 this).1
      exact_mod_cast (card_le_card this).trans (card_singleton b).le
    · push Not at hs
      rw [filter_false_of_mem fun b _ => hs b, card_empty, Nat.cast_zero]
      split_ifs <;> norm_num
  have hweight : ∀ i, ∑ T, w T * (if i ∈ T then (1 : ℝ) else 0) = 1 := fun i => by
    calc ∑ T, w T * (if i ∈ T then (1 : ℝ) else 0) = ∑ T ∈ univ.filter (fun T => i ∈ T), w T := by
          rw [sum_filter]; exact sum_congr rfl fun T _ => by split_ifs <;> ring
      _ = 1 := hw1 i
  have hrow : ∀ b, ∑ s, X b s ≤ 1 := fun b => by
    calc ∑ s, X b s = ∑ T, w T * ∑ s, (if (b, s) ∈ opt T then (1 : ℝ) else 0) := by
          simp only [X, mul_sum]; exact sum_comm
      _ ≤ ∑ T, w T * (if Sum.inl b ∈ T then (1 : ℝ) else 0) :=
          sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hcountB T b) (hw0 T)
      _ = 1 := hweight _
  have hcol : ∀ s, ∑ b, X b s ≤ 1 := fun s => by
    calc ∑ b, X b s = ∑ T, w T * ∑ b, (if (b, s) ∈ opt T then (1 : ℝ) else 0) := by
          simp only [X, mul_sum]; exact sum_comm
      _ ≤ ∑ T, w T * (if Sum.inr s ∈ T then (1 : ℝ) else 0) :=
          sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (hcountS T s) (hw0 T)
      _ = 1 := hweight _
  -- embed in a doubly stochastic matrix on all players
  set D : Matrix (B ⊕ S) (B ⊕ S) ℝ := fromBlocks (diagonal fun b => 1 - ∑ s, X b s) X Xᵀ
    (diagonal fun s => 1 - ∑ b, X b s)
  have hD : D ∈ doublyStochastic ℝ (B ⊕ S) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · rcases i with b | s <;> rcases j with b' | s'
      · simp only [D, fromBlocks_apply₁₁, diagonal_apply]; split_ifs <;> linarith [hrow b]
      · exact hX0 b s'
      · exact hX0 b' s
      · simp only [D, fromBlocks_apply₂₂, diagonal_apply]; split_ifs <;> linarith [hcol s]
    · rcases i with b | s
      · simp only [D, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
          diagonal_apply, sum_ite_eq, mem_univ, ↓reduceIte]
        ring
      · simp only [D, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
          diagonal_apply, sum_ite_eq, mem_univ, ↓reduceIte, transpose_apply]
        ring
    · rcases j with b | s
      · simp only [D, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₁,
          diagonal_apply, sum_ite_eq', mem_univ, ↓reduceIte, transpose_apply]
        ring
      · simp only [D, Fintype.sum_sum_type, fromBlocks_apply₁₂, fromBlocks_apply₂₂,
          diagonal_apply, sum_ite_eq', mem_univ, ↓reduceIte]
        ring
  rw [← SetLike.mem_coe, doublyStochastic_eq_convexHull_permMatrix] at hD
  obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ :=
    (assignLin_convexOn a).exists_ge_of_mem_convexHull (Set.subset_univ _) hD
  refine le_trans (le_of_eq ?_) (hσ.trans (assignLin_perm_le a σ))
  -- `∑_T w_T v(T) = ∑_{b,s} a b s X b s`
  have e : ∀ T, w T * assignmentGame a T =
      ∑ b, ∑ s, a b s * (w T * if (b, s) ∈ opt T then 1 else 0) := by
    intro T
    rw [hval T, matchingValue, ← univ_inter (opt T), ← sum_ite_mem, Fintype.sum_prod_type,
      mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun s _ => ?_
    by_cases h : (b, s) ∈ opt T <;> simp [h, mul_comm]
  have hD12 : ∀ b s, D (Sum.inl b) (Sum.inr s) = X b s := fun _ _ => rfl
  show _ = ∑ b, ∑ s, a b s * D (Sum.inl b) (Sum.inr s)
  simp only [hD12, X]
  rw [sum_congr rfl fun T _ => e T, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_sum]

/-- **Weak duality**: a nonnegative payoff vector covering every pair pays in total at least the
value of an optimal assignment. -/
theorem assignment_weak_duality (a : B → S → ℝ) {x : B ⊕ S → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hcov : ∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) :
    assignmentGame a univ ≤ ∑ i, x i := by
  obtain ⟨M, hM, he⟩ := exists_optimal_matching a univ
  rw [he, matchingValue]
  exact (sum_le_sum fun p _ => hcov p.1 p.2).trans (matching_sum_le hM hx)

omit [DecidableEq B] [DecidableEq S] in
lemma assignmentGame_nonneg (a : B → S → ℝ) (T : Finset (B ⊕ S)) : 0 ≤ assignmentGame a T := by
  have := le_assignmentGame a (isMatchingIn_empty (B := B) (S := S) T)
  rwa [matchingValue, sum_empty] at this

/-- **The core of the assignment game is nonempty** (Shapley–Shubik 1971). -/
theorem assignment_core_nonempty (a : B → S → ℝ) : ∃ x, IsInCore (assignmentGame a) x := by
  rcases isEmpty_or_nonempty (B ⊕ S) with h | h
  · refine ⟨0, (assignment_inCore_iff a 0).2 ⟨fun _ => le_rfl, fun b => isEmptyElim (Sum.inl b : B ⊕ S),
      le_antisymm ?_ (assignment_weak_duality a (fun _ => le_rfl) fun b => isEmptyElim (Sum.inl b : B ⊕ S))⟩⟩
    simp only [Pi.zero_apply, sum_const_zero]
    exact assignmentGame_nonneg a univ
  · exact (bondareva_shapley _).2 (assignment_isBalanced a)

/-- **Shapley–Shubik (1971)**: there are nonnegative payoffs for buyers and sellers that cover
every pair's surplus and add up to the value of an optimal assignment. -/
theorem shapley_shubik (a : B → S → ℝ) :
    ∃ u : B → ℝ, ∃ p : S → ℝ, (∀ b, 0 ≤ u b) ∧ (∀ s, 0 ≤ p s) ∧ (∀ b s, a b s ≤ u b + p s) ∧
      ∑ b, u b + ∑ s, p s = assignmentGame a univ := by
  obtain ⟨x, hx⟩ := assignment_core_nonempty a
  obtain ⟨h0, hcov, hsum⟩ := (assignment_inCore_iff a x).1 hx
  exact ⟨fun b => x (Sum.inl b), fun s => x (Sum.inr s), fun b => h0 _, fun s => h0 _, hcov,
    by rw [← hsum, Fintype.sum_sum_type]⟩

/-- **Strong duality for the assignment LP** (Shapley–Shubik 1971): the minimum total payoff
over nonnegative pair-covering vectors equals the value of an optimal assignment. -/
theorem assignment_strong_duality (a : B → S → ℝ) :
    (∀ x : B ⊕ S → ℝ, (∀ i, 0 ≤ x i) → (∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) →
      assignmentGame a univ ≤ ∑ i, x i) ∧
    ∃ x : B ⊕ S → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ b s, a b s ≤ x (Sum.inl b) + x (Sum.inr s)) ∧
      ∑ i, x i = assignmentGame a univ := by
  refine ⟨fun x hx hcov => assignment_weak_duality a hx hcov, ?_⟩
  obtain ⟨x, hx⟩ := assignment_core_nonempty a
  exact ⟨x, (assignment_inCore_iff a x).1 hx⟩

end Econ
