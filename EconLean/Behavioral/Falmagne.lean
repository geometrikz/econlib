/-
# Falmagne's theorem: nonnegative Block–Marschak polynomials characterize RUMs

References.
* J.-C. Falmagne (1978), "A Representation Theorem for Finite Random Scale
  Systems", *J. Math. Psych.* 18(1).
* S. Fiorini (2004), "A Short Proof of a Theorem of Falmagne",
  *J. Math. Psych.* 48(1) (the flow argument used here).

**Theorem.** A stochastic choice rule `P` on a finite set `X` is a random
utility model iff all its Block–Marschak polynomials are nonnegative. The
"only if" half is `bm_rumP_nonneg` (`StochasticChoice.lean`); this file
proves the converse (`falmagne`) and packages both (`isRUM_iff_bm_nonneg`).

**Proof (Fiorini's flow, as a Markov chain).** Think of a ranking as built
top-down: after the set `B` of the best alternatives has been placed, the
next one is `x ∉ B`. Put `q(B, x) = bm P (X ∖ B) x ≥ 0` on that step: for a
RUM it is the probability that the alternatives above `x` are exactly `B`.
Write `T(B) = Σ_{x ∉ B} q(B, x)`.

1. *Flow conservation* (`sum_q_in`): for `∅ ≠ B ≠ X`,
   `Σ_{b ∈ B} q(B ∖ b, b) = T(B)` (inflow = outflow), and `T(∅) = 1`.
   This is an inclusion–exclusion computation using that `P` is a choice
   rule (`sum_bm_menu`).
2. *The chain*: from `B` move to `B ∪ {x}` with probability `q(B, x)/T(B)`.
   The probability `μ(r)` of a ranking is the product along it. Sums over
   orderings of a set decompose by the first element (`sum_ords`), so all
   the needed probabilities satisfy one-step recursions.
3. *Reaching `B`* has probability `T(B)` (`reach_eq_T`), by induction on
   `|B|` using the Markov property (`hit_eq`) and a last-step decomposition
   (`reach_eq_sum_hit`). Hence `Pr(the set above x is exactly B) = q(B, x)`,
   i.e. the RUM's BM polynomials equal those of `P`.
4. *Möbius inversion* (`sum_bm`): `P A a = Σ_{A ⊆ B} bm P B a`, so equal BM
   polynomials give equal choice probabilities.
-/
module

public import EconLean.Behavioral.StochasticChoice
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

namespace Econ

namespace StochasticChoice

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Möbius inversion and flow conservation for BM polynomials -/

omit [Fintype X] in
/-- Reindexing pairs `C ⊆ S`, `D ⊆ S ∖ C` by `E = C ∪ D ⊆ S`, `D ⊆ E`. -/
theorem sum_powerset_disjoint (S : Finset X) (g : Finset X → Finset X → ℝ) :
    ∑ C ∈ S.powerset, ∑ D ∈ (S \ C).powerset, g C D =
      ∑ E ∈ S.powerset, ∑ D ∈ E.powerset, g (E \ D) D := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun p _ => ⟨p.1 ∪ p.2, p.2⟩) (fun p _ => ⟨p.1 \ p.2, p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨C, D⟩ h
    simp only [mem_sigma, mem_powerset] at h ⊢
    exact ⟨union_subset h.1 (h.2.trans sdiff_subset), subset_union_right⟩
  · rintro ⟨E, D⟩ h
    simp only [mem_sigma, mem_powerset] at h ⊢
    refine ⟨sdiff_subset.trans h.1, fun x hx => ?_⟩
    rw [mem_sdiff]
    exact ⟨h.1 (h.2 hx), fun h' => (mem_sdiff.1 h').2 hx⟩
  · rintro ⟨C, D⟩ h
    simp only [mem_sigma, mem_powerset] at h
    have hd : Disjoint C D := by
      rw [disjoint_left]; intro x hC hD; exact (mem_sdiff.1 (h.2 hD)).2 hC
    simp [union_sdiff_cancel_right hd]
  · rintro ⟨E, D⟩ h
    simp only [mem_sigma, mem_powerset] at h
    simp [sdiff_union_of_subset h.2]
  · rintro ⟨C, D⟩ h
    simp only [mem_sigma, mem_powerset] at h
    have hd : Disjoint C D := by
      rw [disjoint_left]; intro x hC hD; exact (mem_sdiff.1 (h.2 hD)).2 hC
    simp [union_sdiff_cancel_right hd]

omit [Fintype X] in
theorem sum_neg_one_pow (E : Finset X) :
    ∑ D ∈ E.powerset, (-1 : ℝ) ^ D.card = if E = ∅ then 1 else 0 := by
  have := Finset.sum_powerset_neg_one_pow_card (x := E)
  split_ifs at this ⊢ <;> exact_mod_cast this

/-- **Möbius inversion**: choice probabilities are sums of BM polynomials over
supersets, `P A a = Σ_{A ⊆ B} bm P B a`. Holds for any function `P`. -/
theorem sum_bm (P : Finset X → X → ℝ) (A : Finset X) (a : X) :
    ∑ C ∈ (univ \ A).powerset, bm P (A ∪ C) a = P A a := by
  unfold bm
  have h : ∀ C ∈ (univ \ A).powerset, univ \ (A ∪ C) = (univ \ A) \ C := by
    intro C _; ext x; simp [not_or]
  rw [sum_congr rfl fun C hC => by rw [h C hC]]
  rw [sum_powerset_disjoint (univ \ A) fun C D => (-1 : ℝ) ^ D.card * P (A ∪ C ∪ D) a]
  have h2 : ∀ E ∈ (univ \ A).powerset, ∑ D ∈ E.powerset, (-1 : ℝ) ^ D.card * P (A ∪ (E \ D) ∪ D) a
      = (if E = ∅ then 1 else 0) * P (A ∪ E) a := by
    intro E _
    rw [← sum_neg_one_pow, sum_mul]
    refine sum_congr rfl fun D hD => ?_
    rw [union_assoc, sdiff_union_of_subset (mem_powerset.1 hD)]
  rw [sum_congr rfl h2]
  simp

omit [Fintype X] in
/-- Reindexing pairs `c ∈ C ⊆ S` by `c ∈ S` and `C ∖ c ⊆ S ∖ c`. -/
theorem sum_powerset_mem (S : Finset X) (g : Finset X → X → ℝ) :
    ∑ C ∈ S.powerset, ∑ c ∈ C, g C c = ∑ c ∈ S, ∑ C ∈ (S.erase c).powerset, g (insert c C) c := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun p _ => ⟨p.2, p.1.erase p.2⟩) (fun p _ => ⟨insert p.1 p.2, p.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨C, c⟩ h
    simp only [mem_sigma, mem_powerset] at h ⊢
    exact ⟨h.1 h.2, erase_subset_erase c h.1⟩
  · rintro ⟨c, C⟩ h
    simp only [mem_sigma, mem_powerset] at h ⊢
    exact ⟨insert_subset h.1 (h.2.trans (erase_subset _ _)), mem_insert_self _ _⟩
  · rintro ⟨C, c⟩ h
    simp only [mem_sigma] at h
    simp [insert_erase h.2]
  · rintro ⟨c, C⟩ h
    simp only [mem_sigma, mem_powerset] at h
    have : c ∉ C := fun hc => (mem_erase.1 (h.2 hc)).1 rfl
    simp [erase_insert this]
  · rintro ⟨C, c⟩ h
    simp only [mem_sigma] at h
    simp [insert_erase h.2]

/-- **Flow conservation for BM polynomials.** For a choice rule and a menu
`A` with `∅ ≠ A ≠ X`:
`Σ_{x ∈ A} bm P A x = Σ_{b ∉ A} bm P (A ∪ {b}) b`. -/
theorem sum_bm_menu {P : Finset X → X → ℝ} (hP : IsChoiceRule P) {A : Finset X}
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) :
    ∑ x ∈ A, bm P A x = ∑ b ∈ univ \ A, bm P (insert b A) b := by
  set S := univ \ A
  unfold bm
  rw [sum_comm]
  -- inner sums over `A` of a menu's choice probabilities
  have hin : ∀ C ∈ S.powerset, ∑ x ∈ A, (-1 : ℝ) ^ C.card * P (A ∪ C) x =
      (-1 : ℝ) ^ C.card - ∑ c ∈ C, (-1 : ℝ) ^ C.card * P (A ∪ C) c := by
    intro C hC
    have hd : Disjoint A C := by
      rw [disjoint_left]; intro x hx hxC; exact (mem_sdiff.1 (mem_powerset.1 hC hxC)).2 hx
    have h1 := (hP (A ∪ C) (hA.mono subset_union_left)).2.2
    rw [sum_union hd] at h1
    rw [← mul_sum, ← mul_sum]
    linear_combination ((-1 : ℝ) ^ C.card) * h1
  rw [sum_congr rfl hin, sum_sub_distrib, sum_neg_one_pow, ite_eq_right hAc.ne_empty, zero_sub,
    sum_powerset_mem S fun C c => (-1 : ℝ) ^ C.card * P (A ∪ C) c, ← sum_neg_distrib]
  refine sum_congr rfl fun b hb => ?_
  have hS : univ \ insert b A = S.erase b := sdiff_insert _ _ _
  rw [hS, ← sum_neg_distrib]
  refine sum_congr rfl fun C hC => ?_
  have hbC : b ∉ C := fun h => (mem_erase.1 (mem_powerset.1 hC h)).1 rfl
  rw [card_insert_of_notMem hbC, pow_succ, union_insert, insert_union]
  ring

/-! ### Orderings of a finite set -/

namespace Falmagne

/-- The orderings (nodup lists) of a finite set. -/
def ords (S : Finset X) : Finset (List X) := ⟨Multiset.lists S.val, Multiset.lists_nodup_finset S⟩

omit [Fintype X] in
theorem mem_ords {S : Finset X} {l : List X} : l ∈ ords S ↔ l.Nodup ∧ l.toFinset = S := by
  change l ∈ Multiset.lists S.val ↔ _
  rw [Multiset.mem_lists_iff]
  change S.val = (l : Multiset X) ↔ _
  constructor
  · intro h
    have hnd : l.Nodup := by rw [← Multiset.coe_nodup, ← h]; exact S.nodup
    refine ⟨hnd, ?_⟩
    ext x
    rw [List.mem_toFinset, ← Multiset.mem_coe, ← h, Finset.mem_val]
  · rintro ⟨hnd, ht⟩
    refine (Multiset.Nodup.ext S.nodup (Multiset.coe_nodup.2 hnd)).2 fun x => ?_
    rw [Finset.mem_val, Multiset.mem_coe, ← List.mem_toFinset, ht]

omit [Fintype X] in
theorem sum_ords_empty (f : List X → ℝ) : ∑ l ∈ ords (∅ : Finset X), f l = f [] := by
  have : ords (∅ : Finset X) = {[]} := by
    ext l
    rw [mem_ords, mem_singleton, List.toFinset_eq_empty_iff]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ List.nodup_nil, h⟩⟩
  rw [this, sum_singleton]

omit [Fintype X] in
/-- **Decomposition by the first element.** -/
theorem sum_ords {S : Finset X} (hS : S.Nonempty) (f : List X → ℝ) :
    ∑ l ∈ ords S, f l = ∑ a ∈ S, ∑ l ∈ ords (S.erase a), f (a :: l) := by
  rw [sum_sigma']
  symm
  refine sum_bij (fun p _ => p.1 :: p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨a, l⟩ h
    simp only [mem_sigma, mem_ords] at h ⊢
    obtain ⟨ha, hnd, ht⟩ := h
    have hal : a ∉ l := by
      rw [← List.mem_toFinset, ht]; simp
    refine ⟨List.nodup_cons.2 ⟨hal, hnd⟩, ?_⟩
    rw [List.toFinset_cons, ht, insert_erase ha]
  · rintro ⟨a, l⟩ _ ⟨a', l'⟩ _ h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro l hl
    rw [mem_ords] at hl
    obtain ⟨hnd, ht⟩ := hl
    cases l with
    | nil => simp at ht; exact absurd ht.symm hS.ne_empty
    | cons a l =>
      refine ⟨⟨a, l⟩, ?_, rfl⟩
      rw [List.nodup_cons] at hnd
      simp only [mem_sigma, mem_ords]
      refine ⟨by rw [← ht]; simp, hnd.2, ?_⟩
      rw [← ht, List.toFinset_cons, erase_insert (by simpa using hnd.1)]

/-- One-step decomposition of a sum over the orderings of the complement of
`C`. -/
theorem sum_ords_compl {C : Finset X} (hC : C ≠ univ) (f : List X → ℝ) :
    ∑ l ∈ ords (univ \ C), f l = ∑ x ∈ univ \ C, ∑ l ∈ ords (univ \ insert x C), f (x :: l) := by
  have hne : (univ \ C).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
    exact fun h => hC (eq_univ_of_forall fun x => h (mem_univ x))
  rw [sum_ords hne]
  refine sum_congr rfl fun x _ => ?_
  rw [sdiff_insert]

/-! ### The Markov chain -/

section Chain

variable (q : Finset X → X → ℝ)

/-- Total outflow from `C`. -/
noncomputable def T (C : Finset X) : ℝ := ∑ x ∈ univ \ C, q C x

/-- Transition probability from `C` to `C ∪ {x}`. -/
noncomputable def w (C : Finset X) (x : X) : ℝ := q C x / T q C

/-- Probability of following a list of steps starting from `C`. -/
noncomputable def W : Finset X → List X → ℝ
  | _, [] => 1
  | C, x :: l => w q C x * W (insert x C) l

/-- Total probability of all completions from `C`. -/
noncomputable def G (C : Finset X) : ℝ := ∑ l ∈ ords (univ \ C), W q C l

/-- The walk from `C` along `l` passes through the set `D`. -/
def reach (D : Finset X) : Finset X → List X → Bool
  | C, [] => decide (C = D)
  | C, x :: l => decide (C = D) || reach D (insert x C) l

/-- The walk from `C` along `l` passes through `D` and then adds `b`. -/
def hit (D : Finset X) (b : X) : Finset X → List X → Bool
  | _, [] => false
  | C, x :: l => (decide (C = D) && decide (x = b)) || hit D b (insert x C) l

/-- Probability of reaching `D` from `C`. -/
noncomputable def R (D C : Finset X) : ℝ :=
  ∑ l ∈ ords (univ \ C), W q C l * if reach D C l then 1 else 0

/-- Probability of reaching `D` from `C` and then adding `b`. -/
noncomputable def H (D : Finset X) (b : X) (C : Finset X) : ℝ :=
  ∑ l ∈ ords (univ \ C), W q C l * if hit D b C l then 1 else 0

omit [Fintype X] in
theorem reach_sub {D : Finset X} : ∀ {C : Finset X} {l : List X}, reach D C l → C ⊆ D
  | C, [], h => by simp [reach] at h; exact h.le
  | C, x :: l, h => by
    simp only [reach, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact h.le
    · exact (subset_insert x C).trans (reach_sub h)

omit [Fintype X] in
theorem hit_sub {D : Finset X} {b : X} : ∀ {C : Finset X} {l : List X}, hit D b C l → C ⊆ D
  | C, [], h => by simp [hit] at h
  | C, x :: l, h => by
    simp only [hit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact h.1.le
    · exact (subset_insert x C).trans (hit_sub h)

theorem G_univ : G q univ = 1 := by
  simp [G, sdiff_self, sum_ords_empty, W]

theorem G_step {C : Finset X} (hC : C ≠ univ) :
    G q C = ∑ x ∈ univ \ C, w q C x * G q (insert x C) := by
  unfold G
  rw [sum_ords_compl hC]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  rfl

theorem R_step {D C : Finset X} (hC : C ≠ univ) (hCD : C ≠ D) :
    R q D C = ∑ x ∈ univ \ C, w q C x * R q D (insert x C) := by
  unfold R
  rw [sum_ords_compl hC]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [W, reach, hCD, decide_false, Bool.false_or]
  ring

theorem R_self (D : Finset X) : R q D D = G q D := by
  unfold R G
  refine sum_congr rfl fun l _ => ?_
  cases l with
  | nil => simp [reach]
  | cons x l => simp [reach]

theorem R_univ {D : Finset X} (hD : D ≠ univ) : R q D univ = 0 := by
  simp [R, sdiff_self, sum_ords_empty, reach, Ne.symm hD]

theorem H_univ (D : Finset X) (b : X) : H q D b univ = 0 := by
  simp [H, sdiff_self, sum_ords_empty, hit]

theorem H_step {D C : Finset X} {b : X} (hC : C ≠ univ) (hCD : C ≠ D) :
    H q D b C = ∑ x ∈ univ \ C, w q C x * H q D b (insert x C) := by
  unfold H
  rw [sum_ords_compl hC]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [W, hit, hCD, decide_false, Bool.false_and, Bool.false_or]
  ring

theorem H_self {D : Finset X} {b : X} (hD : D ≠ univ) (hb : b ∉ D) :
    H q D b D = w q D b * G q (insert b D) := by
  unfold H
  rw [sum_ords_compl hD]
  rw [sum_eq_single_of_mem b (by simpa using hb)]
  · rw [G, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    have : hit D b (insert b D) l = false := by
      by_contra h
      have := hit_sub (Bool.not_eq_false _ ▸ h)
      exact hb (this (mem_insert_self b D))
    simp [W, hit, this]
  · intro x hx hxb
    refine sum_eq_zero fun l _ => ?_
    have : hit D b (insert x D) l = false := by
      by_contra h
      have := hit_sub (Bool.not_eq_false _ ▸ h)
      exact (mem_sdiff.1 hx).2 (this (mem_insert_self x D))
    simp [W, hit, hxb, this]

theorem H_eq_zero {D C : Finset X} {b : X} (h : ¬ C ⊆ D) : H q D b C = 0 :=
  sum_eq_zero fun l _ => by
    have : hit D b C l = false := by
      by_contra h'; exact h (hit_sub (Bool.not_eq_false _ ▸ h'))
    simp [this]

theorem R_eq_zero {D C : Finset X} (h : ¬ C ⊆ D) : R q D C = 0 :=
  sum_eq_zero fun l _ => by
    have : reach D C l = false := by
      by_contra h'; exact h (reach_sub (Bool.not_eq_false _ ▸ h'))
    simp [this]

end Chain

/-! ### The flow from a choice rule -/

section Flow

variable {P : Finset X → X → ℝ}

/-- The flow out of the upper set `B` to `x`: `bm P (X ∖ B) x` for `x ∉ B`. -/
noncomputable def flow (P : Finset X → X → ℝ) (B : Finset X) (x : X) : ℝ :=
  if x ∈ B then 0 else bm P (univ \ B) x

variable (hbm : ∀ A a, a ∈ A → 0 ≤ bm P A a)
include hbm

theorem flow_nonneg (B : Finset X) (x : X) : 0 ≤ flow P B x := by
  unfold flow; split_ifs with h
  · exact le_rfl
  · exact hbm _ _ (by simpa using h)

theorem T_nonneg (B : Finset X) : 0 ≤ T (flow P) B :=
  sum_nonneg fun x _ => flow_nonneg hbm B x

theorem flow_le_T {B : Finset X} {x : X} (hx : x ∉ B) : flow P B x ≤ T (flow P) B :=
  single_le_sum (f := flow P B) (fun y _ => flow_nonneg hbm B y) (by simpa using hx)

theorem w_nonneg (B : Finset X) (x : X) : 0 ≤ w (flow P) B x :=
  div_nonneg (flow_nonneg hbm B x) (T_nonneg hbm B)

theorem W_nonneg : ∀ (B : Finset X) (l : List X), 0 ≤ W (flow P) B l
  | _, [] => zero_le_one
  | B, x :: l => mul_nonneg (w_nonneg hbm B x) (W_nonneg _ l)

/-- `T · w = q`. -/
theorem T_mul_w (B : Finset X) (x : X) : T (flow P) B * w (flow P) B x = flow P B x := by
  unfold w
  rcases (T_nonneg hbm B).lt_or_eq with h | h
  · field_simp
  · rw [← h, zero_mul]
    by_cases hx : x ∈ B
    · simp [flow, hx]
    · have := flow_le_T hbm hx; rw [← h] at this
      linarith [flow_nonneg hbm B x]

omit hbm in
/-- **Flow conservation**: inflow equals outflow at every `∅ ≠ B ≠ X`. -/
theorem sum_flow_in (hP : IsChoiceRule P) {B : Finset X} (hB : B.Nonempty) (hBu : B ≠ univ) :
    ∑ b ∈ B, flow P (B.erase b) b = T (flow P) B := by
  have hA : (univ \ B).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
    exact fun h => hBu (eq_univ_of_forall fun x => h (mem_univ x))
  have hAc : (univ \ (univ \ B)).Nonempty := by
    rwa [sdiff_sdiff_right_self, univ_inter]
  have key := sum_bm_menu hP hA hAc
  rw [sdiff_sdiff_right_self, univ_inter] at key
  unfold T flow
  rw [sum_congr rfl fun x hx => ite_eq_right (mem_sdiff.1 hx).2, key]
  refine sum_congr rfl fun b hb => ?_
  rw [ite_eq_right (fun h => (mem_erase.1 h).1 rfl)]
  congr 1
  ext x; by_cases hxb : x = b <;> simp [hxb, hb]

omit hbm in
theorem T_empty [Nonempty X] (hP : IsChoiceRule P) : T (flow P) ∅ = 1 := by
  unfold T flow
  simp only [sdiff_empty, notMem_empty, ite_false]
  have h := (hP univ univ_nonempty).2.2
  rw [← h]
  refine sum_congr rfl fun x _ => ?_
  simp [bm]

theorem inflow_le (hP : IsChoiceRule P) {C : Finset X} {x : X} (hx : x ∉ C)
    (hu : insert x C ≠ univ) : flow P C x ≤ T (flow P) (insert x C) := by
  rw [← sum_flow_in hP (insert_nonempty x C) hu]
  have := single_le_sum (f := fun b => flow P ((insert x C).erase b) b)
    (fun b _ => flow_nonneg hbm _ b) (mem_insert_self x C)
  simpa [erase_insert hx] using this

/-- From any state with positive outflow the chain surely completes. -/
theorem G_eq_one (hP : IsChoiceRule P) :
    ∀ n, ∀ C : Finset X, (univ \ C).card = n → 0 < T (flow P) C → G (flow P) C = 1 := by
  intro n
  induction n with
  | zero =>
    intro C hn hT
    rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hn
    have : C = univ := eq_univ_of_forall fun x => hn (mem_univ x)
    subst this; simp [T] at hT
  | succ n ih =>
    intro C hn hT
    have hC : C ≠ univ := by rintro rfl; simp [T] at hT
    rw [G_step _ hC]
    have hterm : ∀ x ∈ univ \ C, w (flow P) C x * G (flow P) (insert x C) = w (flow P) C x := by
      intro x hx
      have hxC := (mem_sdiff.1 hx).2
      rcases (flow_nonneg hbm C x).lt_or_eq with hq | hq
      · by_cases hu : insert x C = univ
        · rw [hu, G_univ, mul_one]
        · rw [ih (insert x C) (by rw [sdiff_insert, card_erase_of_mem hx, hn]; rfl)
            (lt_of_lt_of_le hq (inflow_le hbm hP hxC hu)), mul_one]
      · rw [w, ← hq, zero_div, zero_mul]
    rw [sum_congr rfl hterm]
    unfold w
    rw [← sum_div]
    exact div_self hT.ne'

theorem G_eq_one' (hP : IsChoiceRule P) {C : Finset X} (hT : 0 < T (flow P) C) :
    G (flow P) C = 1 :=
  G_eq_one hbm hP _ C rfl hT

/-- **Markov property**: reaching `D` and then adding `b` has probability
`Pr(reach D) · w(D, b)`. -/
theorem hit_eq (hP : IsChoiceRule P) {D : Finset X} {b : X} (hb : b ∉ D) :
    ∀ n, ∀ C : Finset X, (univ \ C).card = n →
      H (flow P) D b C = R (flow P) D C * w (flow P) D b := by
  have hD : D ≠ univ := by rintro rfl; exact hb (mem_univ b)
  intro n
  induction n with
  | zero =>
    intro C hn
    rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hn
    have : C = univ := eq_univ_of_forall fun x => hn (mem_univ x)
    subst this
    rw [H_univ, R_univ _ hD, zero_mul]
  | succ n ih =>
    intro C hn
    have hC : C ≠ univ := by rintro rfl; simp at hn
    by_cases hCD : C = D
    · subst hCD
      rw [H_self _ hD hb, R_self]
      rcases (flow_nonneg hbm C b).lt_or_eq with hq | hq
      · have hT : 0 < T (flow P) C := lt_of_lt_of_le hq (flow_le_T hbm hb)
        rw [G_eq_one' hbm hP hT]
        by_cases hu : insert b C = univ
        · rw [hu, G_univ]; ring
        · rw [G_eq_one' hbm hP (lt_of_lt_of_le hq (inflow_le hbm hP hb hu))]; ring
      · rw [w, ← hq, zero_div, zero_mul, mul_zero]
    · rw [H_step _ hC hCD, R_step _ hC hCD, sum_mul]
      refine sum_congr rfl fun x hx => ?_
      rw [ih (insert x C) (by rw [sdiff_insert, card_erase_of_mem hx, hn]; rfl)]
      ring

omit hbm in
/-- **Last-step decomposition**: to reach `D ⊋ C` the walk passes through
`D ∖ b` and then adds `b`, for exactly one `b ∈ D ∖ C`. -/
theorem reach_eq_sum_hit :
    ∀ n, ∀ {C D : Finset X}, (D \ C).card = n + 1 → C ⊆ D →
      R (flow P) D C = ∑ b ∈ D \ C, H (flow P) (D.erase b) b C := by
  intro n
  induction n with
  | zero =>
    intro C D hn hCD
    obtain ⟨b, hb⟩ := card_eq_one.1 hn
    have hbD : b ∈ D := (mem_sdiff.1 (hb ▸ mem_singleton_self b : b ∈ D \ C)).1
    have hbC : b ∉ C := (mem_sdiff.1 (hb ▸ mem_singleton_self b : b ∈ D \ C)).2
    have hDe : D = insert b C := by
      ext x; constructor
      · intro hx; by_cases hxC : x ∈ C
        · exact mem_insert_of_mem hxC
        · have : x ∈ D \ C := mem_sdiff.2 ⟨hx, hxC⟩
          rw [hb, mem_singleton] at this; rw [this]; exact mem_insert_self _ _
      · intro hx; rcases mem_insert.1 hx with rfl | hx
        · exact hbD
        · exact hCD hx
    have hC : C ≠ univ := fun h => hbC (h ▸ mem_univ b)
    have hCne : C ≠ D := by rintro rfl; exact hbC hbD
    have hDb : D.erase b = C := by rw [hDe, erase_insert hbC]
    rw [hb, sum_singleton, hDb, H_self _ hC hbC, ← hDe, R_step _ hC hCne]
    rw [sum_eq_single_of_mem b (mem_sdiff.2 ⟨mem_univ b, hbC⟩)]
    · rw [← hDe, R_self]
    · intro x hx hxb
      rw [R_eq_zero]
      · ring
      · intro h
        have hxD := h (mem_insert_self x C)
        rw [hDe] at hxD
        rcases mem_insert.1 hxD with h' | h'
        · exact hxb h'
        · exact (mem_sdiff.1 hx).2 h'
  | succ n ih =>
    intro C D hn hCD
    have hC : C ≠ univ := by
      rintro rfl
      have : D \ univ = ∅ := sdiff_eq_empty_iff_subset.2 (subset_univ _)
      rw [this] at hn; simp at hn
    have hCne : C ≠ D := by rintro rfl; simp at hn
    rw [R_step _ hC hCne]
    -- left side: only `x ∈ D ∖ C` contribute
    have hL : ∀ x ∈ univ \ C, w (flow P) C x * R (flow P) D (insert x C) =
        if x ∈ D \ C then w (flow P) C x *
          ∑ b ∈ D \ insert x C, H (flow P) (D.erase b) b (insert x C) else 0 := by
      intro x hx
      split_ifs with hxD
      · rw [ih (by rw [sdiff_insert, card_erase_of_mem hxD, hn]; rfl)
          (insert_subset (mem_sdiff.1 hxD).1 hCD)]
      · rw [R_eq_zero, mul_zero]
        intro h
        exact hxD (mem_sdiff.2 ⟨h (mem_insert_self x C), (mem_sdiff.1 hx).2⟩)
    rw [sum_congr rfl hL, ← sum_filter]
    have hfilt : (univ \ C).filter (fun x => x ∈ D \ C) = D \ C := by
      ext x; simp only [mem_filter, mem_sdiff, mem_univ, true_and]; tauto
    rw [hfilt]
    -- right side: each `H` steps once (since `|D ∖ C| ≥ 2`, `C ≠ D ∖ b`)
    have hR : ∀ b ∈ D \ C, H (flow P) (D.erase b) b C =
        ∑ x ∈ (D.erase b) \ C, w (flow P) C x * H (flow P) (D.erase b) b (insert x C) := by
      intro b hb
      have hne : C ≠ D.erase b := by
        intro h
        have : (D \ C).card = 1 := by
          rw [h, sdiff_erase_self (mem_sdiff.1 hb).1]
          exact card_singleton b
        rw [this] at hn; omega
      rw [H_step _ hC hne]
      rw [← sum_subset (s₁ := (D.erase b) \ C) (s₂ := univ \ C)]
      · intro x hx; exact mem_sdiff.2 ⟨mem_univ x, (mem_sdiff.1 hx).2⟩
      · intro x hx hx'
        rw [H_eq_zero, mul_zero]
        intro h
        exact hx' (mem_sdiff.2 ⟨h (mem_insert_self x C), (mem_sdiff.1 hx).2⟩)
    rw [sum_congr rfl hR]
    simp_rw [mul_sum]
    refine sum_comm' fun x b => ?_
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    constructor
    · rintro ⟨⟨hxD, hxC⟩, hbD, hbx, hbC⟩
      exact ⟨⟨⟨Ne.symm hbx, hxD⟩, hxC⟩, hbD, hbC⟩
    · rintro ⟨⟨⟨hxb, hxD⟩, hxC⟩, hbD, hbC⟩
      exact ⟨⟨hxD, hxC⟩, hbD, Ne.symm hxb, hbC⟩

/-- **Reaching `D` has probability `T(D)`.** -/
theorem reach_eq_T [Nonempty X] (hP : IsChoiceRule P) :
    ∀ n, ∀ D : Finset X, D.card = n → D ≠ univ → R (flow P) D ∅ = T (flow P) D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hn hDu
    rcases D.eq_empty_or_nonempty with rfl | hD
    · rw [R_self, G_eq_one' hbm hP (by rw [T_empty hP]; exact one_pos), T_empty hP]
    · obtain ⟨m, hm⟩ : ∃ m, (D \ ∅).card = m + 1 := ⟨D.card - 1, by
        rw [sdiff_empty]; have := hD.card_pos; omega⟩
      rw [reach_eq_sum_hit m hm (empty_subset D), sdiff_empty, ← sum_flow_in hP hD hDu]
      refine sum_congr rfl fun b hb => ?_
      have hbD : b ∉ D.erase b := fun h => (mem_erase.1 h).1 rfl
      rw [hit_eq hbm hP hbD _ ∅ rfl, ih (D.erase b).card (by rw [← hn]; exact card_erase_lt_of_mem hb)
        _ rfl (fun h => hDu (by rw [← insert_erase hb, h]; exact insert_eq_of_mem (mem_univ b))), T_mul_w hbm]

/-- **The chain reproduces the flow**: the probability that `b` comes right
after the set `D` is `q(D, b)`. -/
theorem hit_empty_eq [Nonempty X] (hP : IsChoiceRule P) {D : Finset X} {b : X} (hb : b ∉ D) :
    H (flow P) D b ∅ = flow P D b := by
  have hD : D ≠ univ := by rintro rfl; exact hb (mem_univ b)
  rw [hit_eq hbm hP hb _ ∅ rfl, reach_eq_T hbm hP _ D rfl hD, T_mul_w hbm]

end Flow

/-! ### From lists to rankings -/

section Transfer

/-- The ranking read off as a list, best first. -/
def toList (r : Ranking X) : List X := List.ofFn r.symm

theorem toList_mem (r : Ranking X) : toList r ∈ ords (univ : Finset X) := by
  rw [mem_ords]
  refine ⟨List.nodup_ofFn.2 r.symm.injective, ?_⟩
  ext x
  simp only [toList, List.mem_toFinset, List.mem_ofFn, mem_univ, iff_true]
  exact ⟨r x, by simp⟩

omit [DecidableEq X] in
theorem toList_injective : Function.Injective (toList (X := X)) := fun _ _ h =>
  Equiv.symm_bijective.injective (Equiv.coe_inj.1 (List.ofFn_injective h))

theorem image_toList : univ.image (toList (X := X)) = ords univ := by
  ext l
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨r, rfl⟩; exact toList_mem r
  · intro hl
    rw [mem_ords] at hl
    obtain ⟨hnd, ht⟩ := hl
    have hall : ∀ x, x ∈ l := fun x => by rw [← List.mem_toFinset, ht]; exact mem_univ x
    have hlen : l.length = Fintype.card X := by
      rw [← List.toFinset_card_of_nodup hnd, ht, card_univ]
    let e : Fin l.length ≃ X := List.Nodup.getEquivOfForallMemList l hnd hall
    refine ⟨((finCongr hlen.symm).trans e).symm, ?_⟩
    apply List.ext_get
    · simp [toList, hlen]
    · intro n h1 h2
      simp [toList, e, List.Nodup.getEquivOfForallMemList]

/-- Sums over rankings are sums over orderings of `X`. -/
theorem sum_rankings (f : List X → ℝ) : ∑ r : Ranking X, f (toList r) = ∑ l ∈ ords univ, f l := by
  rw [← image_toList, sum_image fun r _ s _ h => toList_injective h]

omit [Fintype X] in
/-- `hit` along a list, in terms of positions. -/
theorem hit_iff {D : Finset X} {b : X} : ∀ {C : Finset X} {l : List X},
    hit D b C l ↔ ∃ k, ∃ hk : k < l.length, l[k] = b ∧ C ∪ (l.take k).toFinset = D
  | C, [] => by simp [hit]
  | C, x :: l => by
    simp only [hit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [hit_iff]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨k, hk, h1, h2⟩)
      · exact ⟨0, by simp, rfl, by simp⟩
      · refine ⟨k + 1, by simpa using hk, by simpa using h1, ?_⟩
        rw [← h2, List.take_succ_cons, List.toFinset_cons, union_insert, insert_union]
    · rintro ⟨k, hk, h1, h2⟩
      cases k with
      | zero => left; simp at h1 h2; exact ⟨h2, h1⟩
      | succ k =>
        right
        refine ⟨k, by simpa using hk, by simpa using h1, ?_⟩
        rw [← h2, List.take_succ_cons, List.toFinset_cons, union_insert, insert_union]

omit [DecidableEq X] in
theorem mem_take_toList (r : Ranking X) (k : ℕ) (x : X) :
    x ∈ (toList r).take k ↔ (r x : ℕ) < k := by
  rw [List.mem_take_iff_getElem]
  simp only [toList, List.getElem_ofFn, List.length_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Equiv.apply_symm_apply]
    exact (lt_min_iff.1 hi).1
  · intro h
    exact ⟨r x, lt_min h (r x).2, by simp⟩

/-- The BM event of a ranking is the `hit` event of its list. -/
theorem bmEvent_iff (r : Ranking X) (A : Finset X) (a : X) :
    (IsTop r A a ∧ ∀ c, c ∉ A → r c < r a) ↔ hit (univ \ A) a ∅ (toList r) := by
  rw [hit_iff]
  simp only [empty_union]
  constructor
  · rintro ⟨⟨haA, htop⟩, hout⟩
    refine ⟨r a, by simp [toList], by simp [toList], ?_⟩
    ext x
    rw [List.mem_toFinset, mem_take_toList, mem_sdiff]
    simp only [mem_univ, true_and]
    constructor
    · intro h hx; exact absurd (htop x hx) (not_le.2 (Fin.lt_def.2 h))
    · intro hx; exact Fin.lt_def.1 (hout x hx)
  · rintro ⟨k, hk, hb, hD⟩
    have hk' : k = r a := by
      simp only [toList, List.getElem_ofFn] at hb
      rw [← hb]; simp
    subst hk'
    have key : ∀ x, (r x : ℕ) < r a ↔ x ∉ A := by
      intro x
      have := congrArg (x ∈ ·) hD
      simp only [List.mem_toFinset, mem_take_toList, mem_sdiff, mem_univ, true_and] at this
      exact Iff.of_eq this
    refine ⟨⟨?_, fun x hx => ?_⟩, fun c hc => Fin.lt_def.2 ((key c).2 hc)⟩
    · by_contra h; exact lt_irrefl _ ((key a).2 h)
    · by_contra h; exact absurd ((key x).1 (Fin.lt_def.1 (lt_of_not_ge h))) (not_not.2 hx)

end Transfer

end Falmagne

/-! ### Falmagne's theorem -/

open Falmagne

/-- **Falmagne (1978).** A choice rule whose Block–Marschak polynomials are
all nonnegative is a random utility model. -/
theorem falmagne {P : Finset X → X → ℝ} (hP : IsChoiceRule P)
    (hbm : ∀ A a, a ∈ A → 0 ≤ bm P A a) :
    ∃ μ : Ranking X → ℝ, IsRUM μ ∧ ∀ A : Finset X, A.Nonempty → ∀ a, rumP μ A a = P A a := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨fun r => if r = Fintype.equivFin X then 1 else 0, isRUM_pointMass _, ?_⟩
    intro A hA; obtain ⟨x, _⟩ := hA; exact isEmptyElim x
  set μ : Ranking X → ℝ := fun r => W (flow P) ∅ (toList r)
  have hμ : IsRUM μ := by
    refine ⟨fun r => W_nonneg hbm ∅ _, ?_⟩
    rw [sum_rankings (W (flow P) ∅), ← sdiff_empty (s := univ)]
    exact G_eq_one' hbm hP (by rw [T_empty hP]; exact one_pos)
  -- equal BM polynomials
  have hBM : ∀ A a, a ∈ A → bm (rumP μ) A a = bm P A a := by
    intro A a ha
    rw [bm_rumP μ ha]
    simp_rw [bmEvent_iff]
    rw [sum_rankings (fun l => W (flow P) ∅ l * if hit (univ \ A) a ∅ l then 1 else 0)]
    have hH := hit_empty_eq hbm hP (D := univ \ A) (b := a) (by simp [ha])
    unfold H at hH
    rw [sdiff_empty] at hH
    rw [hH, flow, ite_eq_right (by simp [ha]), sdiff_sdiff_right_self, univ_inter]
  refine ⟨μ, hμ, fun A hA a => ?_⟩
  by_cases ha : a ∈ A
  · rw [← sum_bm (rumP μ), ← sum_bm P]
    exact sum_congr rfl fun C _ => hBM _ _ (mem_union_left _ ha)
  · rw [(hP A hA).2.1 a ha, (rumP_isChoiceRule hμ A hA).2.1 a ha]

/-- **Block–Marschak–Falmagne.** A choice rule is a random utility model iff
all its Block–Marschak polynomials are nonnegative. -/
theorem isRUM_iff_bm_nonneg {P : Finset X → X → ℝ} (hP : IsChoiceRule P) :
    (∃ μ : Ranking X → ℝ, IsRUM μ ∧ ∀ A : Finset X, A.Nonempty → ∀ a, rumP μ A a = P A a) ↔
      ∀ A a, a ∈ A → 0 ≤ bm P A a := by
  constructor
  · rintro ⟨μ, hμ, hPμ⟩ A a ha
    have : bm P A a = bm (rumP μ) A a := by
      unfold bm
      refine sum_congr rfl fun C _ => ?_
      rw [hPμ _ ⟨a, mem_union_left _ ha⟩]
    rw [this]; exact bm_rumP_nonneg hμ ha
  · exact falmagne hP

end StochasticChoice

end Econ
