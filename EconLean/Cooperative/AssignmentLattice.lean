/-
# The assignment game: lattice of the core and competitive prices (Shapley–Shubik 1971)

Shapley and Shubik (1971), *The assignment game I: The core*; Roth and Sotomayor (1990),
Ch. 8. This file continues `Cooperative/Assignment`. Write a core payoff as buyers' payoffs `u`
and sellers' payoffs `p` (`IsCorePayoff`). Normalization: `a b s = h b s − c s` is buyer `b`'s
value for object `s` net of the seller's reservation value `c s`, and `p s` is the price net of
`c s`; so "an unsold object has price `0`" means it sells at its reservation value.

* `isCorePayoff_iff`: this is the core of `assignmentGame a`.
* `core_sup_inf`: the core is a lattice: if `(u, p)` and `(u', p')` are core payoffs, so are
  `(max u u', min p p')` and `(min u u', max p p')` (the buyers' join is the sellers' meet).
* `buyer_optimal_core`, `seller_optimal_core`: there is a core payoff that is best for every
  buyer simultaneously (and worst for every seller), and one best for every seller.
* `core_slack` (complementary slackness): at a core payoff, every pair of an optimal matching
  splits exactly its surplus, and every unmatched agent gets `0`.
* `compEq_core`: at a competitive equilibrium `(p, M)` the matching `M` is optimal (first
  welfare theorem) and, moreover, the prices with the buyers' surpluses are a core payoff.
* `core_compEq`: conversely, core prices together with any optimal matching form a competitive
  equilibrium. `compEq_prices_iff`: the competitive price vectors are exactly the core price
  vectors; `exists_min_compEq_prices`: there are **minimal competitive prices**, the prices of
  the buyer-optimal core point.
* Witness: one buyer, one seller, surplus `1`: `(1, 0)` and `(0, 1)` are both core payoffs
  (so the core is not a single point), and `p = 1/2` is a competitive price.

Not formalized: the Demange–Gale–Sotomayor exact auction converging to the minimal prices, and
strategy-proofness of the minimal-price mechanism for buyers (Leonard 1983; DGS 1986).
-/
module

public import EconLean.Cooperative.Assignment
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Lattice

@[expose] public section

namespace Econ

open Finset

variable {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]

/-- A **core payoff** of the assignment game: nonnegative buyer payoffs `u` and prices `p`
covering every pair and summing to the optimal assignment value. -/
def IsCorePayoff (a : B → S → ℝ) (u : B → ℝ) (p : S → ℝ) : Prop :=
  (∀ b, 0 ≤ u b) ∧ (∀ s, 0 ≤ p s) ∧ (∀ b s, a b s ≤ u b + p s) ∧
    ∑ b, u b + ∑ s, p s = assignmentGame a univ

/-- Core payoffs are exactly the core of the assignment game. -/
theorem isCorePayoff_iff (a : B → S → ℝ) (u : B → ℝ) (p : S → ℝ) :
    IsCorePayoff a u p ↔ IsInCore (assignmentGame a) (Sum.elim u p) := by
  rw [assignment_inCore_iff, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, IsCorePayoff, Sum.forall]
  tauto

lemma IsCorePayoff.weak (a : B → S → ℝ) {u : B → ℝ} {p : S → ℝ} (hu : ∀ b, 0 ≤ u b)
    (hp : ∀ s, 0 ≤ p s) (hcov : ∀ b s, a b s ≤ u b + p s) :
    assignmentGame a univ ≤ ∑ b, u b + ∑ s, p s := by
  have := assignment_weak_duality a (x := Sum.elim u p) (fun i => by cases i <;> simp [hu, hp])
    (fun b s => by simpa using hcov b s)
  rwa [Fintype.sum_sum_type] at this

/-- **The core is a lattice** (Shapley–Shubik 1971): taking the better payoff for every buyer
and the lower price for every seller (or the reverse) stays in the core. -/
theorem core_sup_inf {a : B → S → ℝ} {u u' : B → ℝ} {p p' : S → ℝ}
    (h : IsCorePayoff a u p) (h' : IsCorePayoff a u' p') :
    IsCorePayoff a (fun b => max (u b) (u' b)) (fun s => min (p s) (p' s)) ∧
      IsCorePayoff a (fun b => min (u b) (u' b)) (fun s => max (p s) (p' s)) := by
  obtain ⟨hu, hp, hc, hs⟩ := h
  obtain ⟨hu', hp', hc', hs'⟩ := h'
  have c1 : ∀ b s, a b s ≤ max (u b) (u' b) + min (p s) (p' s) := fun b s => by
    rcases min_choice (p s) (p' s) with hm | hm <;> rw [hm]
    · linarith [hc b s, le_max_left (u b) (u' b)]
    · linarith [hc' b s, le_max_right (u b) (u' b)]
  have c2 : ∀ b s, a b s ≤ min (u b) (u' b) + max (p s) (p' s) := fun b s => by
    rcases min_choice (u b) (u' b) with hm | hm <;> rw [hm]
    · linarith [hc b s, le_max_left (p s) (p' s)]
    · linarith [hc' b s, le_max_right (p s) (p' s)]
  have n1 : ∀ b, 0 ≤ max (u b) (u' b) := fun b => (hu b).trans (le_max_left _ _)
  have n2 : ∀ s, 0 ≤ min (p s) (p' s) := fun s => le_min (hp s) (hp' s)
  have n3 : ∀ b, 0 ≤ min (u b) (u' b) := fun b => le_min (hu b) (hu' b)
  have n4 : ∀ s, 0 ≤ max (p s) (p' s) := fun s => (hp s).trans (le_max_left _ _)
  have w1 := IsCorePayoff.weak a n1 n2 c1
  have w2 := IsCorePayoff.weak a n3 n4 c2
  -- the two totals add up to twice the optimal value
  have htot : (∑ b, max (u b) (u' b) + ∑ s, min (p s) (p' s)) +
      (∑ b, min (u b) (u' b) + ∑ s, max (p s) (p' s)) =
      (∑ b, u b + ∑ s, p s) + (∑ b, u' b + ∑ s, p' s) := by
    have e1 : ∀ b, max (u b) (u' b) + min (u b) (u' b) = u b + u' b := fun b => max_add_min _ _
    have e2 : ∀ s, min (p s) (p' s) + max (p s) (p' s) = p s + p' s := fun s => by
      rw [add_comm]; exact max_add_min _ _
    have := congrArg₂ (· + ·) (sum_congr rfl fun b (_ : b ∈ univ) => e1 b)
      (sum_congr rfl fun s (_ : s ∈ univ) => e2 s)
    simp only [sum_add_distrib] at this
    linarith
  exact ⟨⟨n1, n2, c1, by linarith⟩, ⟨n3, n4, c2, by linarith⟩⟩

omit [DecidableEq B] [DecidableEq S] in
/-- The set of core payoff vectors (as points of `(B → ℝ) × (S → ℝ)`) is compact. -/
lemma isCompact_core (a : B → S → ℝ) :
    IsCompact {q : (B → ℝ) × (S → ℝ) | IsCorePayoff a q.1 q.2} := by
  set V := assignmentGame a univ
  have hsub : {q : (B → ℝ) × (S → ℝ) | IsCorePayoff a q.1 q.2} ⊆
      (Set.univ.pi fun _ => Set.Icc 0 V) ×ˢ (Set.univ.pi fun _ => Set.Icc 0 V) := by
    rintro ⟨u, p⟩ ⟨hu, hp, -, hs⟩
    have hU : ∑ b, u b ≤ V := by linarith [sum_nonneg fun s (_ : s ∈ univ) => hp s]
    have hP : ∑ s, p s ≤ V := by linarith [sum_nonneg fun b (_ : b ∈ univ) => hu b]
    refine ⟨fun b _ => ⟨hu b, ?_⟩, fun s _ => ⟨hp s, ?_⟩⟩
    · exact (single_le_sum (fun b _ => hu b) (mem_univ b)).trans hU
    · exact (single_le_sum (fun s _ => hp s) (mem_univ s)).trans hP
  refine IsCompact.of_isClosed_subset
    ((isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc))
    ?_ hsub
  have hc1 : Continuous fun q : (B → ℝ) × (S → ℝ) => ∑ b, q.1 b + ∑ s, q.2 s := by fun_prop
  simp only [IsCorePayoff, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (isClosed_eq hc1 continuous_const)))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_le continuous_const (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le continuous_const (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_iInter fun s =>
      isClosed_le continuous_const (by fun_prop)

/-- **Buyer-optimal core point** (Shapley–Shubik 1971): there is a core payoff that gives every
buyer at least as much as any other core payoff, and every seller at most as much. -/
theorem buyer_optimal_core (a : B → S → ℝ) :
    ∃ u p, IsCorePayoff a u p ∧ ∀ u' p', IsCorePayoff a u' p' → (∀ b, u' b ≤ u b) ∧
      ∀ s, p s ≤ p' s := by
  set K := {q : (B → ℝ) × (S → ℝ) | IsCorePayoff a q.1 q.2}
  have hK := isCompact_core a
  obtain ⟨u₀, p₀, h₀⟩ := shapley_shubik a
  have hne : K.Nonempty := ⟨(u₀, p₀), h₀⟩
  -- for each buyer, a core point maximizing that buyer's payoff
  have hmax : ∀ b, ∃ q ∈ K, ∀ q' ∈ K, q'.1 b ≤ q.1 b := fun b => by
    obtain ⟨q, hq, hq'⟩ := hK.exists_isMaxOn hne (by fun_prop : Continuous fun q :
      (B → ℝ) × (S → ℝ) => q.1 b).continuousOn
    exact ⟨q, hq, fun q' h' => hq' h'⟩
  choose q hqK hq using hmax
  -- combine them with the lattice operation
  have key : ∀ T : Finset B, ∃ r ∈ K, ∀ b ∈ T, ∀ q' ∈ K, q'.1 b ≤ r.1 b := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨_, hne.some_mem, fun _ h => absurd h (notMem_empty _)⟩
    | insert b T _ ih =>
      obtain ⟨r, hr, hrT⟩ := ih
      refine ⟨((fun c => max (r.1 c) ((q b).1 c)), fun s => min (r.2 s) ((q b).2 s)),
        (core_sup_inf hr (hqK b)).1, fun c hc q' hq' => ?_⟩
      rcases mem_insert.1 hc with rfl | hc
      · exact (hq c q' hq').trans (le_max_right _ _)
      · exact (hrT c hc q' hq').trans (le_max_left _ _)
  obtain ⟨r, hr, hrb⟩ := key univ
  refine ⟨r.1, r.2, hr, fun u' p' h' => ⟨fun b => hrb b (mem_univ b) (u', p') h', fun s => ?_⟩⟩
  -- the prices are then minimal: the meet with any other core point has the same buyer payoffs
  by_contra hlt
  push Not at hlt
  have hm := (core_sup_inf hr h').1
  have hb : ∀ b, max (r.1 b) (u' b) = r.1 b := fun b =>
    max_eq_left (hrb b (mem_univ b) (u', p') h')
  obtain ⟨-, -, -, hsum⟩ := hm
  obtain ⟨-, -, -, hsumr⟩ := hr
  simp only [hb] at hsum
  have : ∑ s', min (r.2 s') (p' s') < ∑ s', r.2 s' :=
    sum_lt_sum (fun s' _ => min_le_left _ _) ⟨s, mem_univ s, min_lt_iff.2 (Or.inr hlt)⟩
  linarith

/-- **Seller-optimal core point**: symmetrically, some core payoff gives every seller at least
as much as any other core payoff, and every buyer at most as much. -/
theorem seller_optimal_core (a : B → S → ℝ) :
    ∃ u p, IsCorePayoff a u p ∧ ∀ u' p', IsCorePayoff a u' p' → (∀ s, p' s ≤ p s) ∧
      ∀ b, u b ≤ u' b := by
  set K := {q : (B → ℝ) × (S → ℝ) | IsCorePayoff a q.1 q.2}
  have hK := isCompact_core a
  obtain ⟨u₀, p₀, h₀⟩ := shapley_shubik a
  have hne : K.Nonempty := ⟨(u₀, p₀), h₀⟩
  have hmax : ∀ s, ∃ q ∈ K, ∀ q' ∈ K, q'.2 s ≤ q.2 s := fun s => by
    obtain ⟨q, hq, hq'⟩ := hK.exists_isMaxOn hne (by fun_prop : Continuous fun q :
      (B → ℝ) × (S → ℝ) => q.2 s).continuousOn
    exact ⟨q, hq, fun q' h' => hq' h'⟩
  choose q hqK hq using hmax
  have key : ∀ T : Finset S, ∃ r ∈ K, ∀ s ∈ T, ∀ q' ∈ K, q'.2 s ≤ r.2 s := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨_, hne.some_mem, fun _ h => absurd h (notMem_empty _)⟩
    | insert s T _ ih =>
      obtain ⟨r, hr, hrT⟩ := ih
      refine ⟨((fun c => min (r.1 c) ((q s).1 c)), fun c => max (r.2 c) ((q s).2 c)),
        (core_sup_inf hr (hqK s)).2, fun c hc q' hq' => ?_⟩
      rcases mem_insert.1 hc with rfl | hc
      · exact (hq c q' hq').trans (le_max_right _ _)
      · exact (hrT c hc q' hq').trans (le_max_left _ _)
  obtain ⟨r, hr, hrs⟩ := key univ
  refine ⟨r.1, r.2, hr, fun u' p' h' => ⟨fun s => hrs s (mem_univ s) (u', p') h', fun b => ?_⟩⟩
  by_contra hlt
  push Not at hlt
  have hm := (core_sup_inf hr h').2
  have hs : ∀ s, max (r.2 s) (p' s) = r.2 s := fun s =>
    max_eq_left (hrs s (mem_univ s) (u', p') h')
  obtain ⟨-, -, -, hsum⟩ := hm
  obtain ⟨-, -, -, hsumr⟩ := hr
  simp only [hs] at hsum
  have : ∑ b', min (r.1 b') (u' b') < ∑ b', r.1 b' :=
    sum_lt_sum (fun b' _ => min_le_left _ _) ⟨b, mem_univ b, min_lt_iff.2 (Or.inr hlt)⟩
  linarith

/-- An **optimal matching**: a matching of all agents attaining the optimal assignment value. -/
def IsOptimalMatching (a : B → S → ℝ) (M : Finset (B × S)) : Prop :=
  IsPairMatching M ∧ matchingValue a M = assignmentGame a univ

/-- Buyer `b` is matched in `M`. -/
def BMatched (M : Finset (B × S)) (b : B) : Prop := ∃ q ∈ M, q.1 = b
/-- Seller `s` is matched in `M`. -/
def SMatched (M : Finset (B × S)) (s : S) : Prop := ∃ q ∈ M, q.2 = s

omit [Fintype B] [Fintype S] [DecidableEq S] in
/-- For a matching, summing over pairs a function of the buyer is summing over matched buyers;
likewise for sellers. -/
lemma matching_sum_fst {M : Finset (B × S)} (hM : IsPairMatching M) (f : B → ℝ) :
    ∑ q ∈ M, f q.1 = ∑ b ∈ M.image Prod.fst, f b :=
  (sum_image fun q hq r hr h => hM.1 q hq r hr h).symm

omit [Fintype B] [Fintype S] [DecidableEq B] in
lemma matching_sum_snd {M : Finset (B × S)} (hM : IsPairMatching M) (f : S → ℝ) :
    ∑ q ∈ M, f q.2 = ∑ s ∈ M.image Prod.snd, f s :=
  (sum_image fun q hq r hr h => hM.2 q hq r hr h).symm

/-- **Complementary slackness**: at a core payoff, each pair of an optimal matching receives
exactly its surplus, and unmatched buyers and sellers receive `0`. -/
theorem core_slack {a : B → S → ℝ} {u : B → ℝ} {p : S → ℝ} (h : IsCorePayoff a u p)
    {M : Finset (B × S)} (hM : IsOptimalMatching a M) :
    (∀ q ∈ M, u q.1 + p q.2 = a q.1 q.2) ∧ (∀ b, ¬ BMatched M b → u b = 0) ∧
      ∀ s, ¬ SMatched M s → p s = 0 := by
  obtain ⟨hu, hp, hc, hs⟩ := h
  obtain ⟨hPM, hval⟩ := hM
  have hU := sum_add_sum_compl (M.image Prod.fst) u
  have hP := sum_add_sum_compl (M.image Prod.snd) p
  rw [← matching_sum_fst hPM u] at hU
  rw [← matching_sum_snd hPM p] at hP
  have hgap : ∑ q ∈ M, (u q.1 + p q.2 - a q.1 q.2) + (∑ b ∈ (M.image Prod.fst)ᶜ, u b +
      ∑ s ∈ (M.image Prod.snd)ᶜ, p s) = 0 := by
    rw [sum_sub_distrib, sum_add_distrib]
    unfold matchingValue at hval
    linarith
  have h1 : 0 ≤ ∑ q ∈ M, (u q.1 + p q.2 - a q.1 q.2) :=
    sum_nonneg fun q _ => by linarith [hc q.1 q.2]
  have h2 : 0 ≤ ∑ b ∈ (M.image Prod.fst)ᶜ, u b := sum_nonneg fun b _ => hu b
  have h3 : 0 ≤ ∑ s ∈ (M.image Prod.snd)ᶜ, p s := sum_nonneg fun s _ => hp s
  have e1 := (sum_eq_zero_iff_of_nonneg fun q _ => by linarith [hc q.1 q.2]).1
    (show ∑ q ∈ M, (u q.1 + p q.2 - a q.1 q.2) = 0 by linarith)
  have e2 := (sum_eq_zero_iff_of_nonneg fun b _ => hu b).1
    (show ∑ b ∈ (M.image Prod.fst)ᶜ, u b = 0 by linarith)
  have e3 := (sum_eq_zero_iff_of_nonneg fun s _ => hp s).1
    (show ∑ s ∈ (M.image Prod.snd)ᶜ, p s = 0 by linarith)
  refine ⟨fun q hq => by linarith [e1 q hq], fun b hb => e2 b ?_, fun s hs' => e3 s ?_⟩
  · rw [mem_compl, mem_image]; rintro ⟨q, hq, rfl⟩; exact hb ⟨q, hq, rfl⟩
  · rw [mem_compl, mem_image]; rintro ⟨q, hq, rfl⟩; exact hs' ⟨q, hq, rfl⟩

/-- A **competitive equilibrium** of the assignment market: prices `p ≥ 0` and a matching `M`
such that every matched buyer gets a seller in her demand set (and weakly prefers it to staying
out), every unmatched buyer demands nothing at positive surplus, and unsold objects have price
`0`. -/
structure IsCompEq (a : B → S → ℝ) (p : S → ℝ) (M : Finset (B × S)) : Prop where
  matching : IsPairMatching M
  nonneg : ∀ s, 0 ≤ p s
  demand : ∀ q ∈ M, ∀ s, a q.1 s - p s ≤ a q.1 q.2 - p q.2
  ir : ∀ q ∈ M, 0 ≤ a q.1 q.2 - p q.2
  unmatchedB : ∀ b, ¬ BMatched M b → ∀ s, a b s - p s ≤ 0
  unmatchedS : ∀ s, ¬ SMatched M s → p s = 0

/-- A buyer's surplus at prices `p` under matching `M` (zero if unmatched). -/
def buyerSurplus (a : B → S → ℝ) (p : S → ℝ) (M : Finset (B × S)) (b : B) : ℝ :=
  ∑ q ∈ M.filter (fun q => q.1 = b), (a q.1 q.2 - p q.2)

/-- **Competitive equilibria are efficient and in the core** (Shapley–Shubik 1971): at a
competitive equilibrium the matching is optimal and the buyers' surpluses with the prices form a
core payoff. -/
theorem compEq_core {a : B → S → ℝ} {p : S → ℝ} {M : Finset (B × S)} (h : IsCompEq a p M) :
    IsOptimalMatching a M ∧ IsCorePayoff a (buyerSurplus a p M) p := by
  have hPM := h.matching
  -- a matched buyer's surplus is that of her pair
  have hmatched : ∀ q ∈ M, buyerSurplus a p M q.1 = a q.1 q.2 - p q.2 := fun q hq => by
    unfold buyerSurplus
    exact sum_eq_single_of_mem (f := fun r : B × S => a r.1 r.2 - p r.2) q
      (mem_filter.2 ⟨hq, rfl⟩)
      (fun r hr hrq => absurd (hPM.1 r (mem_filter.1 hr).1 q hq (mem_filter.1 hr).2) hrq)
  have hunm : ∀ b, ¬ BMatched M b → buyerSurplus a p M b = 0 := fun b hb => by
    unfold buyerSurplus
    rw [sum_eq_zero]
    intro r hr; exact absurd ⟨r, (mem_filter.1 hr).1, (mem_filter.1 hr).2⟩ hb
  have hnn : ∀ b, 0 ≤ buyerSurplus a p M b := fun b => by
    by_cases hb : BMatched M b
    · obtain ⟨q, hq, rfl⟩ := hb; rw [hmatched q hq]; exact h.ir q hq
    · rw [hunm b hb]
  have hcov : ∀ b s, a b s ≤ buyerSurplus a p M b + p s := fun b s => by
    by_cases hb : BMatched M b
    · obtain ⟨q, hq, rfl⟩ := hb; rw [hmatched q hq]; linarith [h.demand q hq s]
    · rw [hunm b hb]; linarith [h.unmatchedB b hb s]
  -- total payoff equals the matching's value
  have htot : ∑ b, buyerSurplus a p M b + ∑ s, p s = matchingValue a M := by
    have hU : ∑ b, buyerSurplus a p M b = ∑ q ∈ M, (a q.1 q.2 - p q.2) := by
      unfold buyerSurplus
      rw [← sum_fiberwise M Prod.fst (fun q => a q.1 q.2 - p q.2)]
    have hP := sum_add_sum_compl (M.image Prod.snd) p
    rw [← matching_sum_snd hPM p] at hP
    have h0 : ∑ s ∈ (M.image Prod.snd)ᶜ, p s = 0 := sum_eq_zero fun s hs => h.unmatchedS s
      (by rintro ⟨q, hq, rfl⟩; exact (mem_compl.1 hs) (mem_image_of_mem _ hq))
    rw [hU, sum_sub_distrib, matchingValue]
    linarith
  have hM : IsMatchingIn univ M := ⟨hPM, fun _ _ => ⟨mem_univ _, mem_univ _⟩⟩
  have hle := le_assignmentGame a hM
  have hge := IsCorePayoff.weak a hnn h.nonneg hcov
  exact ⟨⟨hPM, by linarith⟩, hnn, h.nonneg, hcov, by linarith⟩

/-- **Core prices are competitive** (Shapley–Shubik 1971): the prices of any core payoff,
together with any optimal matching, form a competitive equilibrium. -/
theorem core_compEq {a : B → S → ℝ} {u : B → ℝ} {p : S → ℝ} (h : IsCorePayoff a u p)
    {M : Finset (B × S)} (hM : IsOptimalMatching a M) : IsCompEq a p M := by
  obtain ⟨e1, e2, e3⟩ := core_slack h hM
  obtain ⟨hu, hp, hc, -⟩ := h
  refine ⟨hM.1, hp, fun q hq s => ?_, fun q hq => ?_, fun b hb s => ?_, e3⟩
  · linarith [hc q.1 s, e1 q hq]
  · linarith [hu q.1, e1 q hq]
  · linarith [hc b s, e2 b hb]

/-- **Competitive prices are core prices** (Shapley–Shubik 1971): a price vector supports a
competitive equilibrium iff it is the sellers' side of a core payoff. -/
theorem compEq_prices_iff (a : B → S → ℝ) (p : S → ℝ) :
    (∃ M, IsCompEq a p M) ↔ ∃ u, IsCorePayoff a u p := by
  constructor
  · rintro ⟨M, hM⟩; exact ⟨_, (compEq_core hM).2⟩
  · rintro ⟨u, hu⟩
    obtain ⟨M, hM, hv⟩ := exists_optimal_matching a univ
    exact ⟨M, core_compEq hu ⟨hM.1, hv.symm⟩⟩

/-- **Minimal competitive prices**: some competitive price vector is below every competitive
price vector; it is the price vector of a buyer-optimal core point. -/
theorem exists_min_compEq_prices (a : B → S → ℝ) :
    ∃ u p, IsCorePayoff a u p ∧ (∀ u' p', IsCorePayoff a u' p' → ∀ b, u' b ≤ u b) ∧
      (∃ M, IsCompEq a p M) ∧ ∀ p' M', IsCompEq a p' M' → ∀ s, p s ≤ p' s := by
  obtain ⟨u, p, hup, hopt⟩ := buyer_optimal_core a
  obtain ⟨M, hM, hv⟩ := exists_optimal_matching a univ
  refine ⟨u, p, hup, fun u' p' h' => (hopt u' p' h').1, ⟨M, core_compEq hup ⟨hM.1, hv.symm⟩⟩,
    fun p' M' h' s => ?_⟩
  exact (hopt _ p' (compEq_core h').2).2 s

/-! ### Witness: one buyer, one seller -/

lemma unit_assignment_value :
    assignmentGame (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) univ = 1 := by
  apply le_antisymm
  · have := assignment_weak_duality (fun (_ : Unit) (_ : Unit) => (1 : ℝ))
      (x := Sum.elim (fun _ => 1) (fun _ => 0)) (fun i => by cases i <;> norm_num)
      (fun _ _ => by norm_num)
    simpa using this
  · have hM : IsMatchingIn (univ : Finset (Unit ⊕ Unit)) {((), ())} :=
      ⟨⟨fun _ _ _ _ _ => Subsingleton.elim _ _, fun _ _ _ _ _ => Subsingleton.elim _ _⟩,
        fun _ _ => ⟨mem_univ _, mem_univ _⟩⟩
    have := le_assignmentGame (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) hM
    simpa [matchingValue] using this

example : IsCorePayoff (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ => 1) (fun _ => 0) ∧
    IsCorePayoff (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ => 0) (fun _ => 1) ∧
    IsCompEq (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ => 1 / 2) {((), ())} := by
  refine ⟨⟨fun _ => by norm_num, fun _ => by norm_num, fun _ _ => by norm_num, ?_⟩,
    ⟨fun _ => by norm_num, fun _ => by norm_num, fun _ _ => by norm_num, ?_⟩,
    ⟨⟨fun _ _ _ _ _ => Subsingleton.elim _ _, fun _ _ _ _ _ => Subsingleton.elim _ _⟩, fun _ => by norm_num,
      fun _ _ _ => le_rfl, fun _ _ => by norm_num, fun b hb => absurd ⟨((), ()), by simp, rfl⟩ hb,
      fun s hs => absurd ⟨((), ()), by simp, rfl⟩ hs⟩⟩ <;>
  simp [unit_assignment_value]

end Econ
