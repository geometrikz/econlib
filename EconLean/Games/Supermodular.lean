/-
# Supermodular games: extremal pure equilibria (Topkis 1979; Milgrom–Roberts 1990)

A game has **strategic complements** when each player's strategy set is ordered and her
payoff has increasing differences between her own strategy and the profile: raising the
others' strategies raises the gain from a higher own strategy (Milgrom and Roberts 1990;
Vives 1990). Here strategy sets are finite linear orders (for instance price or quantity
grids).

Main results:
* `greatestBR_mono` (Topkis's monotonicity theorem): the greatest best response is
  nondecreasing in the others' strategies; likewise `leastBR_mono`.
* `exists_greatest_fixed_of_mono`: an order-theoretic lemma: in a finite partial order with a
  top element, iterating a monotone map from the top reaches a fixed point that lies above
  every `y ≤ f y` (Tarski's construction for finite lattices).
* `supermodular_greatest_nash`, `supermodular_least_nash` (the finite-chain case of Topkis
  1979, Milgrom–Roberts 1990 Thm. 5 and Vives 1990, which allow complete lattices of
  strategies with upper semicontinuous payoffs): a game with strategic complements has a **greatest** and a **least**
  pure Nash equilibrium. Every equilibrium lies between them.
-/
module

public import EconLean.Games.Strategic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Function Finset

/-- **Fixed point by iteration from the top.** If `α` is a finite partial order, `f` is
monotone and `a₀` lies above everything, the iterates `fⁿ a₀` reach a fixed point `x` with
`y ≤ x` for every `y ≤ f y` (in particular for every fixed point). -/
theorem exists_greatest_fixed_of_mono {α : Type*} [PartialOrder α] [Finite α] {f : α → α}
    (hf : Monotone f) (a₀ : α) (htop : ∀ y, y ≤ a₀) :
    ∃ x, f x = x ∧ ∀ y, y ≤ f y → y ≤ x := by
  set a : ℕ → α := fun n => f^[n] a₀
  have hanti : Antitone a := antitone_nat_of_succ_le fun n => by
    simp only [a, iterate_succ_apply']
    induction n with
    | zero => exact htop _
    | succ n ih =>
      simp only [iterate_succ_apply'] at ih ⊢
      exact hf ih
  have habove : ∀ y, y ≤ f y → ∀ n, y ≤ a n := fun y hy n => by
    induction n with
    | zero => exact htop y
    | succ n ih =>
      simp only [a, iterate_succ_apply'] at ih ⊢
      exact hy.trans (hf ih)
  have hni := not_injective_infinite_finite a
  simp only [Injective, not_forall] at hni
  obtain ⟨m, n, he, hmn⟩ := hni
  wlog h : m < n generalizing m n
  · exact this n m he.symm (Ne.symm hmn) (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hmn))
  have hstep : a (m + 1) = a m :=
    le_antisymm (hanti (Nat.le_succ m)) (he ▸ hanti (show m + 1 ≤ n by omega))
  refine ⟨a m, ?_, fun y hy => habove y hy m⟩
  simpa only [a, iterate_succ_apply'] using hstep

variable {I : Type*} [DecidableEq I] {S : I → Type*} [∀ i, LinearOrder (S i)]
  [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]

/-- **Increasing differences** (strategic complements): for `t ≤ t'` and profiles `s ≤ s'`,
the gain `u i (t', ·) − u i (t, ·)` is larger at `s'`. -/
def HasStrategicComplements (u : I → (∀ j, S j) → ℝ) : Prop :=
  ∀ i (s s' : ∀ j, S j), s ≤ s' → ∀ t t' : S i, t ≤ t' →
    u i (update s i t') - u i (update s i t) ≤ u i (update s' i t') - u i (update s' i t)

/-- The set of best responses of `i` to `s`. -/
noncomputable def bestResponses (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) :
    Finset (S i) :=
  univ.filter fun t => ∀ t' : S i, u i (update s i t') ≤ u i (update s i t)

omit [∀ i, LinearOrder (S i)] in
lemma bestResponses_nonempty (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) :
    (bestResponses u i s).Nonempty := by
  obtain ⟨t, -, ht⟩ := exists_max_image (univ : Finset (S i)) (fun t => u i (update s i t))
    univ_nonempty
  exact ⟨t, mem_filter.2 ⟨mem_univ _, fun t' => ht t' (mem_univ _)⟩⟩

/-- The **greatest best response**. -/
noncomputable def greatestBR (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) : S i :=
  (bestResponses u i s).max' (bestResponses_nonempty u i s)

/-- The **least best response**. -/
noncomputable def leastBR (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) : S i :=
  (bestResponses u i s).min' (bestResponses_nonempty u i s)

lemma greatestBR_isBR (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) :
    IsBestResponse u i s (greatestBR u i s) :=
  (mem_filter.1 ((bestResponses u i s).max'_mem _)).2

lemma leastBR_isBR (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) :
    IsBestResponse u i s (leastBR u i s) :=
  (mem_filter.1 ((bestResponses u i s).min'_mem _)).2

lemma le_greatestBR {u : I → (∀ j, S j) → ℝ} {i : I} {s : ∀ j, S j} {t : S i}
    (ht : IsBestResponse u i s t) : t ≤ greatestBR u i s :=
  (bestResponses u i s).le_max' t (mem_filter.2 ⟨mem_univ _, ht⟩)

lemma leastBR_le {u : I → (∀ j, S j) → ℝ} {i : I} {s : ∀ j, S j} {t : S i}
    (ht : IsBestResponse u i s t) : leastBR u i s ≤ t :=
  (bestResponses u i s).min'_le t (mem_filter.2 ⟨mem_univ _, ht⟩)

/-- **Topkis's monotonicity theorem**: with strategic complements, the greatest best response
is nondecreasing in the profile. -/
theorem greatestBR_mono {u : I → (∀ j, S j) → ℝ} (hu : HasStrategicComplements u) (i : I) :
    Monotone (greatestBR u i) := by
  intro s s' hss'
  by_contra hlt
  push Not at hlt
  set t := greatestBR u i s
  set t' := greatestBR u i s'
  -- `t` beats `t'` at `s`, so by increasing differences also at `s'`.
  have h1 : u i (update s i t') ≤ u i (update s i t) := greatestBR_isBR u i s t'
  have h2 := hu i s s' hss' t' t hlt.le
  have hbr : IsBestResponse u i s' t := fun t'' => by
    have := greatestBR_isBR u i s' t''
    linarith
  exact absurd (le_greatestBR hbr) (not_le.2 hlt)

/-- The least best response is nondecreasing in the profile. -/
theorem leastBR_mono {u : I → (∀ j, S j) → ℝ} (hu : HasStrategicComplements u) (i : I) :
    Monotone (leastBR u i) := by
  intro s s' hss'
  by_contra hlt
  push Not at hlt
  set t := leastBR u i s
  set t' := leastBR u i s'
  -- `t'` beats `t` at `s'`, so by increasing differences also at `s`.
  have h1 : u i (update s' i t) ≤ u i (update s' i t') := leastBR_isBR u i s' t
  have h2 := hu i s s' hss' t' t hlt.le
  have hbr : IsBestResponse u i s t' := fun t'' => by
    have := leastBR_isBR u i s t''
    linarith
  exact absurd (leastBR_le hbr) (not_le.2 hlt)

/-- **Greatest pure Nash equilibrium** of a game with strategic complements (Topkis 1979;
Milgrom–Roberts 1990): there is a pure equilibrium `s̄` with `s ≤ s̄` for every pure
equilibrium `s`. -/
theorem supermodular_greatest_nash [Fintype I] {u : I → (∀ j, S j) → ℝ}
    (hu : HasStrategicComplements u) :
    ∃ s, IsNash u s ∧ ∀ s', IsNash u s' → s' ≤ s := by
  set F : (∀ j, S j) → ∀ j, S j := fun s i => greatestBR u i s
  have hF : Monotone F := fun s s' h i => greatestBR_mono hu i h
  set top : ∀ j, S j := fun i => (univ : Finset (S i)).max' univ_nonempty
  obtain ⟨x, hx, hmax⟩ := exists_greatest_fixed_of_mono hF top
    fun y i => (univ : Finset (S i)).le_max' _ (mem_univ _)
  have hnash : ∀ s, F s = s → IsNash u s := fun s hs =>
    (isNash_iff_bestResponse u s).2 fun i => by
      have := greatestBR_isBR u i s
      rwa [show greatestBR u i s = s i from congrFun hs i] at this
  refine ⟨x, hnash x hx, fun s' hs' => hmax s' fun i => ?_⟩
  exact le_greatestBR ((isNash_iff_bestResponse u s').1 hs' i)

/-- **Least pure Nash equilibrium** of a game with strategic complements. -/
theorem supermodular_least_nash [Fintype I] {u : I → (∀ j, S j) → ℝ}
    (hu : HasStrategicComplements u) :
    ∃ s, IsNash u s ∧ ∀ s', IsNash u s' → s ≤ s' := by
  -- Apply the fixed-point lemma in the order dual.
  set F : (∀ j, S j)ᵒᵈ → (∀ j, S j)ᵒᵈ := fun s => OrderDual.toDual fun i =>
    leastBR u i (OrderDual.ofDual s)
  have hF : Monotone F := fun s s' h i => leastBR_mono hu i h
  set bot : ∀ j, S j := fun i => (univ : Finset (S i)).min' univ_nonempty
  obtain ⟨x, hx, hmin⟩ := exists_greatest_fixed_of_mono hF (OrderDual.toDual bot)
    fun y i => (univ : Finset (S i)).min'_le _ (mem_univ _)
  have hnash : ∀ s : ∀ j, S j, (fun i => leastBR u i s) = s → IsNash u s := fun s hs =>
    (isNash_iff_bestResponse u s).2 fun i => by
      have := leastBR_isBR u i s
      rwa [show leastBR u i s = s i from congrFun hs i] at this
  refine ⟨OrderDual.ofDual x, hnash _ hx, fun s' hs' => ?_⟩
  exact hmin (OrderDual.toDual s') fun i => leastBR_le ((isNash_iff_bestResponse u s').1 hs' i)

/-- Witness: a two-player coordination game on `{0, 1}` (`Bool`, with `false < true`) where
each player gets `1` for matching. It has strategic complements; its least and greatest
equilibria are "both `false`" and "both `true`". -/
example : HasStrategicComplements (I := Bool) (S := fun _ => Bool)
    (fun i s => if s i = s (!i) then (1 : ℝ) else 0) := by
  intro i s s' hss' t t' htt'
  have h1 := hss' true
  have h2 := hss' false
  cases i <;> cases t <;> cases t' <;> simp at htt' ⊢ <;>
    cases hs : s true <;> cases hs' : s' true <;> cases hf : s false <;> cases hf' : s' false <;>
    simp_all [Bool.le_iff_imp]

end Econ
