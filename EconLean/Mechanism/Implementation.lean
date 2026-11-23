/-
# Nash implementation: Maskin's theorem (Maskin 1977/1999)

MWG §23.C (Defs. 23.C.6–23.C.7, Props. 23.C.2–23.C.3); Maskin (1999); Repullo (1987);
Jackson (2001). Agents `i ∈ I` have utilities `u i θ x` over outcomes `x ∈ X` in each state
`θ ∈ Θ`. A social choice correspondence `F : Θ → Set X` is **Nash implemented** by a
mechanism `g : (∀ i, M i) → X` if in every state the set of Nash equilibrium outcomes is
exactly `F θ`.

* `maskinMonotone_of_nashImplements` (Maskin's necessity theorem, MWG Prop. 23.C.2): a Nash
  implementable correspondence is **Maskin monotonic**: if `x ∈ F θ` and no agent's lower
  contour set at `x` shrinks from `θ` to `θ'`, then `x ∈ F θ'`.
* `maskin_sufficiency` (Maskin's sufficiency theorem, MWG Prop. 23.C.3): with at least three
  agents, a monotonic correspondence satisfying **no veto power** is Nash implemented by the
  canonical mechanism `maskinOutcome` (messages: a state, an outcome and an integer;
  unanimity, single deviation, and the integer game).
* A witness: a correspondence that changes with the state while preferences do not is not
  monotonic, hence not implementable.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Function Finset

variable {I Θ X : Type*} [DecidableEq I]

/-- `m` is a **Nash equilibrium** of the mechanism `g` in state `θ`. -/
def IsNashAt {M : I → Type*} (u : I → Θ → X → ℝ) (θ : Θ) (g : (∀ i, M i) → X)
    (m : ∀ i, M i) : Prop :=
  ∀ i (m' : M i), u i θ (g (update m i m')) ≤ u i θ (g m)

/-- `g` **Nash implements** `F`: in every state the Nash equilibrium outcomes are exactly
`F θ` (MWG Def. 23.C.6, full implementation). -/
def NashImplements {M : I → Type*} (u : I → Θ → X → ℝ) (F : Θ → Set X)
    (g : (∀ i, M i) → X) : Prop :=
  ∀ θ, {x | ∃ m, IsNashAt u θ g m ∧ g m = x} = F θ

/-- **Maskin monotonicity** (MWG Def. 23.C.7). -/
def IsMaskinMonotone (u : I → Θ → X → ℝ) (F : Θ → Set X) : Prop :=
  ∀ θ θ' x, x ∈ F θ → (∀ i y, u i θ y ≤ u i θ x → u i θ' y ≤ u i θ' x) → x ∈ F θ'

/-- **No veto power**: an outcome that all agents but at most one rank first is chosen. -/
def HasNoVetoPower (u : I → Θ → X → ℝ) (F : Θ → Set X) : Prop :=
  ∀ θ x (j : I), (∀ i, i ≠ j → ∀ y, u i θ y ≤ u i θ x) → x ∈ F θ

/-- **Maskin's necessity theorem** (MWG Prop. 23.C.2). -/
theorem maskinMonotone_of_nashImplements {M : I → Type*} {u : I → Θ → X → ℝ}
    {F : Θ → Set X} {g : (∀ i, M i) → X} (h : NashImplements u F g) :
    IsMaskinMonotone u F := by
  intro θ θ' x hx hlc
  rw [← h θ] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  rw [← h θ']
  exact ⟨m, fun i m' => hlc i _ (hm i m'), rfl⟩

/-- Witness: one agent who is indifferent between two outcomes in both states, while `F`
picks a different outcome in each state. `F` is not monotonic, so not implementable. -/
example : ¬ IsMaskinMonotone (I := Unit) (Θ := Bool) (X := Bool) (fun _ _ _ => 0)
    (fun θ => {θ}) := by
  intro h
  have := h false true false rfl fun _ _ _ => le_rfl
  simp at this

/-! ### The canonical mechanism -/

/-- A message: a state, an outcome and an integer. -/
abbrev MaskinMsg (Θ X : Type*) := Θ × X × ℕ

/-- **Rule 2** applies at `m` with deviator `j` and consensus `c`: everybody but `j`
announces `c`, `j` does not, and the announced outcome is in `F` of the announced state. -/
def MaskinRule2 (F : Θ → Set X) (m : I → MaskinMsg Θ X) (j : I) (c : MaskinMsg Θ X) : Prop :=
  (∀ i, i ≠ j → m i = c) ∧ m j ≠ c ∧ c.2.1 ∈ F c.1

/-- The winner of the integer game: an agent announcing a highest integer. -/
noncomputable def integerWinner [Fintype I] [Nonempty I] (m : I → MaskinMsg Θ X) : I :=
  (exists_max_image (univ : Finset I) (fun i => (m i).2.2) univ_nonempty).choose

open scoped Classical in
/-- **Maskin's canonical mechanism** (MWG proof of Prop. 23.C.3):
1. if everybody announces the same `(θ, x, k)` with `x ∈ F θ`, the outcome is `x`;
2. if all but one agent `j` announce `(θ, x, k)` with `x ∈ F θ`, the outcome is `j`'s
   announced outcome `y` if `j` weakly prefers `x` to `y` in state `θ`, and `x` otherwise;
3. otherwise the agent announcing the highest integer gets her announced outcome. -/
noncomputable def maskinOutcome [Fintype I] [Nonempty I] (u : I → Θ → X → ℝ) (F : Θ → Set X)
    (m : I → MaskinMsg Θ X) : X :=
  if h1 : ∃ c : MaskinMsg Θ X, (∀ i, m i = c) ∧ c.2.1 ∈ F c.1 then h1.choose.2.1
  else if h2 : ∃ jc : I × MaskinMsg Θ X, MaskinRule2 F m jc.1 jc.2 then
    if u h2.choose.1 h2.choose.2.1 (m h2.choose.1).2.1 ≤ u h2.choose.1 h2.choose.2.1 h2.choose.2.2.1
    then (m h2.choose.1).2.1 else h2.choose.2.2.1
  else (m (integerWinner m)).2.1

section Canonical

variable [Fintype I] [Nonempty I] {u : I → Θ → X → ℝ} {F : Θ → Set X}

omit [Nonempty I] in
lemma exists_ne_ne (hn : 3 ≤ Fintype.card I) (j j' : I) : ∃ k, k ≠ j ∧ k ≠ j' := by
  have h1 := pred_card_le_card_erase (s := univ) (a := j)
  have h2 := pred_card_le_card_erase (s := univ.erase j) (a := j')
  rw [card_univ] at h1
  obtain ⟨k, hk⟩ : ((univ.erase j).erase j').Nonempty := by
    rw [← card_pos]; omega
  simp only [mem_erase, mem_univ, and_true] at hk
  exact ⟨k, hk.2, hk.1⟩

omit [Nonempty I] in
/-- With at least three agents, rule 2 determines the deviator and the consensus. -/
lemma maskinRule2_unique (hn : 3 ≤ Fintype.card I) {m : I → MaskinMsg Θ X} {j j' : I}
    {c c' : MaskinMsg Θ X} (h : MaskinRule2 F m j c) (h' : MaskinRule2 F m j' c') :
    j = j' ∧ c = c' := by
  obtain ⟨k, hkj, hkj'⟩ := exists_ne_ne hn j j'
  have hcc : c = c' := (h.1 k hkj).symm.trans (h'.1 k hkj')
  subst hcc
  refine ⟨by_contra fun hne => h.2.1 (h'.1 j hne), rfl⟩

omit [Nonempty I] in
lemma not_rule1_of_rule2 (hn : 3 ≤ Fintype.card I) {m : I → MaskinMsg Θ X} {j : I}
    {c : MaskinMsg Θ X} (h : MaskinRule2 F m j c) :
    ¬ ∃ c' : MaskinMsg Θ X, (∀ i, m i = c') ∧ c'.2.1 ∈ F c'.1 := by
  rintro ⟨c', hc', -⟩
  obtain ⟨k, hkj, -⟩ := exists_ne_ne hn j j
  exact h.2.1 ((hc' j).trans ((hc' k).symm.trans (h.1 k hkj)))

omit [DecidableEq I] in
lemma maskinOutcome_rule1 {m : I → MaskinMsg Θ X} {c : MaskinMsg Θ X} (hc : ∀ i, m i = c)
    (hF : c.2.1 ∈ F c.1) : maskinOutcome u F m = c.2.1 := by
  have h1 : ∃ c : MaskinMsg Θ X, (∀ i, m i = c) ∧ c.2.1 ∈ F c.1 := ⟨c, hc, hF⟩
  rw [maskinOutcome, dite_eq_left_of_eq_true (eq_true h1)]
  obtain ⟨i⟩ := ‹Nonempty I›
  rw [← (h1.choose_spec.1 i).symm.trans (hc i)]

lemma maskinOutcome_rule2 (hn : 3 ≤ Fintype.card I) {m : I → MaskinMsg Θ X} {j : I}
    {c : MaskinMsg Θ X} (h : MaskinRule2 F m j c) :
    maskinOutcome u F m = if u j c.1 (m j).2.1 ≤ u j c.1 c.2.1 then (m j).2.1 else c.2.1 := by
  have h2 : ∃ jc : I × MaskinMsg Θ X, MaskinRule2 F m jc.1 jc.2 := ⟨(j, c), h⟩
  rw [maskinOutcome, dite_eq_right_of_eq_false (eq_false (not_rule1_of_rule2 hn h)),
    dite_eq_left_of_eq_true (eq_true h2)]
  obtain ⟨e1, e2⟩ := maskinRule2_unique hn h2.choose_spec h
  rw [e1, e2]

/-- Under rule 2 the deviator gets something no better than the consensus outcome. -/
lemma maskinOutcome_rule2_le (hn : 3 ≤ Fintype.card I) {m : I → MaskinMsg Θ X} {j : I}
    {c : MaskinMsg Θ X} (h : MaskinRule2 F m j c) :
    u j c.1 (maskinOutcome u F m) ≤ u j c.1 c.2.1 := by
  rw [maskinOutcome_rule2 hn h]
  split_ifs with hle
  · exact hle
  · exact le_rfl

/-- **The integer game**: if rule 1 fails and `i` cannot be the deviator of rule 2, then `i`
can obtain any outcome by announcing it together with a large enough integer. -/
lemma maskin_integer_deviation (hn : 3 ≤ Fintype.card I) {m : I → MaskinMsg Θ X} {i : I}
    (h1 : ¬ ∃ c : MaskinMsg Θ X, (∀ k, m k = c) ∧ c.2.1 ∈ F c.1)
    (h2 : ∀ c, ¬ MaskinRule2 F m i c) (y : X) :
    ∃ m' : MaskinMsg Θ X, maskinOutcome u F (update m i m') = y := by
  set N := ∑ k, (m k).2.2
  have hN : ∀ k, (m k).2.2 ≤ N := fun k =>
    single_le_sum (f := fun k => (m k).2.2) (fun _ _ => Nat.zero_le _) (mem_univ k)
  set m' : MaskinMsg Θ X := ((m i).1, y, N + 1)
  set m₁ := update m i m'
  have hm₁i : m₁ i = m' := update_self _ _ _
  have hm₁k : ∀ k, k ≠ i → m₁ k = m k := fun k hk => update_of_ne hk _ _
  refine ⟨m', ?_⟩
  -- Rule 1 fails: `i`'s integer is new.
  have r1 : ¬ ∃ c : MaskinMsg Θ X, (∀ k, m₁ k = c) ∧ c.2.1 ∈ F c.1 := by
    rintro ⟨c, hc, -⟩
    obtain ⟨k, hki, -⟩ := exists_ne_ne hn i i
    have := congrArg (fun z : MaskinMsg Θ X => z.2.2) ((hc i).trans (hc k).symm)
    simp only [hm₁i, hm₁k k hki, m'] at this
    have := hN k
    omega
  -- Rule 2 fails.
  have r2 : ¬ ∃ jc : I × MaskinMsg Θ X, MaskinRule2 F m₁ jc.1 jc.2 := by
    rintro ⟨⟨j, c⟩, hj⟩
    by_cases hji : j = i
    · subst hji
      -- Then the others agree on `c ∈ F`, so rule 1 or rule 2 (with deviator `i`) held at `m`.
      by_cases hmi : m j = c
      · exact h1 ⟨c, fun k => by
          by_cases hk : k = j
          · rw [hk, hmi]
          · rw [← hm₁k k hk]; exact hj.1 k hk, hj.2.2⟩
      · exact h2 c ⟨fun k hk => by rw [← hm₁k k hk]; exact hj.1 k hk, hmi, hj.2.2⟩
    · -- Then someone other than `i` announced `i`'s new integer.
      obtain ⟨k, hkj, hki⟩ := exists_ne_ne hn j i
      have := congrArg (fun z : MaskinMsg Θ X => z.2.2) ((hj.1 k hkj).trans (hj.1 i (Ne.symm hji)).symm)
      simp only [hm₁i, hm₁k k hki, m'] at this
      have := hN k
      omega
  -- `i` wins the integer game.
  have hwin : integerWinner m₁ = i := by
    have hspec := (exists_max_image (univ : Finset I) (fun k => (m₁ k).2.2)
      univ_nonempty).choose_spec
    by_contra hne
    have := hspec.2 i (mem_univ _)
    simp only [integerWinner] at hne
    rw [hm₁k _ hne, hm₁i] at this
    have := hN (exists_max_image (univ : Finset I) (fun k => (m₁ k).2.2) univ_nonempty).choose
    simp only [m'] at *
    omega
  rw [maskinOutcome, dite_eq_right_of_eq_false (eq_false r1), dite_eq_right_of_eq_false (eq_false r2), hwin]
  exact congrArg (fun z : MaskinMsg Θ X => z.2.1) hm₁i

/-- **Maskin's sufficiency theorem** (Maskin 1999; MWG Prop. 23.C.3). With at least three
agents, a Maskin-monotonic correspondence with no veto power is Nash implemented by the
canonical mechanism. -/
theorem maskin_sufficiency (hn : 3 ≤ Fintype.card I) (hmono : IsMaskinMonotone u F)
    (hnvp : HasNoVetoPower u F) :
    NashImplements (M := fun _ : I => MaskinMsg Θ X) u F (maskinOutcome u F) := by
  intro θ
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    by_cases h1 : ∃ c : MaskinMsg Θ X, (∀ k, m k = c) ∧ c.2.1 ∈ F c.1
    · -- Rule 1 at an equilibrium: monotonicity.
      obtain ⟨c, hc, hF⟩ := h1
      rw [maskinOutcome_rule1 hc hF]
      refine hmono c.1 θ c.2.1 hF fun i y hy => ?_
      have hr2 : MaskinRule2 F (update m i (c.1, y, c.2.2 + 1)) i c := by
        refine ⟨fun k hk => by rw [update_of_ne hk, hc k], ?_, hF⟩
        rw [update_self]
        intro he
        have := congrArg (fun z : MaskinMsg Θ X => z.2.2) he
        simp at this
      have := hm i (c.1, y, c.2.2 + 1)
      rw [maskinOutcome_rule2 hn hr2, maskinOutcome_rule1 hc hF, update_self] at this
      simpa only [hy, ↓reduceIte] using this
    · -- Otherwise all agents but at most one can get anything: no veto power.
      have top : ∀ i, (∀ c, ¬ MaskinRule2 F m i c) → ∀ y, u i θ y ≤ u i θ (maskinOutcome u F m) :=
        fun i hi y => by
          obtain ⟨m', hm'⟩ := maskin_integer_deviation hn h1 hi y
          rw [← hm']
          exact hm i m'
      by_cases h2 : ∃ jc : I × MaskinMsg Θ X, MaskinRule2 F m jc.1 jc.2
      · obtain ⟨⟨j, c⟩, hj⟩ := h2
        exact hnvp θ _ j fun i hij => top i fun c' hc' => hij (maskinRule2_unique hn hc' hj).1
      · obtain ⟨j⟩ := ‹Nonempty I›
        exact hnvp θ _ j fun i _ => top i fun c hc => h2 ⟨(i, c), hc⟩
  · intro hx
    -- Everybody announcing `(θ, x, 0)` is an equilibrium with outcome `x`.
    set c : MaskinMsg Θ X := (θ, x, 0)
    have hF : c.2.1 ∈ F c.1 := hx
    refine ⟨fun _ => c, fun i m' => ?_, maskinOutcome_rule1 (fun _ => rfl) hF⟩
    rw [maskinOutcome_rule1 (fun _ => rfl) hF]
    by_cases hm' : m' = c
    · rw [hm', update_eq_self_iff.2 rfl, maskinOutcome_rule1 (fun _ => rfl) hF]
    · have hr2 : MaskinRule2 F (update (fun _ => c) i m') i c :=
        ⟨fun k hk => update_of_ne hk _ _, by rw [update_self]; exact hm', hF⟩
      exact maskinOutcome_rule2_le hn hr2

/-- The **weak Pareto correspondence**: outcomes that no outcome makes everybody strictly
better off. -/
def weakPareto (u : I → Θ → X → ℝ) (θ : Θ) : Set X := {x | ¬ ∃ y, ∀ i, u i θ x < u i θ y}

omit [DecidableEq I] [Fintype I] [Nonempty I] in
lemma weakPareto_isMaskinMonotone : IsMaskinMonotone u (weakPareto u) := by
  intro θ θ' x hx hlc ⟨y, hy⟩
  refine hx ⟨y, fun i => ?_⟩
  by_contra h
  exact absurd (hlc i y (not_lt.1 h)) (not_le.2 (hy i))

omit [DecidableEq I] [Fintype I] [Nonempty I] in
lemma weakPareto_hasNoVetoPower [Nontrivial I] : HasNoVetoPower u (weakPareto u) := by
  intro θ x j hx ⟨y, hy⟩
  obtain ⟨i, hij⟩ := exists_ne j
  exact absurd (hx i hij y) (not_le.2 (hy i))

/-- Example (MWG Example 23.C.6): with at least three agents the weak Pareto correspondence is
Nash implementable. -/
theorem weakPareto_nashImplements (hn : 3 ≤ Fintype.card I) :
    NashImplements (M := fun _ : I => MaskinMsg Θ X) u (weakPareto u)
      (maskinOutcome u (weakPareto u)) :=
  have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  maskin_sufficiency hn weakPareto_isMaskinMonotone weakPareto_hasNoVetoPower

end Canonical

end Econ
