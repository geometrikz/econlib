/-
# Choice from lists (Rubinstein–Salant)

Reference. A. Rubinstein and Y. Salant (2006), "A model of choice from
lists", *Theoretical Economics* 1, 3–17.

A *list* is a nonempty finite sequence of distinct alternatives (`IsList`).
A choice function from lists `D` picks an element of each list
(`IsChoice`).

**Results.**
* `liia_pi`, `pi_liia`, `liia_iff_pi` (**RS Proposition 1**, for a choice
  function `D`): `D` satisfies *list independence of
  irrelevant alternatives* (deleting an unchosen element does not change the
  choice) iff it satisfies *partition independence*
  `D (L₁ ++ L₂) = D [D L₁, D L₂]` for disjoint lists.
* `rule R δ` is `D_{≽,δ}`: maximize the weak preference `R`, breaking ties
  within an indifference class in favour of the first (`δ = false`) or the
  last (`δ = true`) maximal element in the list. It is computed by a left
  fold of the binary choice `step`.
* `pi_rule` (RS Proposition 2, "if"): for a complete and transitive `R` and
  `δ` constant on indifference classes, `rule R δ` satisfies PI.
* `exists_rule_of_pi` (RS Proposition 2, "only if"): every choice function
  with PI is `rule R δ` for some complete transitive `R` and some `δ`
  constant on indifference classes. The proof reduces `D` to successive
  binary choices and settles the three-element cases by case analysis.
* `rule_mem`, `rule_isMax`: the rule picks an `R`-maximal element of the list.
* `pi_iff_rule`: the two directions together.
* Examples: `pi_first`, `first_eq_rule`, `first_not_rational` (choose the
  first element: everything indifferent, ties to the first; it has PI but
  is not rationalizable by a strict preference); `satisficing`
  (Simon; RS Example 2: satisfactory alternatives indifferent with ties to
  the first, unsatisfactory with ties to the last) with `pi_satisficing` and
  `satisficing_satisfactory`.

Here `R a b` (a `Bool`) means `a ≽ b`. In the converse the revealed relation
is `relOf D` (`a ≽ b` unless `b` is chosen from both `[a, b]` and `[b, a]`)
and the priority indicator is `deltaOf D`.

**Scope.** That the left fold picks the *first* (`δ = false`) or *last*
(`δ = true`) maximal element is by construction of `step`; only maximality
(`rule_isMax`) is stated as a theorem, and the satisficing example is
checked only to pick a satisfactory element when one exists. Uniqueness of
`(R, δ)` in Proposition 2 (for `δ` it can only hold on indifference classes
with at least two elements), Propositions 3–5 (WARP,
random choice) and lists with repetitions are not formalized.
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Push
public import Mathlib.Order.Basic

@[expose] public section

namespace Econ.ChoiceLists

variable {X : Type*} [DecidableEq X]

/-- A list: nonempty, no repetitions. -/
def IsList (L : List X) : Prop := L ≠ [] ∧ L.Nodup

/-- A choice function from lists picks an element of every list. -/
def IsChoice (D : List X → X) : Prop := ∀ L, IsList L → D L ∈ L

/-- **Partition independence.** -/
def PI (D : List X → X) : Prop :=
  ∀ L₁ L₂ : List X, IsList L₁ → IsList L₂ → L₁.Disjoint L₂ → D (L₁ ++ L₂) = D [D L₁, D L₂]

/-- **List independence of irrelevant alternatives.** -/
def LIIA (D : List X → X) : Prop :=
  ∀ L : List X, IsList L → ∀ b ∈ L, b ≠ D L → D (L.erase b) = D L

omit [DecidableEq X] in
theorem isList_singleton (x : X) : IsList [x] := ⟨List.cons_ne_nil _ _, List.nodup_singleton x⟩

omit [DecidableEq X] in
theorem choice_singleton {D : List X → X} (hD : IsChoice D) (x : X) : D [x] = x := by
  simpa using hD [x] (isList_singleton x)

/-! ### Proposition 1 -/

/-- LIIA extends to deleting any set of unchosen elements. -/
theorem liia_sublist {D : List X → X} (h : LIIA D) :
    ∀ (n : ℕ) (L L' : List X), L.length = n → IsList L → L'.Sublist L →
      D L ∈ L' → D L' = D L := by
  intro n
  induction n with
  | zero => intro L L' hn hL; exact absurd (List.length_eq_zero_iff.1 hn) hL.1
  | succ n ih =>
    intro L L' hn hL hsub hmem
    by_cases hlen : L'.length = L.length
    · rw [hsub.eq_of_length hlen]
    · obtain ⟨b, hbL, hbL'⟩ : ∃ b ∈ L, b ∉ L' := by
        by_contra hall
        push Not at hall
        exact hlen (Nat.le_antisymm hsub.length_le (hL.2.length_le_of_subset fun x hx => hall x hx))
      have hb : b ≠ D L := fun hb => hbL' (hb ▸ hmem)
      have hDe : D L ∈ L.erase b := (List.mem_erase_of_ne hb.symm).2 (hsub.subset hmem)
      have hLe : IsList (L.erase b) := ⟨List.ne_nil_of_mem hDe, hL.2.erase b⟩
      have hsub' : L'.Sublist (L.erase b) := by
        have := hsub.erase b
        rwa [List.erase_of_not_mem hbL'] at this
      have hlen' : (L.erase b).length = n := by
        rw [List.length_erase_of_mem hbL, hn]; rfl
      have e := h L hL b hbL hb
      rw [← e] at hmem ⊢
      exact ih _ _ hlen' hLe hsub' hmem

omit [DecidableEq X] in
theorem isList_append {L₁ L₂ : List X} (h : IsList (L₁ ++ L₂)) (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ []) :
    IsList L₁ ∧ IsList L₂ ∧ L₁.Disjoint L₂ :=
  ⟨⟨h₁, h.2.of_append_left⟩, ⟨h₂, h.2.of_append_right⟩, List.disjoint_of_nodup_append h.2⟩

omit [DecidableEq X] in
theorem pair_isList {a b : X} (h : a ≠ b) : IsList [a, b] :=
  ⟨List.cons_ne_nil _ _, by simp [h]⟩

theorem liia_pi {D : List X → X} (hD : IsChoice D) (h : LIIA D) : PI D := by
  intro L₁ L₂ h₁ h₂ hdis
  have hL : IsList (L₁ ++ L₂) :=
    ⟨by simp [h₁.1], List.nodup_append.2 ⟨h₁.2, h₂.2, fun a ha b hb hab => hdis ha (hab ▸ hb)⟩⟩
  have hm := hD _ hL
  have hm₁ := hD _ h₁
  have hm₂ := hD _ h₂
  have hne : D L₁ ≠ D L₂ := fun he => hdis hm₁ (he ▸ hm₂)
  rcases List.mem_append.1 hm with ha | ha
  · have e₁ := liia_sublist h _ _ _ rfl hL (List.sublist_append_left _ _) ha
    have e₂ := liia_sublist h _ _ [D L₁, D L₂] rfl hL
      ((List.singleton_sublist.2 hm₁).append (List.singleton_sublist.2 hm₂)) (by simp [e₁])
    rw [e₂]
  · have e₁ := liia_sublist h _ _ _ rfl hL (List.sublist_append_right _ _) ha
    have e₂ := liia_sublist h _ _ [D L₁, D L₂] rfl hL
      ((List.singleton_sublist.2 hm₁).append (List.singleton_sublist.2 hm₂)) (by simp [e₁])
    rw [e₂]

omit [DecidableEq X] in
/-- Under PI the chosen element stays chosen in any piece of a partition
that contains it. -/
theorem pi_piece {D : List X → X} (hD : IsChoice D) (h : PI D) {L₁ L₂ : List X}
    (hL : IsList (L₁ ++ L₂)) (h₁ : L₁ ≠ []) (h₂ : L₂ ≠ []) :
    (D (L₁ ++ L₂) ∈ L₁ → D L₁ = D (L₁ ++ L₂)) ∧ (D (L₁ ++ L₂) ∈ L₂ → D L₂ = D (L₁ ++ L₂)) := by
  obtain ⟨hl₁, hl₂, hdis⟩ := isList_append hL h₁ h₂
  have hm₁ := hD _ hl₁
  have hm₂ := hD _ hl₂
  have hne : D L₁ ≠ D L₂ := fun he => hdis hm₁ (he ▸ hm₂)
  have e := h L₁ L₂ hl₁ hl₂ hdis
  have hp := hD _ (pair_isList hne)
  rw [← e] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  constructor
  · intro ha
    rcases hp with hp | hp
    · exact hp.symm
    · exact absurd (hp ▸ hm₂) (hdis ha)
  · intro ha
    rcases hp with hp | hp
    · exact absurd ha (hdis (hp ▸ hm₁))
    · exact hp.symm

theorem pi_liia {D : List X → X} (hD : IsChoice D) (h : PI D) : LIIA D := by
  intro L hL b hb hbne
  obtain ⟨P, S, rfl⟩ := List.append_of_mem hb
  have hbP : b ∉ P := fun h' => by
    have := hL.2; rw [List.nodup_append] at this
    exact this.2.2 b h' b (List.mem_cons_self) rfl
  rw [List.erase_append_right _ hbP, List.erase_cons_head]
  have haL : D (P ++ b :: S) ∈ P ++ b :: S := hD _ hL
  have hPS : IsList (P ++ S) → P ≠ [] → S ≠ [] → D (P ++ S) = D [D P, D S] := fun hPS hP hS => by
    obtain ⟨hl₁, hl₂, hdis⟩ := isList_append hPS hP hS
    exact h P S hl₁ hl₂ hdis
  have hnd : (P ++ S).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl P).append (List.sublist_cons_self b S)) hL.2
  rcases List.mem_append.1 haL with haP | haS
  · have hP : P ≠ [] := List.ne_nil_of_mem haP
    have eP := (pi_piece hD h (L₁ := P) (L₂ := b :: S) hL hP (List.cons_ne_nil _ _)).1 haP
    by_cases hS : S = []
    · subst hS; simpa using eP
    · have hL' : IsList ((P ++ [b]) ++ S) := by simpa using hL
      have heq : (P ++ [b]) ++ S = P ++ b :: S := by simp
      have e1 := (pi_piece hD h hL' (by simp) hS).1 (by rw [heq]; simp [haP])
      rw [heq] at e1
      obtain ⟨hl₁', hl₂', hdis'⟩ := isList_append hL' (by simp) hS
      have hPI := h (P ++ [b]) S hl₁' hl₂' hdis'
      rw [heq, e1] at hPI
      rw [hPS ⟨by simp [hP], hnd⟩ hP hS, eP, ← hPI]
  · rcases List.mem_cons.1 haS with hab | haS
    · exact absurd hab.symm hbne
    · have hS : S ≠ [] := List.ne_nil_of_mem haS
      by_cases hP : P = []
      · subst hP
        have hbS : IsList ([b] ++ S) := by simpa using hL
        have := (pi_piece hD h hbS (List.cons_ne_nil _ _) hS).2 (by simpa using haS)
        simpa using this
      · have eS := (pi_piece hD h hL hP (List.cons_ne_nil _ _)).2 (List.mem_cons_of_mem _ haS)
        obtain ⟨hl₁', hbS, hdis'⟩ := isList_append hL hP (List.cons_ne_nil _ _)
        have hbS' : IsList ([b] ++ S) := by simpa using hbS
        have eS' := (pi_piece hD h hbS' (List.cons_ne_nil _ _) hS).2
          (by simp only [List.singleton_append]; rw [eS]; exact haS)
        simp only [List.singleton_append] at eS'
        have hPI := h P (b :: S) hl₁' hbS hdis'
        rw [hPS ⟨by simp [hP], hnd⟩ hP hS, eS']
        exact hPI.symm
/-- **Rubinstein–Salant Proposition 1**: LIIA ⟺ partition independence. -/
theorem liia_iff_pi {D : List X → X} (hD : IsChoice D) : LIIA D ↔ PI D :=
  ⟨liia_pi hD, pi_liia hD⟩

/-! ### The rule `D_{≽,δ}` -/

section Rule

variable (R : X → X → Bool) (δ : X → Bool)

/-- Binary choice: the strictly better element (`R a b` means `a ≽ b`), or
within an indifference class the later one if `δ = true` and the earlier
one if `δ = false`. -/
def step (c x : X) : X :=
  if R c x ∧ ¬ R x c then c else if R x c ∧ ¬ R c x then x else if δ x then x else c

/-- `D_{≽,δ}`: choose an `R`-maximal element, ties within an indifference
class broken by `δ` (first if `false`, last if `true`). -/
def rule [Inhabited X] : List X → X
  | [] => default
  | a :: l => l.foldl (step R δ) a

/-- `R` is complete and transitive. -/
def IsWeakOrder : Prop := (∀ a b, R a b ∨ R b a) ∧ ∀ a b c, R a b → R b c → R a c

/-- `δ` is constant on indifference classes (RS's priority indicator). -/
def ClassConst : Prop := ∀ a b, R a b → R b a → δ a = δ b

variable {R δ}

omit [DecidableEq X] in
set_option maxHeartbeats 4000000 in
theorem step_assoc (hR : IsWeakOrder R) (hδ : ClassConst R δ) (a b c : X) :
    step R δ (step R δ a b) c = step R δ a (step R δ b c) := by
  obtain ⟨tot, tr⟩ := hR
  have e1 := tot a b; have e2 := tot b c; have e3 := tot a c
  have t1 := tr a b c; have t2 := tr a c b; have t3 := tr b a c
  have t4 := tr b c a; have t5 := tr c a b; have t6 := tr c b a
  have d1 := hδ a b; have d2 := hδ b c; have d3 := hδ a c
  cases h1 : R a b <;> cases h2 : R b a <;> cases h3 : R b c <;> cases h4 : R c b <;>
    cases h5 : R a c <;> cases h6 : R c a <;>
    cases hda : δ a <;> cases hdb : δ b <;> cases hdc : δ c <;>
    simp_all [step]

omit [DecidableEq X] in
theorem foldl_step (hR : IsWeakOrder R) (hδ : ClassConst R δ) :
    ∀ (l : List X) (a b : X), l.foldl (step R δ) (step R δ a b) = step R δ a (l.foldl (step R δ) b)
  | [], _, _ => rfl
  | x :: l, a, b => by
    simp only [List.foldl_cons]
    rw [step_assoc hR hδ, foldl_step hR hδ l]

omit [DecidableEq X] in
theorem step_mem (c x : X) : step R δ c x = c ∨ step R δ c x = x := by
  unfold step; split_ifs <;> simp

omit [DecidableEq X] in
theorem foldl_mem : ∀ (l : List X) (a : X), l.foldl (step R δ) a ∈ a :: l
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons]
    have := foldl_mem l (step R δ a x)
    rcases step_mem (R := R) (δ := δ) a x with h | h <;> rw [h] at this ⊢ <;>
      exact (List.mem_cons.1 this).elim (fun h' => by simp [h']) (fun h' => by simp [h'])

omit [DecidableEq X] in
/-- The rule is a choice function. -/
theorem rule_mem [Inhabited X] : IsChoice (rule R δ) := by
  rintro (_ | ⟨a, l⟩) hL
  · exact absurd rfl hL.1
  · exact foldl_mem l a

omit [DecidableEq X] in
theorem step_ge (hR : IsWeakOrder R) (c x : X) :
    R (step R δ c x) c ∧ R (step R δ c x) x := by
  obtain ⟨tot, -⟩ := hR
  have hc := tot c c; have hx := tot x x
  unfold step; split_ifs <;> rcases tot c x with h | h <;> simp_all

omit [DecidableEq X] in
theorem foldl_ge (hR : IsWeakOrder R) :
    ∀ (l : List X) (a : X), ∀ y ∈ a :: l, R (l.foldl (step R δ) a) y
  | [], a => by
    intro y hy; simp only [List.mem_singleton] at hy; subst hy
    simpa using hR.1 y y
  | x :: l, a => by
    intro y hy
    simp only [List.foldl_cons]
    have ih := foldl_ge hR l (step R δ a x)
    obtain ⟨h1, h2⟩ := step_ge (δ := δ) hR a x
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hR.2 _ _ _ (ih _ List.mem_cons_self) h1
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hR.2 _ _ _ (ih _ List.mem_cons_self) h2
      · exact ih _ (List.mem_cons_of_mem _ hy)

omit [DecidableEq X] in
/-- The rule picks an `R`-maximal element of the list. -/
theorem rule_isMax [Inhabited X] (hR : IsWeakOrder R) {L : List X} (hL : L ≠ []) :
    ∀ y ∈ L, R (rule R δ L) y := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a l => exact foldl_ge hR l a

omit [DecidableEq X] in
/-- **Rubinstein–Salant Proposition 2, "if"**: `D_{≽,δ}` satisfies partition
independence. -/
theorem pi_rule [Inhabited X] (hR : IsWeakOrder R) (hδ : ClassConst R δ) : PI (rule R δ) := by
  rintro (_ | ⟨a, l₁⟩) (_ | ⟨b, l₂⟩) h₁ h₂ -
  · exact absurd rfl h₁.1
  · exact absurd rfl h₁.1
  · exact absurd rfl h₂.1
  · simp only [List.cons_append, rule, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact foldl_step hR hδ l₂ _ b

end Rule

/-! ### Proposition 2, "only if" -/

section Converse

omit [DecidableEq X] in
theorem claimT (p : X → X → X) {a b c : X} (hac : a ≠ c)
    (m1 : p a b = a ∨ p a b = b) (m2 : p b a = b ∨ p b a = a) (m3 : p b c = b ∨ p b c = c)
    (m4 : p c b = c ∨ p c b = b)
    (s1 : p (p a b) c = p a (p b c)) (s3 : p (p b a) c = p b (p a c))
    (s5 : p (p c a) b = p c (p a b))
    (s6 : p (p c b) a = p c (p b a))
    (hba : ¬(p a b = b ∧ p b a = b)) (hcb : ¬(p b c = c ∧ p c b = c))
    (hca : p a c = c ∧ p c a = c) : False := by
  obtain ⟨hac1, hca1⟩ := hca
  rcases m1 with m1 | m1
  · rw [hca1, m1] at s5
    have h4 : p b c = b := by
      rcases m3 with m3 | m3
      · exact m3
      · exact absurd ⟨m3, s5.trans hca1⟩ hcb
    rw [m1, h4, m1] at s1
    exact hac (s1.symm.trans hac1)
  · have h2 : p b a = a := by
      rcases m2 with m2 | m2
      · exact absurd ⟨m1, m2⟩ hba
      · exact m2
    rw [h2, hac1] at s3
    have h3 : p b c = c := s3.symm
    have h4 : p c b = b := by
      rcases m4 with m4 | m4
      · exact absurd ⟨h3, m4⟩ hcb
      · exact m4
    rw [h4, h2, hca1] at s6
    exact hac s6

omit [DecidableEq X] in
theorem claimC (p : X → X → X) {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (m4 : p c b = c ∨ p c b = b) (s2 : p (p a c) b = p a (p c b))
    (s6 : p (p c b) a = p c (p b a))
    (h1 : p b a = b) (h2 : p a b = a) (h3 : p a c = c) (h4 : p c a = a) : False := by
  have e3 : p c b = b := by
    rcases m4 with m4 | m4
    · rw [h1, m4, h4] at s6; exact (hac s6).elim
    · exact m4
  rw [h3, e3, h2] at s2
  exact hab s2.symm

variable {D : List X → X}

omit [DecidableEq X] in
theorem pair_mem (hD : IsChoice D) {a b : X} (hab : a ≠ b) : D [a, b] = a ∨ D [a, b] = b := by
  simpa using hD _ (pair_isList hab)

omit [DecidableEq X] in
theorem assoc3 (hD : IsChoice D) (h : PI D) {x y z : X} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : D [D [x, y], z] = D [x, D [y, z]] := by
  have e1 := h [x, y] [z] (pair_isList hxy) (isList_singleton z) (by simp [Ne.symm hxz, Ne.symm hyz])
  have e2 := h [x] [y, z] (isList_singleton x) (pair_isList hyz) (by simp [hxy, hxz])
  rw [choice_singleton hD] at e1 e2
  simp only [List.cons_append, List.nil_append] at e1 e2
  rw [← e1, e2]

/-- The weak preference revealed by binary choices: `a ≽ b` unless `b` is
chosen from both orderings of `{a, b}`. -/
def relOf (D : List X → X) (a b : X) : Bool := decide (a = b ∨ ¬ (D [a, b] = b ∧ D [b, a] = b))

/-- The revealed priority indicator: `a` is in a pair where the later
element is chosen in both orders. -/
noncomputable def deltaOf (D : List X → X) (a : X) : Bool := by
  classical exact decide (∃ b, b ≠ a ∧ D [a, b] = b ∧ D [b, a] = a)

theorem relOf_isWeakOrder (hD : IsChoice D) (h : PI D) : IsWeakOrder (relOf D) := by
  constructor
  · intro a b
    by_cases hab : a = b
    · simp [relOf, hab]
    · simp only [relOf, decide_eq_true_eq, hab, false_or, Ne.symm hab]
      by_contra hc
      push Not at hc
      exact hab (hc.2.1.symm.trans hc.1.2)
  · intro a b c hab hbc
    simp only [relOf, decide_eq_true_eq] at hab hbc ⊢
    by_cases hac : a = c
    · exact Or.inl hac
    right
    intro hca
    by_cases hab' : a = b
    · subst hab'
      rcases hbc with e | e
      · exact hac e
      · exact e hca
    by_cases hbc' : b = c
    · subst hbc'
      exact (hab.resolve_left hab') hca
    exact claimT (fun x y => D [x, y]) hac (pair_mem hD hab') (pair_mem hD (Ne.symm hab'))
      (pair_mem hD hbc') (pair_mem hD (Ne.symm hbc'))
      (assoc3 hD h hab' hbc' hac) (assoc3 hD h (Ne.symm hab') hac hbc')
      (assoc3 hD h (Ne.symm hac) hab' (Ne.symm hbc'))
      (assoc3 hD h (Ne.symm hbc') (Ne.symm hab') (Ne.symm hac))
      (hab.resolve_left hab') (hbc.resolve_left hbc') hca

omit [DecidableEq X] in
/-- In a "first" pair (`a` chosen from `[a, b]`, `b` from `[b, a]`), `a` is in
no "last" pair. -/
theorem deltaOf_first (hD : IsChoice D) (h : PI D) {a b : X} (hab : a ≠ b)
    (h1 : D [a, b] = a) (h2 : D [b, a] = b) : deltaOf D a = false := by
  classical
  simp only [deltaOf, decide_eq_false_iff_not]
  rintro ⟨e, hea, h3, h4⟩
  have hbe : b ≠ e := fun hbe => by subst hbe; rw [h1] at h3; exact hab h3
  exact claimC (fun x y => D [x, y]) hab (Ne.symm hea) (pair_mem hD (Ne.symm hbe))
    (assoc3 hD h (Ne.symm hea) (Ne.symm hbe) hab) (assoc3 hD h (Ne.symm hbe) (Ne.symm hab) hea)
    h2 h1 h3 h4

omit [DecidableEq X] in
theorem deltaOf_last {a b : X} (hab : a ≠ b) (h1 : D [a, b] = b) (h2 : D [b, a] = a) :
    deltaOf D a = true := by
  classical
  simp only [deltaOf, decide_eq_true_eq]
  exact ⟨b, Ne.symm hab, h1, h2⟩

theorem deltaOf_classConst (hD : IsChoice D) (h : PI D) : ClassConst (relOf D) (deltaOf D) := by
  intro a b hab hba
  by_cases e : a = b
  · rw [e]
  simp only [relOf, decide_eq_true_eq, e, false_or, Ne.symm e] at hab hba
  rcases pair_mem hD e with h1 | h1 <;> rcases pair_mem hD (Ne.symm e) with h2 | h2
  · rw [deltaOf_first hD h e h1 h2, deltaOf_first hD h (Ne.symm e) h2 h1]
  · exact absurd ⟨h2, h1⟩ hba
  · exact absurd ⟨h1, h2⟩ hab
  · rw [deltaOf_last e h1 h2, deltaOf_last (Ne.symm e) h2 h1]

/-- Binary choices are `step` for the revealed `R` and `δ`. -/
theorem pair_eq_step (hD : IsChoice D) (h : PI D) {c x : X} (hcx : c ≠ x) :
    D [c, x] = step (relOf D) (deltaOf D) c x := by
  rcases pair_mem hD hcx with h1 | h1 <;> rcases pair_mem hD (Ne.symm hcx) with h2 | h2
  · -- first pair: indifferent, ties to the earlier
    have := deltaOf_first hD h (Ne.symm hcx) h2 h1
    simp [step, relOf, hcx, Ne.symm hcx, h1, h2, this]
  · -- `c ≻ x`
    simp [step, relOf, hcx, Ne.symm hcx, h1, h2]
  · -- `x ≻ c`
    simp [step, relOf, hcx, Ne.symm hcx, h1, h2]
  · -- last pair
    have := deltaOf_last (Ne.symm hcx) h2 h1
    simp [step, relOf, hcx, Ne.symm hcx, h1, h2, this]

theorem eq_foldl (hD : IsChoice D) (h : PI D) (a : X) :
    ∀ l : List X, IsList (a :: l) → D (a :: l) = l.foldl (step (relOf D) (deltaOf D)) a := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; exact choice_singleton hD a
  | append_singleton l x ih =>
    intro hL
    have hL' : IsList ((a :: l) ++ [x]) := by simpa using hL
    obtain ⟨h₁, h₂, hdis⟩ := isList_append hL' (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    have e := h _ _ h₁ h₂ hdis
    rw [choice_singleton hD] at e
    have hne : D (a :: l) ≠ x := fun he => hdis (he ▸ hD _ h₁) (List.mem_singleton_self x)
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih h₁, ← pair_eq_step hD h hne,
      ← e]
    simp

/-- **Rubinstein–Salant Proposition 2, "only if"**: a choice function from
lists with partition independence maximizes a complete transitive
preference, breaking ties within each indifference class always in favour
of the first or always of the last maximal element. -/
theorem exists_rule_of_pi [Inhabited X] (hD : IsChoice D) (h : PI D) :
    ∃ (R : X → X → Bool) (δ : X → Bool), IsWeakOrder R ∧ ClassConst R δ ∧
      ∀ L, IsList L → D L = rule R δ L := by
  refine ⟨relOf D, deltaOf D, relOf_isWeakOrder hD h, deltaOf_classConst hD h, ?_⟩
  rintro (_ | ⟨a, l⟩) hL
  · exact absurd rfl hL.1
  · exact eq_foldl hD h a l hL

/-- **Rubinstein–Salant Proposition 2** (existence part): PI holds iff `D` is
some `D_{≽,δ}`. -/
theorem pi_iff_rule [Inhabited X] (hD : IsChoice D) :
    PI D ↔ ∃ (R : X → X → Bool) (δ : X → Bool), IsWeakOrder R ∧ ClassConst R δ ∧
      ∀ L, IsList L → D L = rule R δ L := by
  refine ⟨exists_rule_of_pi hD, ?_⟩
  rintro ⟨R, δ, hR, hδ, he⟩ L₁ L₂ h₁ h₂ hdis
  have hL : IsList (L₁ ++ L₂) :=
    ⟨by simp [h₁.1], List.nodup_append.2 ⟨h₁.2, h₂.2, fun a ha b hb hab => hdis ha (hab ▸ hb)⟩⟩
  have hne : D L₁ ≠ D L₂ := fun e => hdis (hD _ h₁) (e ▸ hD _ h₂)
  rw [he _ hL, he _ h₁, he _ h₂, he _ (pair_isList (by rwa [← he _ h₁, ← he _ h₂]))]
  exact pi_rule hR hδ L₁ L₂ h₁ h₂ hdis

end Converse

/-! ### Examples -/

/-- Choose the first element of the list. -/
def first [Inhabited X] (L : List X) : X := L.headD default

omit [DecidableEq X] in
theorem first_isChoice [Inhabited X] : IsChoice (first (X := X)) := by
  rintro (_ | ⟨a, l⟩) hL
  · exact absurd rfl hL.1
  · simp [first]

omit [DecidableEq X] in
/-- Non-vacuity: "choose the first element" has partition independence (all
alternatives indifferent, ties to the first), so PI is weaker than
rationality. -/
theorem pi_first [Inhabited X] : PI (first (X := X)) := by
  rintro (_ | ⟨a, l₁⟩) L₂ h₁ - -
  · exact absurd rfl h₁.1
  · simp [first]

omit [DecidableEq X] in
/-- "Choose the first element" is `D_{≽,δ}` with all alternatives indifferent
and ties broken in favour of the first. -/
theorem first_eq_rule [Inhabited X] {L : List X} (hL : L ≠ []) :
    first L = rule (fun _ _ => true) (fun _ => false) L := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a l =>
    simp only [first, List.headD_cons, rule]
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.foldl_cons]; simpa [step] using ih

omit [DecidableEq X] in
/-- "Choose the first element" is not rationalizable (RS's definition): with
two distinct alternatives no asymmetric `P` makes the chosen element
`P`-better than every other element of every list. -/
theorem first_not_rational [Inhabited X] {a b : X} (hab : a ≠ b) :
    ¬ ∃ P : X → X → Prop, (∀ x y, P x y → ¬ P y x) ∧
      ∀ L, IsList L → ∀ y ∈ L, y ≠ first L → P (first L) y := by
  rintro ⟨P, hasym, hP⟩
  have h1 := hP [a, b] (pair_isList hab) b (by simp) (by simpa [first] using Ne.symm hab)
  have h2 := hP [b, a] (pair_isList (Ne.symm hab)) a (by simp) (by simpa [first] using hab)
  exact hasym _ _ (by simpa [first] using h1) (by simpa [first] using h2)

/-- **Satisficing** (Simon; RS Example 2): satisfactory alternatives (`S a`)
are all indifferent and better than unsatisfactory ones; the first
satisfactory element is chosen, and if there is none, the last element. -/
def satisficing [Inhabited X] (S : X → Bool) : List X → X :=
  rule (fun a b => S a || !S b) (fun a => !S a)

omit [DecidableEq X] in
theorem satisficing_weakOrder (S : X → Bool) : IsWeakOrder (fun a b => S a || !S b) := by
  constructor
  · intro a b; cases ha : S a <;> cases hb : S b <;> simp [ha, hb]
  · intro a b c; cases ha : S a <;> cases hb : S b <;> cases hc : S c <;> simp [ha, hb, hc]

omit [DecidableEq X] in
theorem pi_satisficing [Inhabited X] (S : X → Bool) : PI (satisficing S) := by
  apply pi_rule (satisficing_weakOrder S)
  intro a b; cases ha : S a <;> cases hb : S b <;> simp [ha, hb]

omit [DecidableEq X] in
/-- A satisficer picks a satisfactory element whenever the list has one. -/
theorem satisficing_satisfactory [Inhabited X] (S : X → Bool) {L : List X} (hL : L ≠ [])
    {y : X} (hy : y ∈ L) (hSy : S y) : S (satisficing S L) := by
  have := rule_isMax (R := fun a b => S a || !S b) (δ := fun a => !S a)
    (satisficing_weakOrder S) hL y hy
  simpa [hSy, satisficing] using this

end Econ.ChoiceLists
