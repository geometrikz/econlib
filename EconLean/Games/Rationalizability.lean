/-
# Rationalizability

MWG §8.C (Defs. 8.C.1–8.C.3, Props. 8.C.1–8.C.2); Bernheim (1984), Pearce (1984). A
strategy is **rationalizable** if it is a best response to some belief about the others,
where those others' strategies are themselves best responses to beliefs, and so on. We use
MWG's independent beliefs: a belief of player `i` is a profile of mixed strategies of the
others.

`IsBRSet u R` says every strategy in `R i` is a best response to a belief supported on
the others' sets `R j` (a "best-response set"). The rationalizable strategies are the
union of all best-response sets (the largest one).

Main results:
* `isBRSet_support`: the supports of a mixed Nash equilibrium form a best-response set, so
  every strategy played in a Nash equilibrium is rationalizable (MWG Prop. 8.C.1).
* `exists_rationalizable`: every player has a rationalizable strategy.
* `IsBRSet.subset_isd`, `IsBRSet.subset_isdMixed`: rationalizable strategies survive
  iterated deletion of strictly dominated strategies, with dominators pure (`isd`) or mixed
  as in MWG §8.D (`isdMixed`) (MWG Prop. 8.C.2, one inclusion). The converse (two-player
  games, via the separating hyperplane / minimax theorem) is not formalized; with pure
  dominators it is false, and for three or more players MWG's independent beliefs make it
  fail too.
-/
module

public import EconLean.Games.Mixed

@[expose] public section

namespace Econ

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- `t` is a best response for `i` to the belief `σ` (only `σ j`, `j ≠ i`, matter). -/
def IsBestResponseTo (u : I → (∀ j, S j) → ℝ) (σ : ∀ i, S i → ℝ) (i : I) (t : S i) : Prop :=
  ∀ t', pureDev u σ i t' ≤ pureDev u σ i t

/-- `R` is a **best-response set**: every `t ∈ R i` is a best response to some belief
whose support lies in `R j` for every opponent `j`. -/
def IsBRSet (u : I → (∀ j, S j) → ℝ) (R : ∀ j, Set (S j)) : Prop :=
  ∀ i, ∀ t ∈ R i, ∃ σ : ∀ j, S j → ℝ, IsMixedProfile σ ∧
    (∀ j, j ≠ i → ∀ x, 0 < σ j x → x ∈ R j) ∧ IsBestResponseTo u σ i t

/-- **Rationalizable strategy** (MWG Def. 8.C.3): it belongs to some best-response set. -/
def Rationalizable (u : I → (∀ j, S j) → ℝ) (i : I) (t : S i) : Prop :=
  ∃ R, IsBRSet u R ∧ t ∈ R i

/-- **Nash ⟹ rationalizable** (MWG Prop. 8.C.1): the supports of a mixed Nash equilibrium
form a best-response set. -/
theorem isBRSet_support {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) : IsBRSet u fun j => {x | 0 < σ j x} := by
  intro i t ht
  refine ⟨σ, h.1, fun j _ x hx => hx, fun t' => ?_⟩
  rw [h.eq_of_pos ht]
  exact (isMixedNash_iff_pure h.1).1 h i t'

theorem rationalizable_of_isMixedNash {u : I → (∀ j, S j) → ℝ} {σ : ∀ i, S i → ℝ}
    (h : IsMixedNash u σ) {i : I} {t : S i} (ht : 0 < σ i t) : Rationalizable u i t :=
  ⟨_, isBRSet_support h, ht⟩

/-- Every player in a finite game has a rationalizable strategy. -/
theorem exists_rationalizable [∀ i, Nonempty (S i)] (u : I → (∀ j, S j) → ℝ) (i : I) :
    ∃ t, Rationalizable u i t := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNash u
  obtain ⟨t, ht⟩ : ∃ t, 0 < σ i t := by
    by_contra h
    push Not at h
    have : ∑ t, σ i t ≤ 0 := Finset.sum_nonpos fun t _ => h t
    linarith [(hσ.1 i).2]
  exact ⟨t, rationalizable_of_isMixedNash hσ ht⟩

omit [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- A profile drawn with positive probability from `σ` has every opponent's component in
the support of that opponent's mixture. -/
theorem mem_of_profileProb_pos {σ : ∀ i, S i → ℝ} {s : ∀ i, S i}
    (hs : 0 < profileProb σ s) (hσ : IsMixedProfile σ) (j : I) : 0 < σ j (s j) := by
  rcases ((hσ j).1 (s j)).eq_or_lt with h0 | h0
  · exfalso
    have : profileProb σ s = 0 :=
      Finset.prod_eq_zero (mem_univ j) h0.symm
    linarith
  · exact h0

/-- **Rationalizable strategies survive iterated strict dominance** (MWG Prop. 8.C.2,
the inclusion "rationalizable ⊆ surviving"). Every best-response set lies inside the
strategies surviving every round. -/
theorem IsBRSet.subset_isd {u : I → (∀ j, S j) → ℝ} {R : ∀ j, Set (S j)}
    (hR : IsBRSet u R) : ∀ n i, R i ⊆ isd u n i := by
  intro n
  induction n with
  | zero => intro i t _; trivial
  | succ n ih =>
    intro i t ht
    refine ⟨ih i ht, ?_⟩
    rintro ⟨t', -, hdom⟩
    obtain ⟨σ, hσ, hsupp, hbr⟩ := hR i t ht
    -- Averaging the strict dominance over the belief gives `t'` a strictly higher payoff.
    have key : ∀ s, 0 < profileProb σ s → u i (update s i t) < u i (update s i t') := by
      intro s hs
      have := hdom (update s i t) fun j => by
        by_cases hj : j = i
        · subst hj; simpa using ih j ht
        · rw [update_of_ne hj]
          exact ih j (hsupp j hj _ (mem_of_profileProb_pos hs hσ j))
      simpa using this
    have hlt : pureDev u σ i t < pureDev u σ i t' := by
      rw [pureDev_eq_sum_update u (hσ i), pureDev_eq_sum_update u (hσ i)]
      have hne : ∃ s, 0 < profileProb σ s := by
        by_contra h
        push Not at h
        have : ∑ s, profileProb σ s ≤ 0 := Finset.sum_nonpos fun s _ => h s
        linarith [sum_profileProb hσ]
      obtain ⟨s0, hs0⟩ := hne
      refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, mem_univ _, ?_⟩
      · rcases (profileProb_nonneg hσ s).eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact (mul_lt_mul_of_pos_left (key s h0) h0).le
      · exact mul_lt_mul_of_pos_left (key s0 hs0) hs0
    exact absurd (hbr t') (not_le.2 hlt)

/-- Rationalizable strategies survive iterated strict dominance. -/
theorem Rationalizable.mem_isd {u : I → (∀ j, S j) → ℝ} {i : I} {t : S i}
    (h : Rationalizable u i t) (n : ℕ) : t ∈ isd u n i :=
  let ⟨_, hR, ht⟩ := h
  hR.subset_isd n i ht

/-! ### Dominance by mixed strategies (MWG §8.D) -/

/-- `t` is **strictly dominated by a mixed strategy** relative to the surviving sets `R`:
some lottery `τ` over `i`'s surviving strategies does strictly better than `t` against every
surviving profile of the others (MWG Def. 8.D.3, relativized to `R`). -/
def StrictlyDominatedMixed (u : I → (∀ j, S j) → ℝ) (R : ∀ j, Set (S j)) (i : I) (t : S i) :
    Prop :=
  ∃ τ ∈ lotteries (S i), (∀ x, 0 < τ x → x ∈ R i) ∧
    ∀ s : ∀ j, S j, (∀ j, s j ∈ R j) → u i (update s i t) < ∑ x, τ x * u i (update s i x)

/-- Strategies surviving `n` rounds of iterated deletion of strategies strictly dominated by
mixed strategies. -/
def isdMixed (u : I → (∀ j, S j) → ℝ) : ℕ → ∀ j, Set (S j)
  | 0 => fun _ => Set.univ
  | n + 1 => fun i => {t | t ∈ isdMixed u n i ∧ ¬ StrictlyDominatedMixed u (isdMixed u n) i t}

/-- **Rationalizable strategies survive iterated deletion of mixed-dominated strategies**
(MWG Prop. 8.C.2, the inclusion "rationalizable ⊆ surviving", with MWG's mixed dominance). -/
theorem IsBRSet.subset_isdMixed {u : I → (∀ j, S j) → ℝ} {R : ∀ j, Set (S j)}
    (hR : IsBRSet u R) : ∀ n i, R i ⊆ isdMixed u n i := by
  intro n
  induction n with
  | zero => intro i t _; trivial
  | succ n ih =>
    intro i t ht
    refine ⟨ih i ht, ?_⟩
    rintro ⟨τ, hτ, -, hdom⟩
    obtain ⟨σ, hσ, hsupp, hbr⟩ := hR i t ht
    have key : ∀ s, 0 < profileProb σ s →
        u i (update s i t) < ∑ x, τ x * u i (update s i x) := by
      intro s hs
      have := hdom (update s i t) fun j => by
        by_cases hj : j = i
        · subst hj; simpa using ih j ht
        · rw [update_of_ne hj]
          exact ih j (hsupp j hj _ (mem_of_profileProb_pos hs hσ j))
      simpa using this
    -- Average over the belief: `dev(t) < ∑ₓ τₓ dev(x) ≤ dev(t)`.
    have hlt : pureDev u σ i t < ∑ x, τ x * pureDev u σ i x := by
      simp only [pureDev_eq_sum_update u (hσ i), Finset.mul_sum]
      rw [Finset.sum_comm]
      obtain ⟨s0, hs0⟩ : ∃ s, 0 < profileProb σ s := by
        by_contra h
        push Not at h
        have : ∑ s, profileProb σ s ≤ 0 := Finset.sum_nonpos fun s _ => h s
        linarith [sum_profileProb hσ]
      refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, mem_univ _, ?_⟩
      · have e : ∑ x, τ x * (profileProb σ s * u i (update s i x)) =
            profileProb σ s * ∑ x, τ x * u i (update s i x) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]
        rcases (profileProb_nonneg hσ s).eq_or_lt with h0 | h0
        · rw [← h0, zero_mul, zero_mul]
        · exact (mul_lt_mul_of_pos_left (key s h0) h0).le
      · have e : ∑ x, τ x * (profileProb σ s0 * u i (update s0 i x)) =
            profileProb σ s0 * ∑ x, τ x * u i (update s0 i x) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]
        exact mul_lt_mul_of_pos_left (key s0 hs0) hs0
    have hle : ∑ x, τ x * pureDev u σ i x ≤ pureDev u σ i t := by
      calc ∑ x, τ x * pureDev u σ i x ≤ ∑ x, τ x * pureDev u σ i t :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hbr x) (hτ.1 x)
        _ = pureDev u σ i t := by rw [← Finset.sum_mul, hτ.2, one_mul]
    linarith

/-- Rationalizable strategies survive iterated deletion of mixed-dominated strategies. -/
theorem Rationalizable.mem_isdMixed {u : I → (∀ j, S j) → ℝ} {i : I} {t : S i}
    (h : Rationalizable u i t) (n : ℕ) : t ∈ isdMixed u n i :=
  let ⟨_, hR, ht⟩ := h
  hR.subset_isdMixed n i ht

end Econ
