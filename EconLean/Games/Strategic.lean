/-
# Strategic-form games, Nash equilibrium and iterated strict dominance

MWG Ch. 8 (§8.B, §8.D). A game in strategic (normal) form has a set of players `I`,
a strategy set `S i` for each player, and payoffs `u i : (∀ j, S j) → ℝ` on strategy
profiles. Changing player `i`'s strategy in profile `s` to `t` is
`Function.update s i t`, written `(t, s₋ᵢ)` in MWG.

* `IsNash u s`: no player gains by a unilateral deviation (MWG Def. 8.D.1).
* `IsStrictlyDominant`, `IsDominant`: strictly and weakly dominant strategies (MWG Defs.
  8.B.4–8.B.5); a profile of dominant strategies is a Nash equilibrium.
* `StrictlyDominated u R i t`: within the surviving sets `R`, some other `t' ∈ R i`
  does strictly better than `t` against every surviving opponent profile
  (MWG Def. 8.B.1, relativized to `R`).
* `isd u n`: the strategies surviving `n` rounds of simultaneous deletion of strictly
  dominated pure strategies (MWG §8.B).

Main results:
* `isNash_iff_bestResponse`: Nash ⟺ everybody best-responds.
* `isNash_mem_isd`: Nash strategies survive every round of iterated deletion.
* `isNash_of_isd_singleton`: in a finite game, if iterated deletion leaves a single
  profile, that profile is a Nash equilibrium, and (with `isNash_mem_isd`) the unique one.

Here the dominating strategy is pure. Dominance by mixed strategies (MWG §8.D), which
deletes more, is `isdMixed` in `Rationalizability.lean`. Strategy sets are arbitrary types;
the results about elimination assume finite strategy sets where needed.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ

open Function

variable {I : Type*} [DecidableEq I] {S : I → Type*}

/-- **Best response** (MWG Def. 8.D.2): `t` is a best response for `i` to the others'
strategies in `s`. (The value `s i` is ignored.) -/
def IsBestResponse (u : I → (∀ j, S j) → ℝ) (i : I) (s : ∀ j, S j) (t : S i) : Prop :=
  ∀ t' : S i, u i (update s i t') ≤ u i (update s i t)

/-- **Nash equilibrium** in pure strategies (MWG Def. 8.D.1). -/
def IsNash (u : I → (∀ j, S j) → ℝ) (s : ∀ j, S j) : Prop :=
  ∀ i (t : S i), u i (update s i t) ≤ u i s

/-- Nash ⟺ each player's strategy is a best response to the others'. -/
theorem isNash_iff_bestResponse (u : I → (∀ j, S j) → ℝ) (s : ∀ j, S j) :
    IsNash u s ↔ ∀ i, IsBestResponse u i s (s i) := by
  simp only [IsNash, IsBestResponse, update_eq_self]

/-- **Strictly dominant strategy** (MWG Def. 8.B.4): `t` does strictly better than any
other strategy against every profile of the others. -/
def IsStrictlyDominant (u : I → (∀ j, S j) → ℝ) (i : I) (t : S i) : Prop :=
  ∀ (s : ∀ j, S j) (t' : S i), t' ≠ t → u i (update s i t') < u i (update s i t)

/-- **Weakly dominant strategy** (MWG Def. 8.B.5): `t` does at least as well as any other
strategy against every profile of the others, and strictly better against some profile. -/
def IsDominant (u : I → (∀ j, S j) → ℝ) (i : I) (t : S i) : Prop :=
  (∀ (s : ∀ j, S j) (t' : S i), u i (update s i t') ≤ u i (update s i t)) ∧
    ∀ t' : S i, t' ≠ t → ∃ s : ∀ j, S j, u i (update s i t') < u i (update s i t)

/-- A strictly dominant strategy is weakly dominant (when the other players have some
strategy profile). -/
theorem IsStrictlyDominant.isDominant [Nonempty (∀ j, S j)] {u : I → (∀ j, S j) → ℝ}
    {i : I} {t : S i} (h : IsStrictlyDominant u i t) : IsDominant u i t := by
  refine ⟨fun s t' => ?_, fun t' ht' => ⟨Classical.arbitrary _, h _ t' ht'⟩⟩
  by_cases ht : t' = t
  · rw [ht]
  · exact (h s t' ht).le

/-- A profile of (weakly) dominant strategies is a Nash equilibrium (MWG §8.B). -/
theorem isNash_of_dominant {u : I → (∀ j, S j) → ℝ} {s : ∀ j, S j}
    (h : ∀ i, IsDominant u i (s i)) : IsNash u s := fun i t => by
  simpa using (h i).1 s t

/-- `t` is **strictly dominated** for `i` relative to the surviving sets `R`: some
surviving `t'` does strictly better against every surviving profile of the others. -/
def StrictlyDominated (u : I → (∀ j, S j) → ℝ) (R : ∀ j, Set (S j)) (i : I) (t : S i) :
    Prop :=
  ∃ t' ∈ R i, ∀ s : ∀ j, S j, (∀ j, s j ∈ R j) → u i (update s i t) < u i (update s i t')

/-- One round of simultaneous deletion of strictly dominated strategies. -/
def isdStep (u : I → (∀ j, S j) → ℝ) (R : ∀ j, Set (S j)) : ∀ j, Set (S j) :=
  fun i => {t | t ∈ R i ∧ ¬ StrictlyDominated u R i t}

/-- Strategies surviving `n` rounds of iterated strict dominance, starting from all. -/
def isd (u : I → (∀ j, S j) → ℝ) : ℕ → ∀ j, Set (S j)
  | 0 => fun _ => Set.univ
  | n + 1 => isdStep u (isd u n)

theorem isd_succ_subset (u : I → (∀ j, S j) → ℝ) (n : ℕ) (i : I) :
    isd u (n + 1) i ⊆ isd u n i := fun _ ht => ht.1

/-- Surviving sets shrink. -/
theorem isd_antitone (u : I → (∀ j, S j) → ℝ) (i : I) : Antitone fun n => isd u n i :=
  antitone_nat_of_succ_le fun n => isd_succ_subset u n i

/-- **Nash equilibria survive iterated strict dominance.** Every component of a pure
Nash equilibrium survives every round. -/
theorem isNash_mem_isd {u : I → (∀ j, S j) → ℝ} {s : ∀ j, S j} (hs : IsNash u s) :
    ∀ n i, s i ∈ isd u n i := by
  intro n
  induction n with
  | zero => intro i; trivial
  | succ n ih =>
    intro i
    refine ⟨ih i, fun ⟨t', _, hdom⟩ => ?_⟩
    -- `s i` is beaten by `t'` against `s₋ᵢ` itself, contradicting `s` being Nash.
    have := hdom s ih
    rw [update_eq_self] at this
    exact absurd (hs i t') (not_le.2 this)

/-- **Dominance solvability implies Nash.** In a finite game (each `S i` a nonempty
finite set), if after some round `n` the only surviving strategy of each player `i` is
`s i`, then `s` is a Nash equilibrium. Combined with `isNash_mem_isd`, it is the unique
one. -/
theorem isNash_of_isd_singleton [∀ i, Fintype (S i)] {u : I → (∀ j, S j) → ℝ}
    {s : ∀ j, S j} {n : ℕ} (hn : ∀ i, isd u n i = {s i}) : IsNash u s := by
  intro i t
  by_contra hlt
  push Not at hlt
  -- Take a best response `b` to `s₋ᵢ` over all of `S i`.
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (fun t' => u i (update s i t'))
    ⟨t, Finset.mem_univ t⟩
  have hbs : u i s < u i (update s i b) := hlt.trans_le (hb t (Finset.mem_univ t))
  have hbne : b ≠ s i := fun h => by rw [h, update_eq_self] at hbs; exact lt_irrefl _ hbs
  rcases n with _ | n
  · -- Round 0 keeps everything, so it cannot be a singleton missing `b`.
    have : b ∈ isd u 0 i := trivial
    rw [hn i] at this; exact hbne this
  -- `b` is deleted by round `n + 1`; let `k + 1` be the first round where it is gone.
  have hbn : b ∉ isd u (n + 1) i := by rw [hn i]; exact hbne
  have hex : ∃ k, b ∉ isd u (k + 1) i := ⟨n, hbn⟩
  classical
  have hk : b ∉ isd u (Nat.find hex + 1) i := Nat.find_spec hex
  have hkn : Nat.find hex ≤ n := Nat.find_min' hex hbn
  have hbk : b ∈ isd u (Nat.find hex) i := by
    rcases hk' : Nat.find hex with _ | k'
    · trivial
    · have := Nat.find_min hex (show k' < Nat.find hex by omega)
      exact not_not.1 this
  -- So `b` is strictly dominated relative to round `k`, at which `s` still survives.
  have hdom : StrictlyDominated u (isd u (Nat.find hex)) i b := by
    by_contra hnd; exact hk ⟨hbk, hnd⟩
  obtain ⟨t', _, hlt'⟩ := hdom
  have hsk : ∀ j, s j ∈ isd u (Nat.find hex) j := fun j =>
    isd_antitone u j (show Nat.find hex ≤ n + 1 by omega) (show s j ∈ isd u (n + 1) j by rw [hn j]; rfl)
  have := hlt' s hsk
  -- `t'` does strictly better than the best response `b` against `s₋ᵢ`: contradiction.
  exact absurd (hb t' (Finset.mem_univ _)) (not_le.2 (by simpa using this))

/-! ### Witness: the prisoners' dilemma

Two players, strategies `true` = confess, `false` = stay quiet. Confessing strictly
dominates, one round of deletion leaves `(confess, confess)`, and that is the unique
Nash equilibrium. -/

/-- Prisoners' dilemma payoffs (MWG Ex. 8.B.1 up to relabelling): quiet/quiet gives `-1`,
confess/confess gives `-5`; confessing against quiet gives `0`, the sucker gets `-10`. -/
def pdPayoff (i : Bool) (s : Bool → Bool) : ℝ :=
  match s i, s (!i) with
  | true, true => -5
  | true, false => 0
  | false, true => -10
  | false, false => -1

example : IsNash pdPayoff (fun _ => true) ∧
    ∀ i, isd pdPayoff 1 i = {true} := by
  have hnash : IsNash pdPayoff (fun _ => true) := by
    intro i t; cases i <;> cases t <;> simp [pdPayoff, update] <;> norm_num
  refine ⟨hnash, fun i => ?_⟩
  ext t
  simp only [isd, isdStep, Set.mem_univ, true_and, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra ht
    simp only [Bool.not_eq_true] at ht
    subst ht
    exact h ⟨true, trivial, fun s _ => by
      cases i <;> cases hs : s (!false) <;> cases hs' : s (!true) <;>
        simp_all [pdPayoff, update] <;> norm_num⟩
  · rintro rfl ⟨t', -, h⟩
    have := h (fun _ => true) (fun _ => trivial)
    cases i <;> cases t' <;> simp [pdPayoff, update] at this <;> norm_num at this

end Econ
