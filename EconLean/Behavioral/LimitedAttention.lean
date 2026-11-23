/-
# Revealed attention (Masatlioglu–Nakajima–Ozbay 2012)

Reference. Y. Masatlioglu, D. Nakajima and E. Ozbay (2012), "Revealed
Attention", *AER* 102(5), Definitions 1–2, Lemma 1 and Theorem 1.

A decision maker facing menu `S` considers only `Γ S ⊆ S` and picks the best
considered alternative for a strict ranking `u` (an injective `X → ℕ`). MNO
take `X` finite, where every strict linear order has this form; on an
uncountable `X` no such `u` exists and `IsCLA` is never satisfied. `Γ` is an **attention
filter**: removing an alternative that is not considered does not change what
is considered.

**Results.**
* `revealed_pref` (MNO Lemma 1): if removing `x` from `T` changes the choice
  and `x` was not chosen, then `x` was considered and the choice from `T`
  is revealed strictly better than `x`.
* `warpLA_of_cla` (MNO Theorem 1, necessity): a choice with limited attention
  satisfies WARP with limited attention: in every menu `S` there is an
  alternative `x*` (the best one) such that whenever removing `x*` from a
  larger menu `T` changes a choice that lies in `S`, the choice was `x*`.
* `example_cla`, `example_violates_warp`: limited attention explains WARP
  violations: a choice function that picks `a` from `{a, b, c}` and `b` from
  `{a, b}` violates WARP (`¬ WARP cex`) but is a choice with limited attention (the
  decision maker overlooks `b` in the larger menu).

* `cla_of_warpLA`, `cla_iff_warpLA` (MNO Theorem 1, sufficiency): on a
  finite set, WARP(LA) implies a choice with limited attention, represented
  with MNO's revealed attention filter `revealedAttention`. The ranking is
  built by repeatedly putting on top an element that no other element of the
  remaining menu is revealed preferred to (`exists_undominated`,
  `exists_rank`); attention is `Γ(S) = {c(S)} ∪ {x ∈ S : c(S) P x}`.
* `revPref_ranked`: every representation ranks `x` above `y` whenever
  `x P y` (MNO Theorem 2, the "revealed" half).
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Econ

namespace LimitedAttention

variable {X : Type*} [DecidableEq X]

/-- An attention filter (MNO Definition 1). -/
def IsAttentionFilter (Γ : Finset X → Finset X) : Prop :=
  ∀ S : Finset X, S.Nonempty →
    Γ S ⊆ S ∧ (Γ S).Nonempty ∧ ∀ x ∈ S, x ∉ Γ S → Γ (S.erase x) = Γ S

/-- `c` is a choice with limited attention (MNO Definition 2): it picks the
`u`-best considered alternative, for an injective ranking `u` and an attention
filter `Γ`. -/
def IsCLA (c : Finset X → X) (u : X → ℕ) (Γ : Finset X → Finset X) : Prop :=
  Function.Injective u ∧ IsAttentionFilter Γ ∧
    ∀ S : Finset X, S.Nonempty → c S ∈ Γ S ∧ ∀ y ∈ Γ S, u y ≤ u (c S)

/-- WARP with limited attention (MNO Definition 3). -/
def WARPLA (c : Finset X → X) : Prop :=
  ∀ S : Finset X, S.Nonempty → ∃ x ∈ S, ∀ T : Finset X, x ∈ T → c T ∈ S →
    c T ≠ c (T.erase x) → c T = x

variable {c : Finset X → X} {u : X → ℕ} {Γ : Finset X → Finset X}

/-- If removing `x` from `T` changes the choice, `x` was considered. -/
theorem mem_attention_of_change (h : IsCLA c u Γ) {T : Finset X} {x : X} (hx : x ∈ T)
    (hT : (T.erase x).Nonempty) (hch : c T ≠ c (T.erase x)) : x ∈ Γ T := by
  by_contra hxΓ
  obtain ⟨hu, hΓ, hc⟩ := h
  have hTn : T.Nonempty := ⟨x, hx⟩
  have e := (hΓ T hTn).2.2 x hx hxΓ
  have h1 := hc T hTn
  have h2 := hc (T.erase x) hT
  rw [e] at h2
  exact hch (hu (le_antisymm (h2.2 _ h1.1) (h1.2 _ h2.1)))

/-- **Revealed preference (MNO Lemma 1).** If `x ∈ T` is not chosen from `T`
but its removal changes the choice, the choice from `T` is ranked strictly
above `x`. -/
theorem revealed_pref (h : IsCLA c u Γ) {T : Finset X} {x : X} (hx : x ∈ T)
    (hxc : c T ≠ x) (hch : c T ≠ c (T.erase x)) : u x < u (c T) := by
  have hT : (T.erase x).Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    have hcT := (h.2.2 T ⟨x, hx⟩).1
    have : c T ∈ T := (h.2.1 T ⟨x, hx⟩).1 hcT
    have : c T ∈ T.erase x := Finset.mem_erase.2 ⟨hxc, this⟩
    simp [hT] at this
  have hxΓ := mem_attention_of_change h hx hT hch
  exact lt_of_le_of_ne ((h.2.2 T ⟨x, hx⟩).2 x hxΓ) fun e => hxc (h.1 e).symm

/-- **MNO Theorem 1 (necessity).** A choice with limited attention satisfies
WARP(LA). -/
theorem warpLA_of_cla (h : IsCLA c u Γ) : WARPLA c := by
  intro S hS
  obtain ⟨x, hxS, hxmax⟩ := S.exists_max_image u hS
  refine ⟨x, hxS, fun T hxT hcS hch => ?_⟩
  by_contra hne
  have h1 := revealed_pref h hxT hne hch
  have h2 := hxmax _ hcS
  omega

/-! ### Sufficiency (MNO Theorem 1, converse) -/

/-- MNO's revealed preference: `x P y` iff for some menu `T ∋ y`, `x` is chosen
from `T` and removing `y` changes the choice. -/
def RevPref (c : Finset X → X) (x y : X) : Prop :=
  x ≠ y ∧ ∃ T : Finset X, y ∈ T ∧ c T = x ∧ c T ≠ c (T.erase y)

/-- Under WARP(LA), every nonempty menu has an element that no other element
of the menu is revealed preferred to. -/
theorem exists_undominated (h : WARPLA c) {S : Finset X} (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, ¬ RevPref c y x := by
  obtain ⟨x, hxS, hx⟩ := h S hS
  refine ⟨x, hxS, fun y hy ⟨hyx, T, hxT, hcT, hch⟩ => hyx ?_⟩
  rw [← hcT]; exact hx T hxT (hcT ▸ hy) hch

/-- Under WARP(LA), `P` has a ranking extending it on every menu, built by
repeatedly ranking an undominated element on top. -/
theorem exists_rank (h : WARPLA c) (S : Finset X) :
    ∃ u : X → ℕ, Set.InjOn u S ∧ ∀ x ∈ S, ∀ y ∈ S, RevPref c x y → u y < u x := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨fun _ => 0, by simp, by simp⟩
    obtain ⟨x, hxS, hx⟩ := exists_undominated h hS
    obtain ⟨u', hinj, hu'⟩ := ih (S.erase x) (Finset.erase_ssubset hxS)
    set N := (S.erase x).sup u' + 1
    have hlt : ∀ z ∈ S.erase x, u' z < N := fun z hz =>
      Nat.lt_succ_of_le (Finset.le_sup (f := u') hz)
    refine ⟨fun z => if z = x then N else u' z, ?_, ?_⟩
    · intro a ha b hb hab
      simp only at hab
      by_cases hax : a = x <;> by_cases hbx : b = x
      · rw [hax, hbx]
      · rw [ite_eq_left hax, ite_eq_right hbx] at hab
        exact absurd hab (ne_of_gt (hlt b (Finset.mem_erase.2 ⟨hbx, hb⟩)))
      · rw [ite_eq_right hax, ite_eq_left hbx] at hab
        exact absurd hab (ne_of_lt (hlt a (Finset.mem_erase.2 ⟨hax, ha⟩)))
      · rw [ite_eq_right hax, ite_eq_right hbx] at hab
        exact hinj (Finset.mem_erase.2 ⟨hax, ha⟩) (Finset.mem_erase.2 ⟨hbx, hb⟩) hab
    · intro a ha b hb hab
      by_cases hbx : b = x
      · subst hbx; exact absurd hab (hx a ha)
      by_cases hax : a = x
      · simp only [hax, ite_true, hbx, ite_false]
        exact hlt b (Finset.mem_erase.2 ⟨hbx, hb⟩)
      · simp only [hax, hbx, ite_false]
        exact hu' a (Finset.mem_erase.2 ⟨hax, ha⟩) b (Finset.mem_erase.2 ⟨hbx, hb⟩) hab

/-- MNO's attention filter built from choice data:
`Γ(S) = {c(S)} ∪ {x ∈ S : c(S) P x}`. -/
noncomputable def revealedAttention (c : Finset X → X) (S : Finset X) : Finset X := by
  classical exact insert (c S) (S.filter fun x => RevPref c (c S) x)

/-- **MNO Theorem 1 (sufficiency).** On a finite set of alternatives, a choice
function satisfying WARP(LA) is a choice with limited attention, with MNO's
revealed attention filter `revealedAttention c` as the attention filter. -/
theorem cla_of_warpLA [Fintype X] (hc : ∀ S : Finset X, S.Nonempty → c S ∈ S)
    (h : WARPLA c) : ∃ u, IsCLA c u (revealedAttention c) := by
  classical
  obtain ⟨u, hinj, hu⟩ := exists_rank h Finset.univ
  have hu' : Function.Injective u := fun a b hab =>
    hinj (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  have hΓ : ∀ S, revealedAttention c S = insert (c S) (S.filter fun x => RevPref c (c S) x) :=
    fun S => by unfold revealedAttention; congr
  refine ⟨u, hu', ?_, ?_⟩
  · intro S hS
    refine ⟨?_, ⟨c S, by rw [hΓ]; exact Finset.mem_insert_self _ _⟩, ?_⟩
    · rw [hΓ]; intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hc S hS
      · exact (Finset.mem_filter.1 hz).1
    · intro x hxS hxΓ
      rw [hΓ S] at hxΓ
      rw [hΓ (S.erase x), hΓ S]
      have hxc : x ≠ c S := fun e => hxΓ (e ▸ Finset.mem_insert_self _ _)
      have hnP : ¬ RevPref c (c S) x := fun hP =>
        hxΓ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hxS, hP⟩))
      have hsame : c (S.erase x) = c S := by
        by_contra hne
        exact hnP ⟨Ne.symm hxc, S, hxS, rfl, Ne.symm hne⟩
      rw [hsame]
      ext z
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro (h1 | ⟨⟨-, h2⟩, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h2, h3⟩
      · rintro (h1 | ⟨h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨⟨fun e => hnP (e ▸ h3), h2⟩, h3⟩
  · intro S hS
    refine ⟨by rw [hΓ]; exact Finset.mem_insert_self _ _, fun y hy => ?_⟩
    rw [hΓ] at hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact le_rfl
    · exact (hu _ (Finset.mem_univ _) _ (Finset.mem_univ _) (Finset.mem_filter.1 hy).2).le

/-- **MNO Theorem 1.** On a finite set, a choice function (choosing from each
nonempty menu) is a choice with limited attention iff it satisfies WARP(LA). -/
theorem cla_iff_warpLA [Fintype X] (hc : ∀ S : Finset X, S.Nonempty → c S ∈ S) :
    (∃ u Γ, IsCLA c u Γ) ↔ WARPLA c :=
  ⟨fun ⟨_, _, h⟩ => warpLA_of_cla h, fun h => (cla_of_warpLA hc h).elim fun u hu => ⟨u, _, hu⟩⟩

/-- **Revealed preference is exactly what is identified** (MNO Theorem 2,
one direction): if `x P y`, every limited-attention representation ranks `x`
above `y`. -/
theorem revPref_ranked (h : IsCLA c u Γ) {x y : X} (hP : RevPref c x y) : u y < u x := by
  obtain ⟨hxy, T, hyT, hcT, hch⟩ := hP
  rw [← hcT]
  exact revealed_pref h hyT (hcT ▸ hxy) hch

/-! ### Attention explains WARP violations -/

/-- Attention in the example: everything is considered, except that `1`
(`b`) is overlooked in the full menu `{0, 1, 2}`. -/
def Γex (S : Finset (Fin 3)) : Finset (Fin 3) := if S = Finset.univ then {0, 2} else S

/-- Ranking: `b = 1` best, then `a = 0`, then `c = 2`. -/
def uex : Fin 3 → ℕ := ![1, 2, 0]

/-- The choice: the `uex`-best considered alternative (default `0`). -/
def cex (S : Finset (Fin 3)) : Fin 3 :=
  if S = Finset.univ then 0 else if 1 ∈ S then 1 else if 0 ∈ S then 0 else 2

theorem example_cla : IsCLA cex uex Γex := by
  refine ⟨by decide, ?_, ?_⟩
  · unfold IsAttentionFilter Γex; decide
  · unfold cex Γex uex; decide

/-- The weak axiom of revealed preference for a choice function. -/
def WARP (c : Finset X → X) : Prop :=
  ∀ S T : Finset X, ∀ x y : X, x ≠ y → x ∈ S → y ∈ S → x ∈ T → y ∈ T → c S = x → c T ≠ y

/-- The example violates WARP: `0` is chosen from `{0, 1, 2}` although `1` is
available, and `1` is chosen from `{0, 1}`. -/
theorem example_violates_warp : ¬ WARP cex := fun h =>
  h Finset.univ {0, 1} 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end LimitedAttention

end Econ
