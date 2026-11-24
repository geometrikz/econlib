/-
# Matching with contracts (Hatfield–Milgrom 2005)

Hatfield and Milgrom (2005), *Matching with Contracts*, AER; Fleiner (2003); Aygün and Sönmez
(2013); Hatfield and Kominers (2017). There is a set `X` of contracts, each naming a doctor, a
hospital and terms. We work in the abstract two-sided form of Fleiner and Hatfield–Kominers:
each side is described by one aggregate **choice function** `C : Set X → Set X` with
`C Y ⊆ Y`, with no per-agent structure (in Hatfield–Milgrom the doctors' side is the union of
unit-demand individual choices; that special structure is not encoded or needed here).
The **rejected** contracts are `R Y = Y \ C Y`.

* **Substitutes**: `Y ⊆ Z → R Y ⊆ R Z`: a contract rejected from a smaller set is rejected
  from a larger one.
* **Irrelevance of rejected contracts (IRC)**: if `C Z ⊆ Y ⊆ Z` then `C Y = C Z`. It holds
  whenever the choice comes from preferences; Aygün–Sönmez showed that without it the
  Hatfield–Milgrom fixed-point characterization can fail.
* An allocation `Y` is **stable** if both sides choose all of it (`C_D Y = Y`, `C_H Y = Y`,
  individual rationality), and there is no nonempty set `Z` of new contracts, disjoint from
  `Y`, that both sides would choose from `Y ∪ Z` (no blocking set).

Main results:
* `hm_fixedPoint_stable` (the sufficiency half of HM's fixed-point theorem, with substitutes
  and IRC on both sides as in the abstract version): if `(X_D, X_H)` is a fixed point
  of `F(X_D, X_H) = (X \ R_H(X_H), X \ R_D(X_D))`, then `X_D ∩ X_H` is stable.
* `hmOrderHom`: under substitutes `F` is isotone for the order
  `X_D ⊆ X_D'`, `X_H ⊇ X_H'`.
* `stable_exists`: with substitutes and IRC on both sides a stable allocation exists, obtained
  from the least fixed point of `F` (Tarski). For finite `X` this is the point that the
  generalized deferred acceptance algorithm reaches by iterating `F` from the bottom; the
  algorithm itself, and its termination, are not formalized.

Not formalized: the converse half of the fixed-point theorem (every stable allocation comes
from a fixed point), doctor-optimality of the least fixed point, and the law of aggregate
demand results.
-/
module

public import Mathlib.Order.FixedPoints
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace Econ

open Set OrderDual

variable {X : Type*}

/-- A choice function: it chooses a subset of what it is offered. -/
structure ChoiceFn (X : Type*) where
  /-- The chosen contracts. -/
  C : Set X → Set X
  sub : ∀ Y, C Y ⊆ Y

namespace ChoiceFn

/-- The contracts rejected from `Y`. -/
def R (c : ChoiceFn X) (Y : Set X) : Set X := Y \ c.C Y

/-- **Substitutes**: rejection is monotone. -/
def Substitutes (c : ChoiceFn X) : Prop := ∀ Y Z, Y ⊆ Z → c.R Y ⊆ c.R Z

/-- **Irrelevance of rejected contracts**. -/
def IRC (c : ChoiceFn X) : Prop := ∀ Y Z, c.C Z ⊆ Y → Y ⊆ Z → c.C Y = c.C Z

end ChoiceFn

/-- `Y` is a **stable allocation** for the doctors' choice `cD` and the hospitals' choice `cH`. -/
def IsStableAlloc (cD cH : ChoiceFn X) (Y : Set X) : Prop :=
  cD.C Y = Y ∧ cH.C Y = Y ∧
    ∀ Z : Set X, Z.Nonempty → Disjoint Z Y → Z ⊆ cD.C (Y ∪ Z) → ¬ Z ⊆ cH.C (Y ∪ Z)

/-- The Hatfield–Milgrom map `F(X_D, X_H) = (X \ R_H(X_H), X \ R_D(X_D))`. -/
def hmMap (cD cH : ChoiceFn X) (p : Set X × Set X) : Set X × Set X :=
  ((cH.R p.2)ᶜ, (cD.R p.1)ᶜ)

/-- **Hatfield–Milgrom fixed-point theorem** (sufficiency; with substitutes and IRC on both sides, abstract version of Fleiner and
Hatfield–Kominers). The
intersection of the two sets at a fixed point of `F` is a stable allocation. -/
theorem hm_fixedPoint_stable {cD cH : ChoiceFn X} (hsD : cD.Substitutes) (hsH : cH.Substitutes)
    (hiD : cD.IRC) (hiH : cH.IRC) {XD XH : Set X} (hfix : hmMap cD cH (XD, XH) = (XD, XH)) :
    IsStableAlloc cD cH (XD ∩ XH) := by
  simp only [hmMap, Prod.mk.injEq] at hfix
  obtain ⟨hD, hH⟩ := hfix
  -- the doctors choose `XD ∩ XH` from `XD`, the hospitals choose it from `XH`
  have hCD : cD.C XD = XD ∩ XH := by
    ext x; constructor
    · intro hx
      refine ⟨cD.sub XD hx, ?_⟩
      rw [← hH]; exact fun hr => hr.2 hx
    · rintro ⟨hxD, hxH⟩
      by_contra hn
      rw [← hH] at hxH
      exact hxH ⟨hxD, hn⟩
  have hCH : cH.C XH = XD ∩ XH := by
    ext x; constructor
    · intro hx
      refine ⟨?_, cH.sub XH hx⟩
      rw [← hD]; exact fun hr => hr.2 hx
    · rintro ⟨hxD, hxH⟩
      by_contra hn
      rw [← hD] at hxD
      exact hxD ⟨hxH, hn⟩
  -- contracts outside `XD` lie in `XH`, and vice versa
  have outD : ∀ x, x ∉ XD → x ∈ XH := fun x hx => by
    rw [← hH]; exact fun hr => hx hr.1
  have outH : ∀ x, x ∉ XH → x ∈ XD := fun x hx => by
    rw [← hD]; exact fun hr => hx hr.1
  set Y := XD ∩ XH
  refine ⟨?_, ?_, ?_⟩
  · rw [hiD Y XD (hCD ▸ subset_rfl) inter_subset_left, hCD]
  · rw [hiH Y XH (hCH ▸ subset_rfl) inter_subset_right, hCH]
  · intro Z ⟨z, hz⟩ hdisj hZD hZH
    have hzY : z ∉ Y := fun h => hdisj.ne_of_mem hz h rfl
    by_cases hzD : z ∈ XD
    · -- `z ∈ XD \ XH`: the doctors reject it from `XD`, hence from `Y ∪ (Z ∩ XD)`, hence from `Y ∪ Z`
      have hzH : z ∉ XH := fun h => hzY ⟨hzD, h⟩
      have hsub : Y ∪ (Z ∩ XD) ⊆ XD := union_subset inter_subset_left inter_subset_right
      have hirc := hiD (Y ∪ (Z ∩ XD)) XD (hCD ▸ subset_union_left) hsub
      have hrej : z ∈ cD.R (Y ∪ (Z ∩ XD)) := by
        refine ⟨Or.inr ⟨hz, hzD⟩, ?_⟩
        rw [hirc, hCD]; exact fun h => hzH h.2
      have := hsD _ _ (union_subset_union_right Y inter_subset_left) hrej
      exact this.2 (hZD hz)
    · have hzH : z ∈ XH := outD z hzD
      have hsub : Y ∪ (Z ∩ XH) ⊆ XH := union_subset inter_subset_right inter_subset_right
      have hirc := hiH (Y ∪ (Z ∩ XH)) XH (hCH ▸ subset_union_left) hsub
      have hrej : z ∈ cH.R (Y ∪ (Z ∩ XH)) := by
        refine ⟨Or.inr ⟨hz, hzH⟩, ?_⟩
        rw [hirc, hCH]; exact fun h => hzD h.1
      have := hsH _ _ (union_subset_union_right Y inter_subset_left) hrej
      exact this.2 (hZH hz)

/-- **Isotonicity** (Hatfield–Milgrom 2005): under substitutes `F` is isotone on
`Set X × (Set X)ᵒᵈ` (`X_D` ordered by inclusion, `X_H` by reverse inclusion). -/
def hmOrderHom {cD cH : ChoiceFn X} (hsD : cD.Substitutes) (hsH : cH.Substitutes) :
    Set X × (Set X)ᵒᵈ →o Set X × (Set X)ᵒᵈ where
  toFun p := ((cH.R (ofDual p.2))ᶜ, toDual (cD.R p.1)ᶜ)
  monotone' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨ha, hb⟩
    refine ⟨compl_subset_compl.2 (hsH _ _ hb), ?_⟩
    change (cD.R a')ᶜ ⊆ (cD.R a)ᶜ
    exact compl_subset_compl.2 (hsD _ _ ha)

/-- **Existence of a stable allocation** (Hatfield–Milgrom 2005): with substitutable choice
satisfying IRC on both sides, the least fixed point of `F` yields a stable allocation. -/
theorem stable_exists {cD cH : ChoiceFn X} (hsD : cD.Substitutes) (hsH : cH.Substitutes)
    (hiD : cD.IRC) (hiH : cH.IRC) : ∃ Y, IsStableAlloc cD cH Y := by
  set f := hmOrderHom hsD hsH
  have hfix := f.map_lfp
  refine ⟨(OrderHom.lfp f).1 ∩ ofDual (OrderHom.lfp f).2, hm_fixedPoint_stable hsD hsH hiD hiH ?_⟩
  exact hfix

/-- A choice function that takes the contract `x₀` alone when it is offered, and otherwise
accepts everything offered (a side that values `x₀` above any bundle of other contracts). -/
noncomputable def ChoiceFn.top (x₀ : X) : ChoiceFn X where
  C Y := by classical exact if x₀ ∈ Y then {x₀} else Y
  sub Y := by
    classical
    by_cases h : x₀ ∈ Y
    · simp only [h, ↓reduceIte, singleton_subset_iff]
    · simp only [h, ↓reduceIte, subset_rfl]

/-- Accept everything. -/
def ChoiceFn.all : ChoiceFn X where
  C Y := Y
  sub _ := subset_rfl

/-- Witness: `ChoiceFn.top` and `ChoiceFn.all` satisfy substitutes and IRC, so the hypotheses
of the existence theorem are not contradictory (the resulting example is simple). -/
theorem choiceFn_top_spec (x₀ : X) : (ChoiceFn.top x₀).Substitutes ∧ (ChoiceFn.top x₀).IRC ∧
    (ChoiceFn.all : ChoiceFn X).Substitutes ∧ (ChoiceFn.all : ChoiceFn X).IRC := by
  classical
  refine ⟨fun Y Z hYZ x hx => ?_, fun Y Z hZ hYZ => ?_, fun Y Z _ x hx => ?_, fun Y Z hZ hYZ => ?_⟩
  · simp only [ChoiceFn.R, ChoiceFn.top, mem_sdiff] at hx ⊢
    by_cases hY : x₀ ∈ Y
    · simp only [hY, ↓reduceIte, mem_singleton_iff] at hx
      simp only [hYZ hY, ↓reduceIte, mem_singleton_iff]
      exact ⟨hYZ hx.1, hx.2⟩
    · simp only [hY, ↓reduceIte] at hx; exact absurd hx.1 hx.2
  · simp only [ChoiceFn.top] at hZ ⊢
    by_cases hz : x₀ ∈ Z
    · simp only [hz, ↓reduceIte, singleton_subset_iff] at hZ ⊢
      simp only [hZ, ↓reduceIte]
    · have hy : x₀ ∉ Y := fun h => hz (hYZ h)
      simp only [hz, hy, ↓reduceIte] at hZ ⊢
      exact subset_antisymm hYZ hZ
  · simp only [ChoiceFn.R, ChoiceFn.all, mem_sdiff] at hx; exact absurd hx.1 hx.2
  · simp only [ChoiceFn.all] at hZ ⊢; exact subset_antisymm hYZ hZ

example (x₀ : X) : ∃ Y, IsStableAlloc (ChoiceFn.top x₀) ChoiceFn.all Y :=
  have h := choiceFn_top_spec x₀
  stable_exists h.1 h.2.2.1 h.2.1 h.2.2.2

end Econ
