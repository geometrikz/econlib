/-
# Matching with contracts: every stable allocation is a fixed point; side-optimal allocations

Hatfield and Milgrom (2005), *Matching with Contracts*, AER; Fleiner (2003);
Hatfield and Kominers (2017). This file continues `Matching/Contracts`, in its abstract
two-sided setting: each side is one aggregate choice function, satisfying substitutes and the
irrelevance of rejected contracts (IRC).

* `stable_isFixedPoint` (the converse half of the fixed-point theorem): every stable
  allocation `Y` equals `X_D ∩ X_H` for a fixed point of the Hatfield–Milgrom map, namely
  `X_D = Y ∪ {x | doctors reject x from Y ∪ {x}, hospitals do not}` and
  `X_H = Y ∪ {x | hospitals reject x from Y ∪ {x}}`.
* `doctor_optimal`: there is a stable allocation `Y*` (in the proof, from the greatest fixed
  point: largest `X_D`, smallest `X_H`) that the doctors' side prefers to every stable allocation `Y`, in the
  revealed-preference sense `C_D (Y* ∪ Y) = Y*`. With unit-demand doctors with strict
  preferences (Hatfield–Milgrom's setting) this says that every doctor weakly prefers his
  contract in `Y*`.
* `hospital_optimal`: symmetrically, there is a hospital-optimal stable allocation (in the
  proof, from the least fixed point).

The existing witness `choiceFn_top_spec` shows the hypotheses are consistent; it has a unique
stable allocation, so it does not separate the two optima. Not formalized: the lattice structure of the full set of stable allocations, opposition of
interests (the doctor-optimal allocation is the worst stable one for hospitals), and the rural
hospitals theorem.
-/
module

public import EconLean.Matching.Contracts

@[expose] public section

namespace Econ

open Set OrderDual

variable {X : Type*} {cD cH : ChoiceFn X}

/-- At a fixed point of the Hatfield–Milgrom map, the doctors choose `X_D ∩ X_H` from `X_D`. -/
lemma hmFix_chooseD {XD XH : Set X} (hfix : hmMap cD cH (XD, XH) = (XD, XH)) :
    cD.C XD = XD ∩ XH := by
  simp only [hmMap, Prod.mk.injEq] at hfix
  obtain ⟨-, hH⟩ := hfix
  ext x; constructor
  · intro hx
    refine ⟨cD.sub XD hx, ?_⟩
    rw [← hH]; exact fun hr => hr.2 hx
  · rintro ⟨hxD, hxH⟩
    by_contra hn
    rw [← hH] at hxH
    exact hxH ⟨hxD, hn⟩

/-- At a fixed point of the Hatfield–Milgrom map, the hospitals choose `X_D ∩ X_H` from `X_H`. -/
lemma hmFix_chooseH {XD XH : Set X} (hfix : hmMap cD cH (XD, XH) = (XD, XH)) :
    cH.C XH = XD ∩ XH := by
  simp only [hmMap, Prod.mk.injEq] at hfix
  obtain ⟨hD, -⟩ := hfix
  ext x; constructor
  · intro hx
    refine ⟨?_, cH.sub XH hx⟩
    rw [← hD]; exact fun hr => hr.2 hx
  · rintro ⟨hxD, hxH⟩
    by_contra hn
    rw [← hD] at hxD
    exact hxD ⟨hxH, hn⟩

/-- The doctors' set attached to a stable allocation `Y`. -/
def stableXD (cD cH : ChoiceFn X) (Y : Set X) : Set X :=
  Y ∪ {x | x ∈ cD.R (Y ∪ {x}) ∧ x ∉ cH.R (Y ∪ {x})}

/-- The hospitals' set attached to a stable allocation `Y`. -/
def stableXH (cH : ChoiceFn X) (Y : Set X) : Set X :=
  Y ∪ {x | x ∈ cH.R (Y ∪ {x})}

/-- If `c` chooses all of `Y`, and every contract of `W \ Y` is rejected from `Y ∪ {x}`, then
`c` chooses exactly `Y` from `W ⊇ Y`. -/
lemma choose_eq_of_rejects {c : ChoiceFn X} (hs : c.Substitutes) (hi : c.IRC) {Y W : Set X}
    (hY : c.C Y = Y) (hYW : Y ⊆ W) (hrej : ∀ x ∈ W, x ∉ Y → x ∈ c.R (Y ∪ {x})) :
    c.C W = Y := by
  have hsub : c.C W ⊆ Y := by
    intro x hx
    by_contra hxY
    have hxW := c.sub W hx
    have := hs _ _ (union_subset hYW (singleton_subset_iff.2 hxW)) (hrej x hxW hxY)
    exact this.2 hx
  rw [← hi Y W hsub hYW, hY]

/-- **Every stable allocation comes from a fixed point** (the converse half of the
Hatfield–Milgrom 2005 fixed-point theorem; abstract version with substitutes and IRC on both
sides). -/
theorem stable_isFixedPoint (hsD : cD.Substitutes) (hsH : cH.Substitutes) (hiD : cD.IRC)
    (hiH : cH.IRC) {Y : Set X} (hY : IsStableAlloc cD cH Y) :
    hmMap cD cH (stableXD cD cH Y, stableXH cH Y) = (stableXD cD cH Y, stableXH cH Y) ∧
      stableXD cD cH Y ∩ stableXH cH Y = Y := by
  obtain ⟨hYD, hYH, hblock⟩ := hY
  -- a single contract outside `Y` chosen by the doctors is rejected by the hospitals
  have single : ∀ x, x ∉ Y → x ∉ cD.R (Y ∪ {x}) → x ∈ cH.R (Y ∪ {x}) := by
    intro x hxY hxD
    have hxC : x ∈ cD.C (Y ∪ {x}) := by
      by_contra h; exact hxD ⟨Or.inr rfl, h⟩
    refine ⟨Or.inr rfl, fun hxH => hblock {x} ⟨x, rfl⟩
      (disjoint_singleton_left.2 hxY) (singleton_subset_iff.2 hxC)
      (singleton_subset_iff.2 hxH)⟩
  set XD := stableXD cD cH Y
  set XH := stableXH cH Y
  have hYXD : Y ⊆ XD := subset_union_left
  have hYXH : Y ⊆ XH := subset_union_left
  have hCH : cH.C XH = Y := choose_eq_of_rejects hsH hiH hYH hYXH (fun x hx hxY => by
    rcases hx with hx | hx
    · exact absurd hx hxY
    · exact hx)
  have hCD : cD.C XD = Y := choose_eq_of_rejects hsD hiD hYD hYXD (fun x hx hxY => by
    rcases hx with hx | hx
    · exact absurd hx hxY
    · exact hx.1)
  have hinter : XD ∩ XH = Y := by
    ext x; constructor
    · rintro ⟨hxD, hxH⟩
      rcases hxD with hxD | hxD
      · exact hxD
      · rcases hxH with hxH | hxH
        · exact hxH
        · exact absurd hxH hxD.2
    · intro hx; exact ⟨hYXD hx, hYXH hx⟩
  refine ⟨?_, hinter⟩
  simp only [hmMap, Prod.mk.injEq]
  constructor
  · -- `X_D` is the set of contracts not rejected by the hospitals from `X_H`
    ext x
    simp only [mem_compl_iff, ChoiceFn.R, mem_sdiff, hCH, not_and, not_not]
    constructor
    · intro h
      by_cases hxY : x ∈ Y
      · exact hYXD hxY
      · by_cases hxH : x ∈ XH
        · exact absurd (h hxH) hxY
        · have hxR : x ∉ cH.R (Y ∪ {x}) := fun hr => hxH (Or.inr hr)
          refine Or.inr ⟨?_, hxR⟩
          by_contra hxD
          exact hxR (single x hxY hxD)
    · intro hx hxH
      rcases hx with hx | hx
      · exact hx
      · rcases hxH with hxH | hxH
        · exact hxH
        · exact absurd hxH hx.2
  · -- `X_H` is the set of contracts not rejected by the doctors from `X_D`
    ext x
    simp only [mem_compl_iff, ChoiceFn.R, mem_sdiff, hCD, not_and, not_not]
    constructor
    · intro h
      by_cases hxY : x ∈ Y
      · exact hYXH hxY
      · by_cases hxD : x ∈ XD
        · exact absurd (h hxD) hxY
        · refine Or.inr ?_
          by_cases hr : x ∈ cD.R (Y ∪ {x})
          · by_contra hH; exact hxD (Or.inr ⟨hr, hH⟩)
          · exact single x hxY hr
    · intro hx hxD
      rcases hx with hx | hx
      · exact hx
      · rcases hxD with hxD | hxD
        · exact hxD
        · exact absurd hx hxD.2

/-- **Doctor-optimal stable allocation** (Hatfield–Milgrom 2005): there is a stable allocation
`Y*` such that the doctors choose `Y*` from `Y* ∪ Y` for every stable allocation `Y`. (In the
proof, `Y*` comes from the greatest fixed point of the Hatfield–Milgrom map.) -/
theorem doctor_optimal (hsD : cD.Substitutes) (hsH : cH.Substitutes) (hiD : cD.IRC)
    (hiH : cH.IRC) :
    ∃ Ystar, IsStableAlloc cD cH Ystar ∧
      ∀ Y, IsStableAlloc cD cH Y → cD.C (Ystar ∪ Y) = Ystar := by
  set f := hmOrderHom hsD hsH
  set p := OrderHom.gfp f
  have hfix : hmMap cD cH (p.1, ofDual p.2) = (p.1, ofDual p.2) := f.map_gfp
  refine ⟨p.1 ∩ ofDual p.2, hm_fixedPoint_stable hsD hsH hiD hiH hfix, fun Y hY => ?_⟩
  obtain ⟨hfixY, hinterY⟩ := stable_isFixedPoint hsD hsH hiD hiH hY
  -- the fixed point attached to `Y` lies below the greatest fixed point
  have hle : ((stableXD cD cH Y, toDual (stableXH cH Y)) : Set X × (Set X)ᵒᵈ) ≤ p :=
    OrderHom.le_gfp f (le_of_eq (congrArg (fun q : Set X × Set X => (q.1, toDual q.2))
      hfixY).symm)
  have hYp : Y ⊆ p.1 := hinterY ▸ inter_subset_left.trans hle.1
  have hC := hmFix_chooseD hfix
  exact (hiD _ _ (hC ▸ subset_union_left)
    (union_subset inter_subset_left hYp)).trans hC

/-- **Hospital-optimal stable allocation**: symmetrically, there is a stable allocation `Y*`
such that the hospitals choose `Y*` from `Y* ∪ Y` for every stable allocation `Y` (in the
proof, from the least fixed point). -/
theorem hospital_optimal (hsD : cD.Substitutes) (hsH : cH.Substitutes) (hiD : cD.IRC)
    (hiH : cH.IRC) :
    ∃ Ystar, IsStableAlloc cD cH Ystar ∧
      ∀ Y, IsStableAlloc cD cH Y → cH.C (Ystar ∪ Y) = Ystar := by
  set f := hmOrderHom hsD hsH
  set p := OrderHom.lfp f
  have hfix : hmMap cD cH (p.1, ofDual p.2) = (p.1, ofDual p.2) := f.map_lfp
  refine ⟨p.1 ∩ ofDual p.2, hm_fixedPoint_stable hsD hsH hiD hiH hfix, fun Y hY => ?_⟩
  obtain ⟨hfixY, hinterY⟩ := stable_isFixedPoint hsD hsH hiD hiH hY
  have hle : p ≤ ((stableXD cD cH Y, toDual (stableXH cH Y)) : Set X × (Set X)ᵒᵈ) :=
    OrderHom.lfp_le f (le_of_eq (congrArg (fun q : Set X × Set X => (q.1, toDual q.2))
      hfixY))
  have hYp : Y ⊆ ofDual p.2 := hinterY ▸ inter_subset_right.trans hle.2
  have hC := hmFix_chooseH hfix
  exact (hiH _ _ (hC ▸ subset_union_left)
    (union_subset inter_subset_right hYp)).trans hC

end Econ
