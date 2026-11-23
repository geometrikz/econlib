/-
# Public goods: the Samuelson condition, Lindahl equilibrium, private provision

MWG §11.C–11.D. Consumers `i ∈ I` have quasilinear utility `φᵢ(G) + mᵢ` in the level `G ≥ 0`
of a public good, which costs `C(G)` to produce.

Main results:
* `samuelson_condition` (MWG §11.C, eq. 11.C.1): at an interior efficient level, the sum of
  marginal benefits equals marginal cost, `∑ᵢ φᵢ'(G*) = C'(G*)`.
* `samuelson_sufficient`: with concave benefits and convex costs the Samuelson condition is
  also sufficient for efficiency.
* `lindahl_efficient` (MWG §11.D): a Lindahl equilibrium (personalised prices summing
  to marginal cost, every consumer demanding the same level) is efficient.
* `voluntary_underprovision` (MWG Prop. 11.C.1): with at least two consumers, strictly
  decreasing positive marginal benefits and unit cost, voluntary contributions provide
  strictly less than the efficient level.
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Econ

open Finset Set Filter

/-- **Tangent-line inequality for concave functions**: `f y ≤ f x + f'(x) (y − x)`. -/
lemma concaveOn_le_tangent {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ} (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f f' x) : f y ≤ f x + f' * (y - x) := by
  have hg : ConvexOn ℝ S (-f) := hfc.neg
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have := hg.le_slope_of_hasDerivAt hx hy hxy hd.neg
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at this
    simp only [Pi.neg_apply] at this
    linarith
  · simp
  · have := hg.slope_le_of_hasDerivAt hy hx hxy hd.neg
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hxy)] at this
    simp only [Pi.neg_apply] at this
    linarith

/-- **Tangent-line inequality for convex functions**: `f x + f'(x) (y − x) ≤ f y`. -/
lemma convexOn_tangent_le {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ} (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f f' x) : f x + f' * (y - x) ≤ f y := by
  have := concaveOn_le_tangent hfc.neg hx hy hd.neg
  simp only [Pi.neg_apply] at this
  linarith

variable {I : Type*} [Fintype I]

/-- Social surplus from public good level `G`: total benefit minus cost. -/
def publicSurplus (φ : I → ℝ → ℝ) (C : ℝ → ℝ) (G : ℝ) : ℝ := ∑ i, φ i G - C G

/-- `G` is an **efficient** level of the public good. -/
def IsEfficientLevel (φ : I → ℝ → ℝ) (C : ℝ → ℝ) (G : ℝ) : Prop :=
  0 ≤ G ∧ ∀ G', 0 ≤ G' → publicSurplus φ C G' ≤ publicSurplus φ C G

/-- **The Samuelson condition** (MWG 11.C.1). At an interior efficient level, the sum of the
consumers' marginal benefits equals the marginal cost. -/
theorem samuelson_condition {φ : I → ℝ → ℝ} {C : ℝ → ℝ} {G : ℝ} {φ' : I → ℝ} {C' : ℝ}
    (hG : IsEfficientLevel φ C G) (hpos : 0 < G) (hφ : ∀ i, HasDerivAt (φ i) (φ' i) G)
    (hC : HasDerivAt C C' G) : ∑ i, φ' i = C' := by
  have hmax : IsLocalMax (publicSurplus φ C) G :=
    Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun G' hG' => hG.2 G' (le_of_lt hG')
  have hd : HasDerivAt (publicSurplus φ C) (∑ i, φ' i - C') G := by
    have := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hφ i).sub hC
    have e : publicSurplus φ C = (fun y => ∑ i, φ i y) - C := by
      funext y; simp [publicSurplus]
    rw [e]; exact this
  linarith [hmax.hasDerivAt_eq_zero hd]

/-- **The Samuelson condition is sufficient** under concave benefits and convex cost. -/
theorem samuelson_sufficient {φ : I → ℝ → ℝ} {C : ℝ → ℝ} {G : ℝ} {φ' : I → ℝ} {C' : ℝ}
    (hφc : ∀ i, ConcaveOn ℝ (Ici 0) (φ i)) (hCc : ConvexOn ℝ (Ici 0) C) (hG : 0 ≤ G)
    (hφ : ∀ i, HasDerivAt (φ i) (φ' i) G) (hC : HasDerivAt C C' G)
    (hsam : ∑ i, φ' i = C') : IsEfficientLevel φ C G := by
  refine ⟨hG, fun G' hG' => ?_⟩
  have h1 : ∑ i, φ i G' ≤ ∑ i, (φ i G + φ' i * (G' - G)) :=
    sum_le_sum fun i _ => concaveOn_le_tangent (hφc i) hG hG' (hφ i)
  have h2 := convexOn_tangent_le hCc hG hG' hC
  rw [sum_add_distrib, ← sum_mul, hsam] at h1
  simp only [publicSurplus]
  linarith

/-- **Lindahl equilibrium** with constant marginal cost `c`: personalised prices `p i` that
sum to `c` (so the producer breaks even at every level), and a level `G ≥ 0` that every
consumer demands at her price. -/
def IsLindahlEq (φ : I → ℝ → ℝ) (c : ℝ) (p : I → ℝ) (G : ℝ) : Prop :=
  0 ≤ G ∧ ∑ i, p i = c ∧ ∀ i, ∀ G', 0 ≤ G' → φ i G' - p i * G' ≤ φ i G - p i * G

/-- **Lindahl equilibria are efficient** (MWG §11.D). -/
theorem lindahl_efficient {φ : I → ℝ → ℝ} {c : ℝ} {p : I → ℝ} {G : ℝ}
    (h : IsLindahlEq φ c p G) : IsEfficientLevel φ (fun G => c * G) G := by
  refine ⟨h.1, fun G' hG' => ?_⟩
  have := sum_le_sum fun i (_ : i ∈ Finset.univ) => h.2.2 i G' hG'
  simp only [sum_sub_distrib, ← sum_mul, h.2.1] at this
  simp only [publicSurplus]
  linarith

/-- **Voluntary contributions equilibrium** with unit cost: each consumer `i` contributes
`g i ≥ 0`, and no consumer gains by changing her own contribution to any `t ≥ 0`. -/
def IsVoluntaryEq (φ : I → ℝ → ℝ) (g : I → ℝ) : Prop :=
  (∀ i, 0 ≤ g i) ∧
    ∀ i, ∀ t, 0 ≤ t → φ i (∑ j, g j - g i + t) - t ≤ φ i (∑ j, g j) - g i

/-- **Private provision is inefficiently low** (MWG Prop. 11.C.1). Suppose there are at least
two consumers, unit cost, and marginal benefits `d i` that are positive and strictly
decreasing. If `Gstar` satisfies the Samuelson condition `∑ᵢ dᵢ(Gstar) = 1` and the voluntary
contributions equilibrium provides a positive amount, it provides strictly less than
`Gstar`. -/
theorem voluntary_underprovision [DecidableEq I] {φ d : I → ℝ → ℝ}
    (hd : ∀ i x, HasDerivAt (φ i) (d i x) x) (hpos : ∀ i x, 0 < d i x)
    (hanti : ∀ i, StrictAnti (d i)) (htwo : 1 < Fintype.card I) {g : I → ℝ}
    (heq : IsVoluntaryEq φ g) (hGpos : 0 < ∑ j, g j) {Gstar : ℝ}
    (hsam : ∑ i, d i Gstar = 1) : ∑ j, g j < Gstar := by
  set Ge := ∑ j, g j
  -- Some consumer contributes a positive amount.
  obtain ⟨i, hi⟩ : ∃ i, 0 < g i := by
    by_contra h
    push Not at h
    exact absurd (sum_nonpos fun j _ => h j) (not_le.2 hGpos)
  -- Her first-order condition: `d i Ge = 1`.
  have hfoc : d i Ge = 1 := by
    set ψ : ℝ → ℝ := fun t => φ i (Ge - g i + t) - t
    have hmax : IsLocalMax ψ (g i) := by
      filter_upwards [Ioi_mem_nhds hi] with t ht
      have := heq.2 i t (le_of_lt ht)
      simp only [ψ, sub_add_cancel]
      exact this
    have hψ : HasDerivAt ψ (d i Ge - 1) (g i) := by
      have h2 := HasDerivAt.comp_const_add (Ge - g i) (g i) (hd i (Ge - g i + g i))
      simp only [sub_add_cancel] at h2
      exact h2.sub (hasDerivAt_id _)
    linarith [hmax.hasDerivAt_eq_zero hψ]
  -- Another consumer's marginal benefit is positive, so `∑ d Ge > 1`.
  obtain ⟨j, hji⟩ : ∃ j, j ≠ i := by
    by_contra h
    push Not at h
    have : Fintype.card I ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    omega
  have hsum : 1 < ∑ k, d k Ge := by
    rw [← add_sum_erase _ _ (mem_univ i), hfoc]
    have : 0 < ∑ k ∈ univ.erase i, d k Ge :=
      sum_pos (fun k _ => hpos k Ge) ⟨j, mem_erase.2 ⟨hji, mem_univ j⟩⟩
    linarith
  by_contra hge
  push Not at hge
  have : ∑ k, d k Ge ≤ ∑ k, d k Gstar :=
    sum_le_sum fun k _ => (hanti k).antitone hge
  linarith

end Econ
