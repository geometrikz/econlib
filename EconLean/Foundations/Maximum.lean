/-
# Berge's maximum theorem

Aliprantis–Border Thm 17.31; Stokey–Lucas Thm 3.6; MWG Thm M.K.6;
Ok, *Real Analysis with Economic Applications*, §E.3.

**The economics.** Many economic objects are "the best choice from a
feasible set that moves with parameters":

* demand `x(p, w)` maximizes utility over the budget set `B(p, w)`;
* the indirect utility `v(p, w)` is the maximized value;
* the policy and value functions of a dynamic program solve
  `max_{y ∈ Γ(x)} F(x, y) + β V(y)`.

Berge's theorem says: if the objective `f(x, y)` is continuous and the
feasible set `Φ(x)` is a continuous correspondence with nonempty compact
values, then

1. the **value** `m(x) = max_{y ∈ Φ x} f(x, y)` is continuous, and
2. the **argmax** `μ(x) = {y ∈ Φ x | f(x, y) = m(x)}` is UHC with nonempty
   compact values.

If moreover the argmax is a single point `g x` (e.g. strictly quasiconcave
objective on convex feasible sets), then `g` is a continuous function.

**Documented deviations from Aliprantis–Border.**
* We assume `f` is continuous on all of `X × Y`, as in Stokey–Lucas Thm 3.6
  and MWG Thm M.K.6. AB 17.31 needs continuity only on the graph of `Φ`.
* The one-sided halves (AB 17.29–17.30) are proved for continuous `f`, not
  merely semicontinuous `f`, and the lower half assumes compact values: AB
  allows `m` to be `+∞`, while our `m` is a real-valued `sSup`, which is only
  meaningful when attained.

The sequential characterizations of LHC (AB 17.21, both directions) and the
sequential sufficient condition for UHC (AB 17.20) are in Mathlib as
`LowerHemicontinuousAt.of_sequences`, `LowerHemicontinuousAt.exists_seq_tendsto`
and `UpperHemicontinuousAt.of_sequences`.

We also prove the two halves separately: UHC of `Φ` gives *upper*
semicontinuity of `m`, LHC gives *lower* semicontinuity.

**Junk-value warning.** We define `m(x)` as `sSup (f x '' Φ x)`. In Lean
`sSup` of an empty or unbounded set of reals is `0`, a meaningless value.
Every theorem below therefore assumes nonempty compact values, and the
headline theorem also states that `m x` is *attained*
(`IsGreatest (f x '' Φ x) (m x)`), so `m` really is the maximum.
-/
module

public import EconLean.Foundations.Correspondence
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace Econ

open Filter Topology Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The **value function** `m(x) = sup_{y ∈ Φ x} f(x, y)`. Meaningful only
when the supremum is attained; see the junk-value warning above. -/
noncomputable def maxValue (f : X → Y → ℝ) (Φ : X → Set Y) (x : X) : ℝ :=
  sSup (f x '' Φ x)

/-- The **argmax correspondence**: the feasible `y` that do at least as well
as every other feasible `y'`. Defined without reference to `maxValue`. -/
def argmax (f : X → Y → ℝ) (Φ : X → Set Y) (x : X) : Set Y :=
  {y | y ∈ Φ x ∧ ∀ y' ∈ Φ x, f x y' ≤ f x y}

variable {f : X → Y → ℝ} {Φ : X → Set Y}

/-- If `f` is jointly continuous then each section `f x` is continuous. -/
theorem continuous_section (hf : Continuous (Function.uncurry f)) (x : X) :
    Continuous (f x) :=
  hf.comp (Continuous.prodMk_right x)

/-- On a nonempty compact feasible set, `maxValue` is attained. -/
theorem isGreatest_maxValue (hf : Continuous (Function.uncurry f)) {x : X}
    (hne : (Φ x).Nonempty) (hK : IsCompact (Φ x)) :
    IsGreatest (f x '' Φ x) (maxValue f Φ x) :=
  (hK.image (continuous_section hf x)).isGreatest_sSup (hne.image _)

/-- On a nonempty compact feasible set, the argmax is exactly the feasible
points attaining `maxValue`. -/
theorem argmax_eq (hf : Continuous (Function.uncurry f)) {x : X}
    (hne : (Φ x).Nonempty) (hK : IsCompact (Φ x)) :
    argmax f Φ x = Φ x ∩ {y | maxValue f Φ x ≤ f x y} := by
  have hg := isGreatest_maxValue hf hne hK
  ext y
  simp only [argmax, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hmax⟩
    obtain ⟨y₀, hy₀, heq⟩ := hg.1
    exact ⟨hy, heq ▸ hmax y₀ hy₀⟩
  · rintro ⟨hy, hle⟩
    exact ⟨hy, fun y' hy' => (hg.2 ⟨y', hy', rfl⟩).trans hle⟩

/-! ### The value function -/

/-- **Berge, upper half.** If `Φ` is UHC with nonempty compact values and `f`
is continuous, the value function is upper semicontinuous. -/
theorem upperSemicontinuous_maxValue (hf : Continuous (Function.uncurry f))
    (hU : UpperHemicontinuous Φ) (hne : ∀ x, (Φ x).Nonempty) (hK : ∀ x, IsCompact (Φ x)) :
    UpperSemicontinuous (maxValue f Φ) := by
  intro x c hc
  -- Every feasible `y` at `x` has `f(x, y) ≤ m(x) < c`.
  have hlt : ∀ y ∈ Φ x, f x y < c := fun y hy =>
    lt_of_le_of_lt ((isGreatest_maxValue hf (hne x) (hK x)).2 ⟨y, hy, rfl⟩) hc
  -- The set where `f < c` is open and contains `{x} × Φ x`; by the tube lemma
  -- it contains a box `u × v`.
  have hW : IsOpen {q : X × Y | f q.1 q.2 < c} := isOpen_lt hf continuous_const
  have hsub : ({x} : Set X) ×ˢ Φ x ⊆ {q : X × Y | f q.1 q.2 < c} := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hlt y hy
  obtain ⟨u, v, huo, hvo, hxu, hΦv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (hK x) hW hsub
  -- Near `x`: `x' ∈ u` and (UHC) `Φ x' ⊆ v`, so `f(x', ·) < c` on `Φ x'`.
  filter_upwards [upperHemicontinuousAt_iff_textbook.1 (hU x) v hvo hΦv,
    huo.mem_nhds (hxu rfl)] with x' h1 h2
  obtain ⟨y', hy', heq⟩ := (isGreatest_maxValue hf (hne x') (hK x')).1
  rw [← heq]
  exact huv (mk_mem_prod h2 (h1 hy'))

/-- **Berge, lower half.** If `Φ` is LHC with nonempty compact values and `f`
is continuous, the value function is lower semicontinuous. -/
theorem lowerSemicontinuous_maxValue (hf : Continuous (Function.uncurry f))
    (hL : LowerHemicontinuous Φ) (hne : ∀ x, (Φ x).Nonempty) (hK : ∀ x, IsCompact (Φ x)) :
    LowerSemicontinuous (maxValue f Φ) := by
  intro x c hc
  -- A maximizer `y` at `x` has `f(x, y) > c`, and this persists on a box.
  obtain ⟨y, hy, heq⟩ := (isGreatest_maxValue hf (hne x) (hK x)).1
  have hW : IsOpen {q : X × Y | c < f q.1 q.2} := isOpen_lt continuous_const hf
  have hxy : (x, y) ∈ {q : X × Y | c < f q.1 q.2} := by
    show c < f x y
    rw [heq]; exact hc
  obtain ⟨u, v, huo, hvo, hxu, hyv, huv⟩ := isOpen_prod_iff.1 hW x y hxy
  -- LHC: near `x`, some feasible `y'` lies in `v`; then `m(x') ≥ f(x', y') > c`.
  filter_upwards [lowerHemicontinuousAt_iff.1 (hL x) v hvo ⟨y, hy, hyv⟩,
    huo.mem_nhds hxu] with x' ⟨y', hy'Φ, hy'v⟩ hx'u
  have hlt : c < f x' y' := huv (mk_mem_prod hx'u hy'v)
  exact lt_of_lt_of_le hlt
    ((isGreatest_maxValue hf (hne x') (hK x')).2 (mem_image_of_mem (f x') hy'Φ))

/-- **Berge: the value function is continuous.** -/
theorem continuous_maxValue (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) :
    Continuous (maxValue f Φ) :=
  continuous_iff_lower_upperSemicontinuous.2
    ⟨lowerSemicontinuous_maxValue hf hΦ.2 hne hK, upperSemicontinuous_maxValue hf hΦ.1 hne hK⟩

/-! ### The argmax correspondence -/

/-- The argmax is nonempty (Weierstrass). -/
theorem argmax_nonempty (hf : Continuous (Function.uncurry f)) {x : X}
    (hne : (Φ x).Nonempty) (hK : IsCompact (Φ x)) : (argmax f Φ x).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne (continuous_section hf x).continuousOn
  exact ⟨y, hy, fun y' hy' => hmax hy'⟩

/-- The argmax is compact: a closed subset of the compact feasible set. -/
theorem isCompact_argmax (hf : Continuous (Function.uncurry f)) {x : X}
    (hne : (Φ x).Nonempty) (hK : IsCompact (Φ x)) : IsCompact (argmax f Φ x) := by
  rw [argmax_eq hf hne hK]
  exact hK.inter_right (isClosed_le continuous_const (continuous_section hf x))

/-- **Berge: the argmax is UHC.** Needs the value function to be continuous,
hence both UHC and LHC of `Φ`. -/
theorem upperHemicontinuous_argmax (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) :
    UpperHemicontinuous (argmax f Φ) := by
  intro x
  -- `argmax = Φ ∩ Ψ` with `Ψ x = {y | m x ≤ f x y}`, whose graph is closed
  -- because `m` and `f` are continuous.
  have hm := continuous_maxValue hf hΦ hne hK
  have hΨ : IsClosed (graph fun x => {y | maxValue f Φ x ≤ f x y}) :=
    isClosed_le (hm.comp continuous_fst) hf
  have h := UpperHemicontinuousAt.inter_of_isClosed_graph (hΦ.1 x) (hK x) hΨ
  refine UpperHemicontinuousAt.congr' h (Eventually.of_forall fun x' => ?_)
  exact (argmax_eq hf (hne x') (hK x')).symm

/-- **Berge's maximum theorem** (AB 17.31, SL 3.6, MWG M.K.6).
Let `f : X × Y → ℝ` be continuous and `Φ : X ↠ Y` be continuous (UHC and
LHC) with nonempty compact values. Then
1. the maximum is attained: `m x` is the greatest value of `f x` on `Φ x`;
2. the value function `m` is continuous;
3. the argmax correspondence has nonempty compact values and is UHC. -/
theorem berge_maximum_theorem (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) :
    (∀ x, IsGreatest (f x '' Φ x) (maxValue f Φ x)) ∧
    Continuous (maxValue f Φ) ∧
    (∀ x, (argmax f Φ x).Nonempty ∧ IsCompact (argmax f Φ x)) ∧
    UpperHemicontinuous (argmax f Φ) :=
  ⟨fun x => isGreatest_maxValue hf (hne x) (hK x), continuous_maxValue hf hΦ hne hK,
    fun x => ⟨argmax_nonempty hf (hne x) (hK x), isCompact_argmax hf (hne x) (hK x)⟩,
    upperHemicontinuous_argmax hf hΦ hne hK⟩

/-- **Continuous selection when the maximizer is unique.** If in Berge's
setting the argmax is always a single point `g x`, then `g` is continuous.
This is the step "unique demand ⇒ continuous demand" (MWG Prop. 3.D.2/3.AA). -/
theorem continuous_of_argmax_eq_singleton (hf : Continuous (Function.uncurry f))
    (hΦ : ContinuousCorrespondence Φ) (hne : ∀ x, (Φ x).Nonempty)
    (hK : ∀ x, IsCompact (Φ x)) {g : X → Y} (hg : ∀ x, argmax f Φ x = {g x}) :
    Continuous g := by
  rw [← upperHemicontinuous_singleton_iff]
  have h := upperHemicontinuous_argmax hf hΦ hne hK
  have hfun : argmax f Φ = fun x => {g x} := funext hg
  rwa [hfun] at h

/-! ### Sanity checks (non-vacuity and necessity)

**Non-vacuity.** All hypotheses of Berge's theorem hold for the problem
`max_{y ∈ [-1, 1]} -(y - x)²` (feasible set fixed, optimum moves with `x`). -/

example : Continuous (Function.uncurry fun x y : ℝ => -(y - x) ^ 2) ∧
    ContinuousCorrespondence (fun _ : ℝ => Icc (-1 : ℝ) 1) ∧
    (∀ x : ℝ, ((fun _ : ℝ => Icc (-1 : ℝ) 1) x).Nonempty) ∧
    (∀ x : ℝ, IsCompact ((fun _ : ℝ => Icc (-1 : ℝ) 1) x)) ∧
    Continuous (maxValue (fun x y : ℝ => -(y - x) ^ 2) (fun _ => Icc (-1) 1)) ∧
    UpperHemicontinuous (argmax (fun x y : ℝ => -(y - x) ^ 2) (fun _ => Icc (-1) 1)) := by
  -- First the hypotheses of Berge, then its conclusions obtained from the theorem.
  have hf : Continuous (Function.uncurry fun x y : ℝ => -(y - x) ^ 2) := by
    unfold Function.uncurry; fun_prop
  have hΦ : ContinuousCorrespondence (fun _ : ℝ => Icc (-1 : ℝ) 1) :=
    ⟨UpperHemicontinuous.const, LowerHemicontinuous.const⟩
  have hne : ∀ x : ℝ, ((fun _ : ℝ => Icc (-1 : ℝ) 1) x).Nonempty :=
    fun _ => nonempty_Icc.2 (by norm_num : (-1 : ℝ) ≤ 1)
  have hK : ∀ x : ℝ, IsCompact ((fun _ : ℝ => Icc (-1 : ℝ) 1) x) := fun _ => isCompact_Icc
  have h := berge_maximum_theorem hf hΦ hne hK
  exact ⟨hf, hΦ, hne, hK, h.2.1, h.2.2.2⟩

/-! **Necessity of LHC.** `Φ 0 = [0, 1]`, `Φ x = {0}` otherwise, objective
`f(x, y) = y`. `Φ` is UHC with nonempty compact values (proved below via the
closed-graph test), but not LHC at `0`, and the value function jumps from `1`
(at `0`) to `0` (elsewhere). So UHC alone does not give a continuous value. -/

/-- The jumping correspondence of the counterexample. -/
noncomputable def jumpCorr (x : ℝ) : Set ℝ := if x = 0 then Icc 0 1 else {0}

/-- The counterexample satisfies every hypothesis of Berge except LHC. -/
example : UpperHemicontinuous jumpCorr ∧ (∀ x, (jumpCorr x).Nonempty) ∧
    (∀ x, IsCompact (jumpCorr x)) ∧ ¬ LowerHemicontinuousAt jumpCorr 0 := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, ?_⟩
  · -- The graph is `({0} × [0,1]) ∪ (ℝ × {0})`, a closed set, and all values
    -- lie in the compact set `[0, 1]`.
    have hgraph : graph jumpCorr = ({0} ×ˢ Icc 0 1) ∪ (univ ×ˢ {0}) := by
      ext ⟨a, b⟩
      by_cases ha : a = 0
      · subst ha
        simp only [mem_graph, jumpCorr, ite_true, mem_union, mem_prod, mem_singleton_iff,
          mem_univ, true_and]
        constructor
        · exact Or.inl
        · rintro (h | rfl)
          · exact h
          · exact ⟨le_refl _, zero_le_one⟩
      · simp [jumpCorr, ha]
    have hcl : IsClosed (graph jumpCorr) := by
      rw [hgraph]
      exact (isClosed_singleton.prod isClosed_Icc).union (isClosed_univ.prod isClosed_singleton)
    refine upperHemicontinuousAt_of_isClosed_graph hcl (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      (Eventually.of_forall fun x' => ?_)
    unfold jumpCorr
    split_ifs
    · exact subset_rfl
    · exact singleton_subset_iff.2 ⟨le_refl _, zero_le_one⟩
  · unfold jumpCorr
    split_ifs
    · exact nonempty_Icc.2 zero_le_one
    · exact singleton_nonempty _
  · unfold jumpCorr
    split_ifs
    · exact isCompact_Icc
    · exact isCompact_singleton
  · -- LHC fails at `0` with the open set `U = (1/2, ∞)`: it meets `Φ 0 = [0,1]`
    -- (at `1`) but misses `Φ x = {0}` for every `x ≠ 0`, and such `x` exist
    -- arbitrarily close to `0`.
    intro hL
    have h := lowerHemicontinuousAt_iff.1 hL (Ioi (1 / 2)) isOpen_Ioi
      ⟨1, by simp [jumpCorr], by norm_num⟩
    obtain ⟨x, hx, hx0⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ) (a := 0))).exists
    have hx0' : x ≠ 0 := hx0
    obtain ⟨y, hy, hyU⟩ := hx
    simp only [jumpCorr, hx0', ite_false, mem_singleton_iff] at hy
    subst hy
    norm_num at hyU

/-- …but its value function is not continuous. -/
example : ¬ Continuous (maxValue (fun (_ : ℝ) (y : ℝ) => y) jumpCorr) := by
  intro h
  have hv0 : maxValue (fun (_ : ℝ) (y : ℝ) => y) jumpCorr 0
      = 1 := by
    simp [maxValue, jumpCorr, csSup_Icc (zero_le_one' ℝ)]
  have hv : ∀ x : ℝ, x ≠ 0 →
      maxValue (fun (_ : ℝ) (y : ℝ) => y) jumpCorr x = 0 := by
    intro x hx
    simp [maxValue, jumpCorr, hx]
  -- Along `1/(n+1) → 0` the value is `0`, so its limit `1` would be `0`.
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := (h.tendsto 0).comp ht
  rw [hv0] at hlim
  have hconst : (maxValue (fun (_ : ℝ) (y : ℝ) => y) jumpCorr) ∘ (fun n : ℕ => (1 : ℝ) / (n + 1)) =
      fun _ => 0 := by
    funext n
    exact hv _ (by positivity)
  rw [hconst] at hlim
  exact one_ne_zero (tendsto_nhds_unique hlim tendsto_const_nhds)

end Econ
