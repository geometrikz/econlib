/-
# Lyapunov's theorem for integrals

**The mathematics.** Lyapunov's convexity theorem (`Foundations/Measure/Lyapunov.lean`)
says that a finite vector of finite nonatomic measures takes every intermediate
value `t • (μ A)` on some measurable `B ⊆ A`. The form needed in economics,
e.g. for Aumann's (1964) core equivalence, is for **indefinite integrals of a
vector-valued integrable function**: if `λ` is a finite nonatomic measure and
`f : Ω → ℝ^η` is integrable, then for every measurable `A` and `t ∈ [0, 1]` some
measurable `B ⊆ A` has `∫_B f dλ = t ∫_A f dλ`.

**Proof.** Split each coordinate into positive and negative parts. The `2|η|`
measures `λ.withDensity (f i)⁺` and `λ.withDensity (f i)⁻` are finite (as `f` is
integrable) and nonatomic (being absolutely continuous with respect to the
nonatomic `λ`), and `∫_B f i = (f i)⁺λ(B) − (f i)⁻λ(B)`. Apply Lyapunov's
theorem to this family.

**Results.**
* `setIntegral_eq_measureReal_sub`: `∫_B g = (g⁺λ)(B) − (g⁻λ)(B)`.
* `exists_subset_setIntegral_eq_smul`: Lyapunov's theorem for integrals.
* `convex_integralRange`: the range `{∫_B f dλ}` of the indefinite integral is
  convex.
* `exists_subset_piecewise_setIntegral_eq` (and the case `A = Ω`,
  `exists_piecewise_integral_eq`): **gluing**: for integrable `g₁, g₂`, a
  measurable `A` and `t ∈ [0, 1]` some measurable `B ⊆ A` has
  `∫_A (B.piecewise g₁ g₂) = t ∫_A g₁ + (1 − t) ∫_A g₂`.
* `convex_selectionIntegral`: hence the integral of any correspondence
  (the set of integrals of its integrable selections) is convex, with no
  convexity assumption on its values: the step of Aumann's core equivalence
  proof that uses nonatomicity.

**Scope.** Only the convexity half of Lyapunov's theorem is proved (not
compactness of the range), for finite `λ`; weighted gluing with measurable
weights (Hildenbrand's `∫ F = ∫ conv F`) is not covered. The helpers
`partMeasure`, `partDiff` and their lemmas are internal to the proof.
* `nonatomic_volume_Icc`, `exists_half_integral_id`: Lebesgue measure on
  `[0, 1]` is nonatomic, and a set carrying half the integral of the identity.
-/
module

public import EconLean.Foundations.Measure.Lyapunov
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

noncomputable section

namespace Econ
namespace Lyapunov

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {η : Type*} [Fintype η]

/-- A real integral over a measurable set is the difference of the
positive-part and negative-part density measures of that set. -/
theorem setIntegral_eq_measureReal_sub {lam : Measure Ω} {g : Ω → ℝ} (hg : Integrable g lam)
    {B : Set Ω} (hB : MeasurableSet B) :
    ∫ a in B, g a ∂lam = (lam.withDensity fun a => ENNReal.ofReal (g a)).real B -
      (lam.withDensity fun a => ENNReal.ofReal (-g a)).real B := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg.integrableOn, measureReal_def,
    measureReal_def, withDensity_apply _ hB, withDensity_apply _ hB]

/-- The `2|η|` positive- and negative-part density measures of `f`. -/
def partMeasure (lam : Measure Ω) (f : Ω → η → ℝ) (p : η × Bool) : Measure Ω :=
  lam.withDensity fun a => ENNReal.ofReal (if p.2 then f a p.1 else -f a p.1)

theorem isFiniteMeasure_partMeasure {lam : Measure Ω} {f : Ω → η → ℝ} (hf : Integrable f lam)
    (p : η × Bool) : IsFiniteMeasure (partMeasure lam f p) := by
  obtain ⟨i, b⟩ := p
  cases b
  · exact isFiniteMeasure_withDensity_ofReal (hf.eval i).neg.2
  · exact isFiniteMeasure_withDensity_ofReal (hf.eval i).2

theorem nonatomic_partMeasure {lam : Measure Ω} [IsFiniteMeasure lam] (hlam : Nonatomic lam)
    {f : Ω → η → ℝ} (hf : Integrable f lam) (p : η × Bool) : Nonatomic (partMeasure lam f p) :=
  haveI := isFiniteMeasure_partMeasure hf p
  hlam.of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)

theorem setIntegral_apply_eq_partMeasure {lam : Measure Ω} {f : Ω → η → ℝ}
    (hf : Integrable f lam) {B : Set Ω} (hB : MeasurableSet B) (i : η) :
    (∫ a in B, f a ∂lam) i =
      (partMeasure lam f (i, true)).real B - (partMeasure lam f (i, false)).real B := by
  rw [eval_integral (fun j => (hf.eval j).restrict) i]
  exact setIntegral_eq_measureReal_sub (hf.eval i) hB

/-- **Lyapunov's theorem for integrals**: for a finite nonatomic `λ` and an
integrable `f : Ω → ℝ^η` (with `η` finite), every fraction `t ∈ [0, 1]` of
`∫_A f` is attained as `∫_B f` for some measurable `B ⊆ A`. -/
theorem exists_subset_setIntegral_eq_smul {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) {f : Ω → η → ℝ} (hf : Integrable f lam) {A : Set Ω}
    (hA : MeasurableSet A) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B ⊆ A, MeasurableSet B ∧ ∫ a in B, f a ∂lam = t • ∫ a in A, f a ∂lam := by
  have := isFiniteMeasure_partMeasure hf
  obtain ⟨B, hBA, hB, hBeq⟩ :=
    exists_subset_measureReal_eq_smul (nonatomic_partMeasure hlam hf) hA ht0 ht1
  refine ⟨B, hBA, hB, funext fun i => ?_⟩
  rw [Pi.smul_apply, setIntegral_apply_eq_partMeasure hf hB, setIntegral_apply_eq_partMeasure hf hA,
    hBeq (i, true), hBeq (i, false), smul_eq_mul]
  ring

/-- The **range of the indefinite integral** of `f`. -/
def integralRange (lam : Measure Ω) (f : Ω → η → ℝ) : Set (η → ℝ) :=
  {v | ∃ B, MeasurableSet B ∧ v = ∫ a in B, f a ∂lam}

/-- The linear map `v ↦ (v (i, true) − v (i, false))ᵢ`. -/
def partDiff : ((η × Bool) → ℝ) →ₗ[ℝ] (η → ℝ) where
  toFun v i := v (i, true) - v (i, false)
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- **Lyapunov's theorem, convexity form for integrals**: the range of the
indefinite integral of an integrable `f : Ω → ℝ^η` with respect to a finite
nonatomic measure is convex. -/
theorem convex_integralRange {lam : Measure Ω} [IsFiniteMeasure lam] (hlam : Nonatomic lam)
    {f : Ω → η → ℝ} (hf : Integrable f lam) : Convex ℝ (integralRange lam f) := by
  have := isFiniteMeasure_partMeasure hf
  have heq : integralRange lam f = partDiff '' Lyapunov.range (partMeasure lam f) := by
    ext v
    constructor
    · rintro ⟨B, hB, rfl⟩
      refine ⟨_, ⟨B, hB, rfl⟩, funext fun i => ?_⟩
      exact (setIntegral_apply_eq_partMeasure hf hB i).symm
    · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨B, hB, funext fun i => (setIntegral_apply_eq_partMeasure hf hB i).symm⟩
  rw [heq]
  exact (convex_range (nonatomic_partMeasure hlam hf)).linear_image _

/-- **Gluing on a set**: for integrable `g₁, g₂ : Ω → ℝ^η`, a measurable `A`
and `t ∈ [0, 1]` there is a measurable `B ⊆ A` such that the function equal to
`g₁` on `B` and to `g₂` off `B` integrates over `A` to
`t ∫_A g₁ + (1 − t) ∫_A g₂`. -/
theorem exists_subset_piecewise_setIntegral_eq {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) {g₁ g₂ : Ω → η → ℝ} (h₁ : Integrable g₁ lam) (h₂ : Integrable g₂ lam)
    {A : Set Ω} (hA : MeasurableSet A) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B ⊆ A, MeasurableSet B ∧ ∀ [DecidablePred (· ∈ B)],
      ∫ a in A, B.piecewise g₁ g₂ a ∂lam =
        t • ∫ a in A, g₁ a ∂lam + (1 - t) • ∫ a in A, g₂ a ∂lam := by
  let f : Ω → η ⊕ η → ℝ := fun a => Sum.elim (g₁ a) (g₂ a)
  have hf : Integrable f lam := by
    refine Integrable.of_eval fun j => ?_
    cases j with
    | inl i => exact h₁.eval i
    | inr i => exact h₂.eval i
  obtain ⟨B, hBA, hB, hBeq⟩ := exists_subset_setIntegral_eq_smul hlam hf hA ht0 ht1
  refine ⟨B, hBA, hB, fun {_} => ?_⟩
  have hc : ∀ (g : Ω → η → ℝ) (hg : Integrable g lam) (j : η → η ⊕ η)
      (hj : ∀ a i, f a (j i) = g a i),
      ∫ a in B, g a ∂lam = t • ∫ a in A, g a ∂lam := by
    intro g hg j hj
    funext i
    have := congrFun hBeq (j i)
    rw [eval_integral (fun k => (hf.eval k).restrict), Pi.smul_apply,
      eval_integral (fun k => (hf.eval k).restrict)] at this
    simp only [hj] at this
    rw [eval_integral (fun k => (hg.eval k).restrict), Pi.smul_apply,
      eval_integral (fun k => (hg.eval k).restrict)]
    exact this
  have h1 := hc g₁ h₁ Sum.inl (fun _ _ => rfl)
  have h2 := hc g₂ h₂ Sum.inr (fun _ _ => rfl)
  rw [integral_piecewise (μ := lam.restrict A) hB h₁.restrict.integrableOn
    h₂.restrict.integrableOn, setIntegral_compl (μ := lam.restrict A) hB h₂.restrict,
    Measure.restrict_restrict hB, inter_eq_left.2 hBA, h1, h2]
  module

/-- **Gluing**: the case `A = Ω` of `exists_subset_piecewise_setIntegral_eq`. -/
theorem exists_piecewise_integral_eq {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) {g₁ g₂ : Ω → η → ℝ} (h₁ : Integrable g₁ lam) (h₂ : Integrable g₂ lam)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B, MeasurableSet B ∧ ∀ [DecidablePred (· ∈ B)],
      ∫ a, B.piecewise g₁ g₂ a ∂lam = t • ∫ a, g₁ a ∂lam + (1 - t) • ∫ a, g₂ a ∂lam := by
  obtain ⟨B, -, hB, h⟩ :=
    exists_subset_piecewise_setIntegral_eq hlam h₁ h₂ MeasurableSet.univ ht0 ht1
  refine ⟨B, hB, fun {_} => ?_⟩
  simpa only [Measure.restrict_univ] using h

/-- The **integral of a correspondence** `F : Ω → Set ℝ^η`: the set of
integrals of its integrable almost-everywhere selections. -/
def selectionIntegral (lam : Measure Ω) (F : Ω → Set (η → ℝ)) : Set (η → ℝ) :=
  {v | ∃ g : Ω → η → ℝ, Integrable g lam ∧ (∀ᵐ a ∂lam, g a ∈ F a) ∧ v = ∫ a, g a ∂lam}

/-- **The integral of a correspondence over a finite nonatomic measure is
convex** (Aumann 1965, the convexity half; Richter 1963), with no convexity,
closedness or measurability assumption on the values `F a`. -/
theorem convex_selectionIntegral {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) (F : Ω → Set (η → ℝ)) : Convex ℝ (selectionIntegral lam F) := by
  classical
  rintro _ ⟨f, hf, hfF, rfl⟩ _ ⟨g, hg, hgF, rfl⟩ a b ha hb hab
  obtain ⟨B, hB, hBeq⟩ := exists_piecewise_integral_eq hlam hf hg ha (by linarith)
  refine ⟨B.piecewise f g,
    Integrable.piecewise hB.nullMeasurableSet hf.integrableOn hg.integrableOn, ?_, ?_⟩
  · filter_upwards [hfF, hgF] with x h1 h2
    by_cases hx : x ∈ B <;> simp [Set.piecewise, hx, h1, h2]
  · rw [hBeq, ← hab]; simp

/-! ### Witnesses -/

/-- **Lebesgue measure on `[0, 1]` is nonatomic**, so the hypotheses of the
Lyapunov theorems are satisfiable. Proof: `x ↦ λ(s ∩ (−∞, x])` is
1-Lipschitz, so by the intermediate value theorem it takes the value `λ(s)/2`. -/
theorem nonatomic_volume_Icc : Nonatomic (volume.restrict (Icc (0 : ℝ) 1)) := by
  intro s hs hpos
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hμdef
  have hspos : 0 < μ.real s := measureReal_pos_iff.2 hpos
  let g : ℝ → ℝ := fun x => μ.real (s ∩ Iic x)
  have hstep : ∀ x y, x ≤ y → g x ≤ g y ∧ g y - g x ≤ y - x := by
    intro x y hxy
    refine ⟨measureReal_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hxy)), ?_⟩
    have hsub : s ∩ Iic y ⊆ (s ∩ Iic x) ∪ Ioc x y := by
      rintro z ⟨hz, hzy⟩
      by_cases hzx : z ≤ x
      · exact Or.inl ⟨hz, hzx⟩
      · exact Or.inr ⟨lt_of_not_ge hzx, hzy⟩
    have h1 : g y ≤ g x + μ.real (Ioc x y) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have h2 : μ.real (Ioc x y) ≤ volume.real (Ioc x y) :=
      ENNReal.toReal_mono (by simp) (Measure.restrict_apply_le _ _)
    rw [Real.volume_real_Ioc_of_le hxy] at h2
    linarith
  have hlip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
    rcases le_total x y with hxy | hxy
    · have := hstep x y hxy
      constructor <;> rw [abs_of_nonpos (by linarith)] <;> linarith
    · have := hstep y x hxy
      constructor <;> rw [abs_of_nonneg (by linarith)] <;> linarith
  have hg0 : g (-1) = 0 := by
    show μ.real _ = 0
    rw [hμdef, measureReal_restrict_apply (hs.inter measurableSet_Iic)]
    convert measureReal_empty (μ := volume)
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
    intro h; linarith [h.1.2, h.2.1]
  have hg1 : g 1 = μ.real s := by
    show μ.real _ = _
    rw [hμdef, measureReal_restrict_apply (hs.inter measurableSet_Iic), measureReal_restrict_apply hs,
      inter_assoc]
    congr 2
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨h.2, h⟩⟩
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hlip.continuous.continuousOn
    (show μ.real s / 2 ∈ Icc (g (-1)) (g 1) by rw [hg0, hg1]; constructor <;> linarith)
  refine ⟨s ∩ Iic x, inter_subset_left, hs.inter measurableSet_Iic, ?_, ?_⟩
  · rw [← measureReal_pos_iff]; show 0 < g x; rw [hx]; linarith
  · have : μ.real (s ∩ Iic x) < μ.real s := by show g x < _; rw [hx]; linarith
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- Lyapunov for integrals in action: some measurable `B ⊆ [0, 1]` carries
exactly half of the integral of the identity, `∫_B a da = 1/4`. -/
theorem exists_half_integral_id :
    ∃ B ⊆ Icc (0 : ℝ) 1, MeasurableSet B ∧
      ∫ a in B, (fun _ : Fin 1 => a) ∂(volume.restrict (Icc (0 : ℝ) 1)) =
        (1 / 2 : ℝ) • ∫ a in Icc (0 : ℝ) 1, (fun _ : Fin 1 => a) ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
  exists_subset_setIntegral_eq_smul nonatomic_volume_Icc
    (Continuous.integrableOn_Icc (f := fun a : ℝ => fun _ : Fin 1 => a)
      (continuous_pi fun _ => continuous_id) : IntegrableOn _ _ _) measurableSet_Icc
    (by norm_num) (by norm_num)

end Lyapunov
end Econ
