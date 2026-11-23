/-
# Extremum estimators: consistency, MLE identification, asymptotic normality

Newey and McFadden, "Large sample estimation and hypothesis testing",
*Handbook of Econometrics* IV (1994), Thm 2.1 and Thm 3.1; Hayashi,
*Econometrics* (2000), Prop. 7.1 and 7.8; van der Vaart, *Asymptotic Statistics*
(1998), Thm 5.7 and §5.3; Coretto (2026).

**The results.**

* **Consistency of extremum estimators** (Newey–McFadden Thm 2.1): on a compact
  parameter space, if the population criterion `Q₀` is continuous and uniquely
  maximised at `θ₀`, and the sample criterion converges to `Q₀` uniformly in
  probability, then any approximate maximiser `θ̂ₙ` is consistent.
* **Information inequality** (identification of the MLE, Newey–McFadden
  Lemma 2.2): if the model `θ ↦ P_θ` is identified (injective), the
  Kullback–Leibler divergence `KL(P_θ₀ ‖ P_θ)` is positive for `θ ≠ θ₀`. Hence
  the expected log-likelihood, which equals a constant minus this divergence, is
  uniquely maximised at `θ₀`; with the uniform law of large numbers this gives
  **consistency of the MLE**.
* **Asymptotic normality of Z-estimators** (Newey–McFadden Thm 3.1): if the
  first-order condition admits the expansion `Sₙ + Hₙ (θ̂ₙ − θ₀) = 0`, with
  `√n Sₙ →d L` and `Hₙ →p H₀` invertible, then `√n (θ̂ₙ − θ₀) →d −H₀⁻¹ L`.
  For the MLE, `Sₙ` is the average score, `L ~ N(0, I)` and `H₀ = −I`, so the
  limit is `I⁻¹ L ~ N(0, I⁻¹)`; a Gaussian `L` gives a Gaussian limit
  (`z_estimator_gaussian`).

**Design (as in Coretto 2026).** The probabilistic inputs that Mathlib does not
yet supply are hypotheses: the uniform law of large numbers (PLAN item F25),
the multivariate CLT for the score (F27) and the mean-value expansion of the
first-order condition. Uniform convergence in probability is stated with the
outer measure of the event `∃ θ, δ ≤ |Q̂ₙ(θ) − Q₀(θ)|`, so no measurability of
the supremum is needed. The link between the expected log-likelihood and the
divergence is the hypothesis `hgap`; for models with densities it is the
identity `E_{θ₀}[log f_θ₀ − log f_θ] = KL(P_θ₀ ‖ P_θ)`.

The general tools proved here, reused for GMM: the continuous mapping theorem
for convergence in probability at a point in metric spaces, Slutsky's theorem
for random matrices acting on vectors, and "equal with probability tending to
one" for convergence in distribution.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

/-! ### Consistency of extremum estimators -/

/-- **Consistency of extremum estimators** (Newey–McFadden 1994, Thm 2.1).
`Θ` is a compact metric space, `Q₀` is continuous and uniquely maximised at `θ₀`,
`θ̂ₙ` maximises the sample criterion `Qₙ` up to an error `rₙ →p 0`, and `Qₙ`
converges to `Q₀` uniformly in probability. Then `θ̂ₙ →p θ₀`. -/
theorem extremum_consistent {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {Q₀ : Θ → ℝ} (hQ₀ : Continuous Q₀) {θ₀ : Θ} (hid : ∀ θ, θ ≠ θ₀ → Q₀ θ < Q₀ θ₀)
    {Q : ℕ → Ω → Θ → ℝ} {θhat : ℕ → Ω → Θ} {r : ℕ → Ω → ℝ}
    (hmax : ∀ n ω θ, Q n ω θ ≤ Q n ω (θhat n ω) + r n ω)
    (hr : TendstoInMeasure P r atTop (fun _ => 0))
    (hulln : ∀ δ > 0, Tendsto (fun n => P {ω | ∃ θ, δ ≤ |Q n ω θ - Q₀ θ|}) atTop (𝓝 0)) :
    TendstoInMeasure P θhat atTop (fun _ => θ₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set K : Set Θ := {θ | ε ≤ dist θ θ₀} with hK
  have hKc : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have : ∀ n, {ω | ε ≤ dist (θhat n ω) θ₀} = ∅ := fun n => by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; have : θhat n ω ∈ K := h
      rw [hKe] at this; exact this
    simp [this]
  obtain ⟨θ₁, hθ₁K, hθ₁max⟩ := hKc.exists_isMaxOn hKne hQ₀.continuousOn
  have hθ₁ : θ₁ ≠ θ₀ := by
    intro h; have : ε ≤ dist θ₁ θ₀ := hθ₁K; rw [h, dist_self] at this; linarith
  set η := Q₀ θ₀ - Q₀ θ₁ with hη
  have hηpos : 0 < η := by have := hid θ₁ hθ₁; linarith
  rw [tendstoInMeasure_iff_dist] at hr
  have hsum := (hulln (η / 3) (by linarith)).add (hr (η / 3) (by linarith))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
  by_contra hcon
  push Not at hcon
  obtain ⟨hall, hrω⟩ := hcon
  have h1 := hall (θhat n ω)
  have h2 := hall θ₀
  have h3 := hmax n ω θ₀
  have h4 : Q₀ (θhat n ω) ≤ Q₀ θ₁ := hθ₁max hω
  rw [abs_lt] at h1 h2 hrω
  linarith [h1.1, h1.2, h2.1, h2.2, hrω.1, hrω.2]

/-! ### Identification of the MLE: the information inequality -/

/-- **Information inequality** (Newey–McFadden Lemma 2.2): in an identified
model (`θ ↦ P_θ` injective) of finite measures, `KL(P_θ₀ ‖ P_θ) > 0` for
`θ ≠ θ₀`. -/
theorem klDiv_pos_of_identified {Θ α : Type*} {mα : MeasurableSpace α}
    {Pθ : Θ → Measure α} [∀ θ, IsFiniteMeasure (Pθ θ)] (hinj : Function.Injective Pθ)
    {θ₀ θ : Θ} (h : θ ≠ θ₀) : 0 < InformationTheory.klDiv (Pθ θ₀) (Pθ θ) := by
  rw [pos_iff_ne_zero, Ne, InformationTheory.klDiv_eq_zero_iff]
  exact fun he => h (hinj he).symm

/-- **The expected log-likelihood is uniquely maximised at the truth.** If
`Q₀(θ₀) − Q₀(θ) = KL(P_θ₀ ‖ P_θ)` (finite) and the model is identified, then
`Q₀(θ) < Q₀(θ₀)` for `θ ≠ θ₀`. -/
theorem mle_unique_max {Θ α : Type*} {mα : MeasurableSpace α}
    {Pθ : Θ → Measure α} [∀ θ, IsFiniteMeasure (Pθ θ)] (hinj : Function.Injective Pθ)
    {θ₀ : Θ} {Q₀ : Θ → ℝ}
    (hgap : ∀ θ, Q₀ θ₀ - Q₀ θ = (InformationTheory.klDiv (Pθ θ₀) (Pθ θ)).toReal)
    (hfin : ∀ θ, InformationTheory.klDiv (Pθ θ₀) (Pθ θ) ≠ ⊤) :
    ∀ θ, θ ≠ θ₀ → Q₀ θ < Q₀ θ₀ := by
  intro θ h
  have hpos := klDiv_pos_of_identified hinj h
  have : 0 < (InformationTheory.klDiv (Pθ θ₀) (Pθ θ)).toReal :=
    ENNReal.toReal_pos hpos.ne' (hfin θ)
  linarith [hgap θ]

/-- **Consistency of the maximum likelihood estimator** (Newey–McFadden
Thm 2.5, with the uniform law of large numbers as a hypothesis): compact
parameter space, identified model, continuous expected log-likelihood `Q₀`
whose gap to the truth is the Kullback–Leibler divergence, and an approximate
maximiser of a sample criterion converging uniformly in probability to `Q₀`.
The sample criterion is abstract (for the MLE it is the average log-likelihood);
the likelihood enters only through `hgap`, the identity
`E_{θ₀}[log f_θ₀ − log f_θ] = KL(P_θ₀ ‖ P_θ)`, whose derivation from densities is
left open. -/
theorem mle_consistent {Θ α : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {mα : MeasurableSpace α} {Pθ : Θ → Measure α} [∀ θ, IsFiniteMeasure (Pθ θ)]
    (hinj : Function.Injective Pθ) {θ₀ : Θ} {Q₀ : Θ → ℝ} (hQ₀ : Continuous Q₀)
    (hgap : ∀ θ, Q₀ θ₀ - Q₀ θ = (InformationTheory.klDiv (Pθ θ₀) (Pθ θ)).toReal)
    (hfin : ∀ θ, InformationTheory.klDiv (Pθ θ₀) (Pθ θ) ≠ ⊤)
    {Q : ℕ → Ω → Θ → ℝ} {θhat : ℕ → Ω → Θ} {r : ℕ → Ω → ℝ}
    (hmax : ∀ n ω θ, Q n ω θ ≤ Q n ω (θhat n ω) + r n ω)
    (hr : TendstoInMeasure P r atTop (fun _ => 0))
    (hulln : ∀ δ > 0, Tendsto (fun n => P {ω | ∃ θ, δ ≤ |Q n ω θ - Q₀ θ|}) atTop (𝓝 0)) :
    TendstoInMeasure P θhat atTop (fun _ => θ₀) :=
  extremum_consistent hQ₀ (mle_unique_max hinj hgap hfin) hmax hr hulln

/-! ### Tools: continuous mapping, Slutsky for matrices, equality w.p.→1 -/

omit [MeasurableSpace Ω'] in
/-- **Continuous mapping theorem at a point** for convergence in probability,
in metric spaces. -/
theorem tendstoInMeasure_comp_continuousAt {ι E F : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace F] {l : Filter ι} {X : ι → Ω → E} {c : E}
    (h : TendstoInMeasure P X l (fun _ => c)) {q : E → F} (hq : ContinuousAt q c) :
    TendstoInMeasure P (fun i ω => q (X i ω)) l (fun _ => q c) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hq ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ => zero_le) (fun i => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt; push Not at hlt
  exact absurd (hball hlt) (not_lt.mpr hω)

omit [MeasurableSpace Ω'] in
/-- Joint convergence in probability of a pair to a constant pair. -/
theorem tendstoInMeasure_prodMk {ι E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {l : Filter ι} {X : ι → Ω → E} {Y : ι → Ω → F} {a : E} {b : F}
    (hX : TendstoInMeasure P X l (fun _ => a)) (hY : TendstoInMeasure P Y l (fun _ => b)) :
    TendstoInMeasure P (fun i ω => (X i ω, Y i ω)) l (fun _ => (a, b)) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro ε hε
  have hsum := (hX ε hε).add (hY ε hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _))
  simp only [Set.mem_ofPred_eq, Prod.dist_eq, le_max_iff] at hω
  exact hω

omit [MeasurableSpace Ω'] in
/-- If `Bₙ →p b` and `Yₙ = Xₙ` whenever `Bₙ` lies within `δ` of `b`, then
`Yₙ − Xₙ →p 0`: the two sequences agree with probability tending to one. -/
theorem tendstoInMeasure_sub_of_eq_near {ι E F : Type*} [SeminormedAddCommGroup E]
    [PseudoMetricSpace F] {l : Filter ι} {X Y : ι → Ω → E} {B : ι → Ω → F} {b : F}
    (hB : TendstoInMeasure P B l (fun _ => b)) {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ i ω, dist (B i ω) b < δ → Y i ω = X i ω) :
    TendstoInMeasure P (Y - X) l 0 := by
  rw [tendstoInMeasure_iff_norm]
  rw [tendstoInMeasure_iff_dist] at hB
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hB δ hδ)
    (fun _ => zero_le) (fun i => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω ⊢
  by_contra hlt; push Not at hlt
  rw [heq i ω hlt, sub_self, norm_zero] at hω
  linarith

omit [MeasurableSpace Ω'] in
/-- Variant of `tendstoInMeasure_sub_of_eq_near` with an exceptional event `Eᵢ`
of vanishing probability: if `Yᵢ = Xᵢ` whenever `Bᵢ` is within `δ` of `b` and
`ω ∉ Eᵢ`, then `Yᵢ − Xᵢ →p 0`. -/
theorem tendstoInMeasure_sub_of_eq_near_off {ι E F : Type*} [SeminormedAddCommGroup E]
    [PseudoMetricSpace F] {l : Filter ι} {X Y : ι → Ω → E} {B : ι → Ω → F} {b : F}
    (hB : TendstoInMeasure P B l (fun _ => b)) {δ : ℝ} (hδ : 0 < δ) {Ex : ι → Set Ω}
    (hEx : Tendsto (fun i => P (Ex i)) l (𝓝 0))
    (heq : ∀ i ω, dist (B i ω) b < δ → ω ∉ Ex i → Y i ω = X i ω) :
    TendstoInMeasure P (Y - X) l 0 := by
  rw [tendstoInMeasure_iff_norm]
  rw [tendstoInMeasure_iff_dist] at hB
  intro ε hε
  have hsum := (hB δ hδ).add hEx
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _))
  simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_contra hlt; push Not at hlt
  rw [heq i ω hlt.1 hlt.2, sub_self, norm_zero] at hω
  linarith

variable {k l : Type*} [Fintype k] [Fintype l]

/-- **Slutsky's theorem for random matrices**: if `Vₙ →d L` and `Aₙ →p A`, then
`Aₙ Vₙ →d A L`. Matrices are passed as functions `k → l → ℝ` (sup norm). -/
theorem tendstoInDistribution_mulVec [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {A : ℕ → Ω → k → l → ℝ} {A₀ : k → l → ℝ} {V : ℕ → Ω → l → ℝ} {L : Ω' → l → ℝ}
    (hV : TendstoInDistribution V atTop L (fun _ => P) P')
    (hA : TendstoInMeasure P A atTop (fun _ => A₀)) (hAm : ∀ n, AEMeasurable (A n) P) :
    TendstoInDistribution (fun n ω => Matrix.of (A n ω) *ᵥ V n ω) atTop
      (fun ω => Matrix.of A₀ *ᵥ L ω) (fun _ => P) P' :=
  hV.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (l → ℝ) × (k → l → ℝ) => Matrix.of p.2 *ᵥ p.1)
    (Continuous.matrix_mulVec continuous_snd continuous_fst) hA hAm

/-- The set of square matrices (as functions) with invertible determinant is a
neighbourhood of each of its points. -/
theorem exists_ball_isUnit_det [DecidableEq k] {H₀ : k → k → ℝ}
    (hH₀ : IsUnit (Matrix.of H₀).det) :
    ∃ δ > 0, ∀ H : k → k → ℝ, dist H H₀ < δ → IsUnit (Matrix.of H).det := by
  have hopen : IsOpen {H : k → k → ℝ | (Matrix.of H).det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen H₀ hH₀.ne_zero
  exact ⟨δ, hδ, fun H hH => (hball (Metric.mem_ball.mpr hH)).isUnit⟩

/-- Matrix inversion is continuous at an invertible matrix (functions form). -/
theorem continuousAt_inv_of [DecidableEq k] {H₀ : k → k → ℝ} (hH₀ : IsUnit (Matrix.of H₀).det) :
    ContinuousAt (fun H : k → k → ℝ => ((Matrix.of H)⁻¹ : Matrix k k ℝ)) H₀ := by
  have h := continuousAt_matrix_inv (Matrix.of H₀)
    (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hH₀.ne_zero)
  exact h.comp (f := fun H : k → k → ℝ => Matrix.of H) continuousAt_id

/-- Matrix inversion (functions form) is measurable. -/
theorem measurable_inv_of [DecidableEq k] :
    Measurable (fun H : k → k → ℝ => (Matrix.of.symm (Matrix.of H)⁻¹ : k → k → ℝ)) := by
  have hdet : Continuous (fun H : k → k → ℝ => (Matrix.of H).det) :=
    Continuous.matrix_det continuous_id
  have hadj : Continuous (fun H : k → k → ℝ => (Matrix.of H).adjugate) :=
    Continuous.matrix_adjugate continuous_id
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have : (fun H : k → k → ℝ => (Matrix.of.symm (Matrix.of H)⁻¹ : k → k → ℝ) i j)
      = fun H => ((Matrix.of H).det)⁻¹ * (Matrix.of H).adjugate i j := by
    funext H; simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact hdet.measurable.inv.mul
    ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable

/-! ### Asymptotic normality of Z-estimators (MLE) -/

/-- **Asymptotic normality of Z-estimators** (Newey–McFadden 1994, Thm 3.1;
for the MLE, Hayashi Prop. 7.9). Suppose the first-order condition admits the
expansion `Sₙ + Hₙ (θ̂ₙ − θ₀) = 0` (mean-value form, `Sₙ` the sample score at
`θ₀`) with probability tending to one (it holds whenever `θ̂ₙ` is interior), with
`√n Sₙ →d L` and `Hₙ →p H₀` invertible. Then `√n (θ̂ₙ − θ₀) →d −H₀⁻¹ L`. -/
theorem z_estimator_asymptotic [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [DecidableEq k] {θhat : ℕ → Ω → k → ℝ} {θ₀ : k → ℝ} {S : ℕ → Ω → k → ℝ}
    {H : ℕ → Ω → k → k → ℝ} {H₀ : k → k → ℝ} {L : Ω' → k → ℝ}
    (hH₀ : IsUnit (Matrix.of H₀).det)
    (hexp : Tendsto (fun n => P {ω | S n ω + Matrix.of (H n ω) *ᵥ (θhat n ω - θ₀) ≠ 0})
      atTop (𝓝 0))
    (hH : TendstoInMeasure P H atTop (fun _ => H₀)) (hHm : ∀ n, AEMeasurable (H n) P)
    (hS : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • S n ω) atTop L (fun _ => P) P')
    (hθm : ∀ n, AEMeasurable (θhat n) P) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (θhat n ω - θ₀)) atTop
      (fun ω => -((Matrix.of H₀)⁻¹ *ᵥ L ω)) (fun _ => P) P' := by
  set q : (k → k → ℝ) → k → k → ℝ := fun H => ((-(Matrix.of H)⁻¹ : Matrix k k ℝ) :
      k → k → ℝ) with hq
  have hqc : ContinuousAt q H₀ := (continuousAt_inv_of hH₀).neg
  have hA := tendstoInMeasure_comp_continuousAt hH hqc
  have hAm : ∀ n, AEMeasurable (fun ω => q (H n ω)) P := fun n =>
    (measurable_inv_of.neg.comp_aemeasurable (hHm n) :)
  have hX := tendstoInDistribution_mulVec hS hA hAm
  obtain ⟨δ, hδ, hball⟩ := exists_ball_isUnit_det hH₀
  have heq : ∀ (n : ℕ) ω, dist (H n ω) H₀ < δ →
      ω ∉ {ω | S n ω + Matrix.of (H n ω) *ᵥ (θhat n ω - θ₀) ≠ 0} →
      Real.sqrt n • (θhat n ω - θ₀) = Matrix.of (q (H n ω)) *ᵥ (Real.sqrt n • S n ω) := by
    intro n ω hd hω
    simp only [Set.mem_ofPred_eq, not_not] at hω
    have hu := hball _ hd
    have hlin : Matrix.of (H n ω) *ᵥ (θhat n ω - θ₀) = -S n ω :=
      eq_neg_of_add_eq_zero_right hω
    have hsol : θhat n ω - θ₀ = -((Matrix.of (H n ω))⁻¹ *ᵥ S n ω) := by
      rw [← mulVec_neg, ← hlin, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    rw [hsol]
    show Real.sqrt n • -((Matrix.of (H n ω))⁻¹ *ᵥ S n ω)
      = (-(Matrix.of (H n ω))⁻¹ : Matrix k k ℝ) *ᵥ (Real.sqrt n • S n ω)
    rw [Matrix.mulVec_smul, Matrix.neg_mulVec]
  have hsub := tendstoInMeasure_sub_of_eq_near_off hH hδ hexp heq
  have hY : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n • (θhat n ω - θ₀)) P := fun n =>
    (by fun_prop : Measurable fun x : k → ℝ => Real.sqrt n • (x - θ₀)).comp_aemeasurable (hθm n)
  have := tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX hsub hY
  convert this using 2 with ω
  show _ = (-(Matrix.of H₀)⁻¹ : Matrix k k ℝ) *ᵥ L ω
  rw [Matrix.neg_mulVec]

/-- With a Gaussian limit for the score (for the MLE, `L ~ N(0, I)` by the
multivariate CLT), the limit law of `√n (θ̂ₙ − θ₀)` is Gaussian. -/
theorem z_estimator_gaussian [IsProbabilityMeasure P'] [DecidableEq k] {H₀ : k → k → ℝ}
    {L : Ω' → k → ℝ} (hL : Measurable L) [IsGaussian (P'.map L)] :
    IsGaussian (P'.map (fun ω => -((Matrix.of H₀)⁻¹ *ᵥ L ω))) := by
  let T : (k → ℝ) →L[ℝ] (k → ℝ) :=
    LinearMap.toContinuousLinearMap (-(Matrix.of H₀)⁻¹ : Matrix k k ℝ).mulVecLin
  have : (fun ω => -((Matrix.of H₀)⁻¹ *ᵥ L ω)) = T ∘ L := by
    funext ω; simp [T]
  rw [this, ← Measure.map_map T.continuous.measurable hL]
  infer_instance

end Econ.Asymptotics
