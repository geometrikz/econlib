/-
# Linear GMM: consistency and asymptotic normality

Hansen, "Large sample properties of generalized method of moments estimators",
*Econometrica* (1982), Thm 2.1 and 3.1; Hayashi, *Econometrics* (2000),
Prop. 3.1 and 3.3; Newey and McFadden (1994), Thm 2.6 and 3.4.

**Setup.** Linear moments `E[zᵢ (yᵢ − xᵢᵀθ₀)] = 0`. With sample moments
`Ŝₙ = n⁻¹ Σ zᵢ xᵢᵀ`, `ŝₙ = n⁻¹ Σ zᵢ yᵢ` and `ĝₙ = n⁻¹ Σ zᵢ uᵢ`, the model gives
the exact identity `ŝₙ = Ŝₙ θ₀ + ĝₙ`. The GMM estimator with weighting `Ŵₙ` is
`θ̂ₙ = (ŜₙᵀŴₙŜₙ)⁻¹ ŜₙᵀŴₙ ŝₙ` (`GMM.estimator`).

**The results.**

* **Consistency** (Hayashi Prop. 3.1): if `Ŝₙ →p G`, `Ŵₙ →p W`, `ĝₙ →p 0` and
  `GᵀWG` is invertible (rank condition), then `θ̂ₙ →p θ₀`.
* **Asymptotic normality** (Hayashi Prop. 3.3): if in addition `√n ĝₙ →d L`
  (by the CLT, `L ~ N(0, S)` with `S = E[uᵢ² zᵢ zᵢᵀ]`), then
  `√n (θ̂ₙ − θ₀) →d A L` with `A = (GᵀWG)⁻¹ GᵀW`. The limit is Gaussian when `L`
  is, and its covariance `A S Aᵀ` is the sandwich `GMM.avar W G S`
  (`avar_eq_sandwich`); with `W = S⁻¹` it is `(GᵀS⁻¹G)⁻¹`, the efficiency bound
  of `GMM.avar_sub_posSemidef`.

The law of large numbers and the CLT for the sample moments are hypotheses
(their Mathlib versions are scalar; PLAN item F27). Since the moments are
linear, no uniform law of large numbers or mean-value expansion is needed: the
estimator is a continuous function of `(Ŝₙ, Ŵₙ, ĝₙ)` near the limit, and the
results follow from the continuous mapping theorem and Slutsky's theorem
(`Asymptotics.Extremum`). Matrices are passed as functions so that they carry
the sup norm.
-/
module

public import EconLean.Econometrics.Asymptotics.Extremum
public import EconLean.Econometrics.GMM

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k]

/-- The weighted Gram matrix `SᵀWS` of `p = (S, W)`. -/
def gram (p : (l → k → ℝ) × (l → l → ℝ)) : Matrix k k ℝ :=
  (Matrix.of p.1)ᵀ * Matrix.of p.2 * Matrix.of p.1

/-- The cross product `SᵀW` of `p = (S, W)`. -/
def cross (p : (l → k → ℝ) × (l → l → ℝ)) : Matrix k l ℝ :=
  (Matrix.of p.1)ᵀ * Matrix.of p.2

omit [DecidableEq k] [Fintype k] in
lemma continuous_gram : Continuous (gram (k := k) (l := l)) := by
  unfold gram; fun_prop

omit [DecidableEq k] [Fintype k] in
lemma continuous_cross : Continuous (cross (k := k) (l := l)) := by
  unfold cross; fun_prop

/-- The GMM "influence matrix" `A(S, W) = (SᵀWS)⁻¹ SᵀW`, as a function of
`(S, W)` in function form. -/
noncomputable def gmmA (p : (l → k → ℝ) × (l → l → ℝ)) : k → l → ℝ :=
  Matrix.of.symm ((gram p)⁻¹ * cross p)

/-- The estimator is `A(S, W) ŝ`. -/
lemma estimator_eq_gmmA (S : l → k → ℝ) (W : l → l → ℝ) (s : l → ℝ) :
    GMM.estimator (Matrix.of W) (Matrix.of S) s = Matrix.of (gmmA (S, W)) *ᵥ s := by
  rw [GMM.estimator, gmmA, Equiv.apply_symm_apply, mulVec_mulVec]
  rfl

/-- On the rank condition, `A(S, W) S = I`, so `θ̂ − θ₀ = A(S, W) ĝ`. -/
lemma estimator_sub (S : l → k → ℝ) (W : l → l → ℝ)
    (h : IsUnit (gram (S, W)).det) (θ₀ : k → ℝ) (g : l → ℝ) :
    GMM.estimator (Matrix.of W) (Matrix.of S) (Matrix.of S *ᵥ θ₀ + g) - θ₀
      = Matrix.of (gmmA (S, W)) *ᵥ g := by
  rw [estimator_eq_gmmA, mulVec_add, add_sub_right_comm]
  have : Matrix.of (gmmA (S, W)) *ᵥ (Matrix.of S *ᵥ θ₀) = θ₀ := by
    rw [← estimator_eq_gmmA]; exact GMM.estimator_of_exact h θ₀
  rw [this, sub_self, zero_add]

/-- `A(S, W)` is continuous at any `(G, W)` satisfying the rank condition. -/
lemma continuousAt_gmmA {p₀ : (l → k → ℝ) × (l → l → ℝ)} (h : IsUnit (gram p₀).det) :
    ContinuousAt (gmmA (k := k) (l := l)) p₀ := by
  have hinv : ContinuousAt (fun p => (gram p)⁻¹) p₀ :=
    (continuousAt_matrix_inv (gram p₀) (by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ h.ne_zero)).comp
      continuous_gram.continuousAt
  have hmul : Continuous (fun q : Matrix k k ℝ × Matrix k l ℝ => q.1 * q.2) := by fun_prop
  exact hmul.continuousAt.comp (f := fun p => ((gram p)⁻¹, cross p))
    (hinv.prodMk continuous_cross.continuousAt)

/-- `A(S, W)` is measurable. -/
lemma measurable_gmmA : Measurable (gmmA (k := k) (l := l)) := by
  have hI : Measurable (fun p : (l → k → ℝ) × (l → l → ℝ) =>
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (gram p)))⁻¹ : k → k → ℝ)) :=
    have hg : Continuous (fun p : (l → k → ℝ) × (l → l → ℝ) =>
        (Matrix.of.symm (gram p) : k → k → ℝ)) := continuous_gram
    measurable_inv_of.comp hg.measurable
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have : (fun p : (l → k → ℝ) × (l → l → ℝ) => gmmA p i j)
      = fun p => ∑ m, (Matrix.of.symm (Matrix.of (Matrix.of.symm (gram p)))⁻¹ : k → k → ℝ) i m
          * cross p m j := by
    funext p; simp only [gmmA, Equiv.apply_symm_apply]; rfl
  rw [this]
  refine Finset.measurable_sum _ fun m _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply m).comp ((measurable_pi_apply i).comp hI)
  · exact ((continuous_apply j).comp ((continuous_apply m).comp continuous_cross)).measurable

/-- The open set of `(S, W)` satisfying the rank condition contains a ball. -/
lemma exists_ball_rank {p₀ : (l → k → ℝ) × (l → l → ℝ)} (h : IsUnit (gram p₀).det) :
    ∃ δ > 0, ∀ p : (l → k → ℝ) × (l → l → ℝ), dist p p₀ < δ → IsUnit (gram p).det := by
  have hc : Continuous (fun p : (l → k → ℝ) × (l → l → ℝ) => (gram p).det) :=
    continuous_gram.matrix_det
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_ne_fun hc continuous_const) p₀ h.ne_zero
  exact ⟨δ, hδ, fun p hp => (hball (Metric.mem_ball.mpr hp)).isUnit⟩

/-- **Consistency of linear GMM** (Hansen 1982 Thm 2.1; Hayashi Prop. 3.1). -/
theorem gmm_consistent {S : ℕ → Ω → l → k → ℝ} {W : ℕ → Ω → l → l → ℝ}
    {g : ℕ → Ω → l → ℝ} {G : l → k → ℝ} {W₀ : l → l → ℝ} {θ₀ : k → ℝ}
    (hrank : IsUnit (gram (G, W₀)).det)
    (hS : TendstoInMeasure P S atTop (fun _ => G))
    (hW : TendstoInMeasure P W atTop (fun _ => W₀))
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n ω => GMM.estimator (Matrix.of (W n ω)) (Matrix.of (S n ω))
        (Matrix.of (S n ω) *ᵥ θ₀ + g n ω)) atTop (fun _ => θ₀) := by
  let F : ((l → k → ℝ) × (l → l → ℝ)) × (l → ℝ) → k → ℝ :=
    fun p => θ₀ + Matrix.of (gmmA p.1) *ᵥ p.2
  have hF : ContinuousAt F ((G, W₀), 0) := by
    refine continuousAt_const.add ?_
    have hmv : Continuous (fun q : (k → l → ℝ) × (l → ℝ) => Matrix.of q.1 *ᵥ q.2) := by
      fun_prop
    exact hmv.continuousAt.comp (f := fun p : ((l → k → ℝ) × (l → l → ℝ)) × (l → ℝ) =>
      (gmmA p.1, p.2))
      ((ContinuousAt.comp (g := gmmA)
        (f := fun p : ((l → k → ℝ) × (l → l → ℝ)) × (l → ℝ) => p.1) (x := ((G, W₀), 0))
        (continuousAt_gmmA hrank) continuousAt_fst).prodMk continuousAt_snd)
  have hF0 : F ((G, W₀), 0) = θ₀ := by simp [F]
  have hSW := tendstoInMeasure_prodMk (E := l → k → ℝ) (F := l → l → ℝ) hS hW
  have hp := tendstoInMeasure_prodMk (E := (l → k → ℝ) × (l → l → ℝ)) (F := l → ℝ) hSW hg
  have hFp := tendstoInMeasure_comp_continuousAt hp hF
  rw [hF0] at hFp
  -- the estimator equals `F` near the limit
  obtain ⟨δ, hδ, hball⟩ := exists_ball_rank hrank
  have hsub := tendstoInMeasure_sub_of_eq_near (Y := fun n ω => GMM.estimator
      (Matrix.of (W n ω)) (Matrix.of (S n ω)) (Matrix.of (S n ω) *ᵥ θ₀ + g n ω))
    (X := fun n ω => F ((S n ω, W n ω), g n ω)) hSW hδ
    (fun n ω hd => by
      simp only [F]
      rw [← estimator_sub _ _ (hball _ hd), add_sub_cancel])
  rw [tendstoInMeasure_iff_norm] at hsub hFp ⊢
  intro ε hε
  have hsum := (hsub (ε / 2) (by linarith)).add (hFp (ε / 2) (by linarith))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _))
  simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω ⊢
  by_contra hcon; push Not at hcon
  have := norm_sub_le_norm_sub_add_norm_sub
    (GMM.estimator (Matrix.of (W n ω)) (Matrix.of (S n ω)) (Matrix.of (S n ω) *ᵥ θ₀ + g n ω))
    (F ((S n ω, W n ω), g n ω)) θ₀
  linarith [hcon.1, hcon.2]

/-- **Asymptotic normality of linear GMM** (Hansen 1982 Thm 3.1; Hayashi
Prop. 3.3): `√n (θ̂ₙ − θ₀) →d A L` with `A = (GᵀWG)⁻¹ GᵀW`. -/
theorem gmm_asymptotic_normal [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {S : ℕ → Ω → l → k → ℝ} {W : ℕ → Ω → l → l → ℝ}
    {g : ℕ → Ω → l → ℝ} {G : l → k → ℝ} {W₀ : l → l → ℝ} {θ₀ : k → ℝ} {L : Ω' → l → ℝ}
    (hrank : IsUnit (gram (G, W₀)).det)
    (hS : TendstoInMeasure P S atTop (fun _ => G))
    (hW : TendstoInMeasure P W atTop (fun _ => W₀))
    (hg : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • g n ω) atTop L
      (fun _ => P) P')
    (hSm : ∀ n, AEMeasurable (S n) P) (hWm : ∀ n, AEMeasurable (W n) P)
    (hgm : ∀ n, AEMeasurable (g n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (GMM.estimator (Matrix.of (W n ω)) (Matrix.of (S n ω))
        (Matrix.of (S n ω) *ᵥ θ₀ + g n ω) - θ₀)) atTop
      (fun ω => Matrix.of (gmmA (G, W₀)) *ᵥ L ω) (fun _ => P) P' := by
  have hSW := tendstoInMeasure_prodMk (E := l → k → ℝ) (F := l → l → ℝ) hS hW
  have hA := tendstoInMeasure_comp_continuousAt hSW (continuousAt_gmmA hrank)
  have hAm : ∀ n, AEMeasurable (fun ω => gmmA (S n ω, W n ω)) P := fun n =>
    measurable_gmmA.comp_aemeasurable ((hSm n).prodMk (hWm n))
  have hX := tendstoInDistribution_mulVec hg hA hAm
  obtain ⟨δ, hδ, hball⟩ := exists_ball_rank hrank
  have hsub := tendstoInMeasure_sub_of_eq_near (Y := fun (n : ℕ) ω => Real.sqrt n •
      (GMM.estimator (Matrix.of (W n ω)) (Matrix.of (S n ω))
        (Matrix.of (S n ω) *ᵥ θ₀ + g n ω) - θ₀))
    (X := fun (n : ℕ) ω => Matrix.of (gmmA (S n ω, W n ω)) *ᵥ (Real.sqrt n • g n ω))
    hSW hδ (fun n ω hd => by
      rw [estimator_sub _ _ (hball _ hd), mulVec_smul])
  have hY : ∀ n : ℕ, AEMeasurable (fun ω => Real.sqrt n •
      (GMM.estimator (Matrix.of (W n ω)) (Matrix.of (S n ω))
        (Matrix.of (S n ω) *ᵥ θ₀ + g n ω) - θ₀)) P := by
    intro n
    have hE : ∀ ω, GMM.estimator (Matrix.of (W n ω)) (Matrix.of (S n ω))
        (Matrix.of (S n ω) *ᵥ θ₀ + g n ω)
        = Matrix.of (gmmA (S n ω, W n ω)) *ᵥ (Matrix.of (S n ω) *ᵥ θ₀ + g n ω) :=
      fun ω => estimator_eq_gmmA _ _ _
    simp_rw [hE]
    have hc : Continuous (fun p : (k → l → ℝ) × (l → k → ℝ) × (l → ℝ) =>
        Real.sqrt n • (Matrix.of p.1 *ᵥ (Matrix.of p.2.1 *ᵥ θ₀ + p.2.2) - θ₀)) := by
      fun_prop
    have h2 := hc.measurable.comp_aemeasurable ((hAm n).prodMk ((hSm n).prodMk (hgm n)))
    exact h2
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hX hsub hY

/-- A Gaussian limit for `√n ĝₙ` gives a Gaussian limit for `√n (θ̂ₙ − θ₀)`. -/
theorem gmm_limit_gaussian [IsProbabilityMeasure P'] {G : l → k → ℝ} {W₀ : l → l → ℝ}
    {L : Ω' → l → ℝ} (hL : Measurable L) [IsGaussian (P'.map L)] :
    IsGaussian (P'.map (fun ω => Matrix.of (gmmA (G, W₀)) *ᵥ L ω)) := by
  let T : (l → ℝ) →L[ℝ] (k → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.of (gmmA (G, W₀))).mulVecLin
  have : (fun ω => Matrix.of (gmmA (G, W₀)) *ᵥ L ω) = T ∘ L := by
    funext ω; simp [T]
  rw [this, ← Measure.map_map T.continuous.measurable hL]
  infer_instance

/-- The covariance of the limit, `A S Aᵀ`, is the sandwich `GMM.avar W G S`. -/
theorem avar_eq_sandwich {G : Matrix l k ℝ} {W : Matrix l l ℝ} (hW : Wᵀ = W)
    (S : Matrix l l ℝ) :
    GMM.avar W G S = ((Gᵀ * W * G)⁻¹ * (Gᵀ * W)) * S * ((Gᵀ * W * G)⁻¹ * (Gᵀ * W))ᵀ := by
  rw [GMM.avar, transpose_mul, transpose_mul, hW, GMM.transpose_inv_gram hW,
    transpose_transpose]
  simp only [Matrix.mul_assoc]

end Econ.Asymptotics
