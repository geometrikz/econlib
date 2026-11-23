/-
# Covariances of Gaussian limits: MLE and GMM

Hayashi, *Econometrics* (2000), Prop. 3.3, 3.5 and 7.9; Newey and McFadden
(1994), Thm 3.1–3.3; van der Vaart (1998), Thm 5.39.

**The results.** A linear image of a centred Gaussian is Gaussian with the
transformed covariance: `A · N(0, Σ) = N(0, A Σ Aᵀ)` (`map_multivariateGaussian`).
Hence, when the score or the sample moments have a Gaussian limit:

* **Z-estimators**: `√n (θ̂ₙ − θ₀) →d N(0, H₀⁻¹ Σ H₀⁻ᵀ)` (`z_estimator_limit_law`).
* **MLE**: with the information equality `H₀ = −I` and score covariance `Σ = I`
  (`I` symmetric, invertible), the limit is `N(0, I⁻¹)` (`mle_limit_law`).
* **Linear GMM**: the limit is `N(0, Avar(W))` with the sandwich
  `Avar(W) = (GᵀWG)⁻¹ GᵀWSWG (GᵀWG)⁻¹`, and with `W = S⁻¹` it is
  `N(0, (GᵀS⁻¹G)⁻¹)` (`gmm_limit_law`, `gmm_limit_law_efficient`).

**Encoding.** Mathlib's `multivariateGaussian μ S` lives on `EuclideanSpace ℝ ι`;
the limit variables of `Asymptotics.Extremum` live in `ι → ℝ`. A limit `L` is
`N(0, S)` when `P'.map L = (multivariateGaussian 0 S).map ofLp`.
-/
module

public import EconLean.Econometrics.Asymptotics.GMMAsymptotics
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Matrix WithLp

variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-- The continuous linear map of a matrix on Euclidean spaces. -/
noncomputable def euclidCLM (A : Matrix k l ℝ) : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ k :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

omit [DecidableEq k] in
lemma euclidCLM_apply (A : Matrix k l ℝ) (x : EuclideanSpace ℝ l) :
    euclidCLM A x = toLp 2 (A *ᵥ ofLp x) := rfl

lemma adjoint_euclidCLM (A : Matrix k l ℝ) : (euclidCLM A).adjoint = euclidCLM Aᵀ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  simp only [euclidCLM_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  exact dotProduct_comm _ _

/-- **Linear images of centred Gaussians**: `A · N(0, Σ) = N(0, A Σ Aᵀ)`. -/
theorem map_multivariateGaussian (A : Matrix k l ℝ) {S : Matrix l l ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (euclidCLM A) = multivariateGaussian 0 (A * S * Aᵀ) := by
  have hASA : (A * S * Aᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same A
  refine IsGaussian.ext ?_ ?_
  · rw [integral_id_multivariateGaussian']
    rw [show (Measure.map (euclidCLM A) (multivariateGaussian 0 S))[id]
        = euclidCLM A ((multivariateGaussian 0 S)[id]) from
      (euclidCLM A).integral_id_map IsGaussian.integrable_id]
    simp
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hASA, adjoint_euclidCLM, euclidCLM_apply,
      euclidCLM_apply]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ A, mulVec_transpose,
      mulVec_transpose]

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}

/-- **Law of a linear image of a Gaussian limit**: if `L ~ N(0, S)` then
`A L ~ N(0, A S Aᵀ)`. -/
theorem map_mulVec_of_gaussian {L : Ω' → l → ℝ} (hL : Measurable L) {S : Matrix l l ℝ}
    (hS : S.PosSemidef) (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp)
    (A : Matrix k l ℝ) :
    P'.map (fun ω => A *ᵥ L ω) = (multivariateGaussian 0 (A * S * Aᵀ)).map ofLp := by
  have hmv : Measurable (fun x : l → ℝ => A *ᵥ x) := (Continuous.matrix_mulVec
    continuous_const continuous_id).measurable
  have hofLp : Measurable (ofLp : EuclideanSpace ℝ l → l → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hofLp' : Measurable (ofLp : EuclideanSpace ℝ k → k → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  rw [← map_multivariateGaussian A hS, Measure.map_map hofLp' (euclidCLM A).continuous.measurable,
    show (fun ω => A *ᵥ L ω) = (fun x => A *ᵥ x) ∘ L from rfl, ← Measure.map_map hmv hL, hlaw,
    Measure.map_map hmv hofLp]
  rfl

/-- **Covariance of the Z-estimator limit** (Newey–McFadden Thm 3.1): with
`L ~ N(0, Σ)`, the limit `−H₀⁻¹ L` of `z_estimator_asymptotic` is
`N(0, H₀⁻¹ Σ H₀⁻ᵀ)`. -/
theorem z_estimator_limit_law {L : Ω' → k → ℝ} (hL : Measurable L) {V : Matrix k k ℝ}
    (hV : V.PosSemidef) (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp)
    (H₀ : Matrix k k ℝ) :
    P'.map (fun ω => -(H₀⁻¹ *ᵥ L ω))
      = (multivariateGaussian 0 (H₀⁻¹ * V * H₀⁻¹ᵀ)).map ofLp := by
  have := map_mulVec_of_gaussian hL hV hlaw (-H₀⁻¹)
  simp only [neg_mulVec, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at this
  exact this

/-- **Asymptotic efficiency form of the MLE limit**: with the information
equality (`H₀ = −I`, score covariance `I`, `I` symmetric and invertible), the
Z-estimator limit is `N(0, I⁻¹)`. The information equality is assumed (as
`H₀ = −I` and score covariance `I`), not derived from the density. -/
theorem mle_limit_law {L : Ω' → k → ℝ} (hL : Measurable L) {I : Matrix k k ℝ}
    (hI : I.PosSemidef) (hIu : IsUnit I.det) (hlaw : P'.map L = (multivariateGaussian 0 I).map ofLp) :
    P'.map (fun ω => -((-I)⁻¹ *ᵥ L ω)) = (multivariateGaussian 0 I⁻¹).map ofLp := by
  have hIt : Iᵀ = I := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hI.1
  rw [z_estimator_limit_law hL hI hlaw (-I)]
  congr 2
  have hneg : (-I)⁻¹ = -I⁻¹ :=
    inv_eq_left_inv (by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, nonsing_inv_mul _ hIu])
  rw [hneg, transpose_neg, transpose_nonsing_inv, hIt]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [nonsing_inv_mul _ hIu, Matrix.one_mul]

/-- **Covariance of the GMM limit** (Hayashi Prop. 3.3(a)): with `L ~ N(0, S)` and
symmetric `W`, the limit `A L` of `gmm_asymptotic_normal` is `N(0, Avar(W))`. -/
theorem gmm_limit_law {L : Ω' → l → ℝ} (hL : Measurable L) {S : Matrix l l ℝ}
    (hS : S.PosSemidef) (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp)
    {G : l → k → ℝ} {W₀ : l → l → ℝ} (hW : (Matrix.of W₀)ᵀ = Matrix.of W₀) :
    P'.map (fun ω => Matrix.of (gmmA (G, W₀)) *ᵥ L ω)
      = (multivariateGaussian 0 (GMM.avar (Matrix.of W₀) (Matrix.of G) S)).map ofLp := by
  rw [map_mulVec_of_gaussian hL hS hlaw, avar_eq_sandwich hW]
  rfl

/-- **Efficient GMM limit** (Hansen 1982; Hayashi Prop. 3.5): with `W = S⁻¹`
(`S` positive definite) and full-column-rank `G`, the limit is
`N(0, (Gᵀ S⁻¹ G)⁻¹)`. -/
theorem gmm_limit_law_efficient {L : Ω' → l → ℝ} (hL : Measurable L) {S : Matrix l l ℝ}
    (hS : S.PosDef) (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp)
    {G : l → k → ℝ} (hG : Function.Injective (Matrix.of G *ᵥ ·)) {W₀ : l → l → ℝ}
    (hW₀ : Matrix.of W₀ = S⁻¹) :
    P'.map (fun ω => Matrix.of (gmmA (G, W₀)) *ᵥ L ω)
      = (multivariateGaussian 0 ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹).map ofLp := by
  have hW : (Matrix.of W₀)ᵀ = Matrix.of W₀ := by
    rw [hW₀]; exact GMM.transpose_eq_of_posDef hS.inv
  rw [gmm_limit_law hL hS.posSemidef hlaw hW, hW₀, GMM.avar_inv hS hG]

end Econ.Asymptotics
