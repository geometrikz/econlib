/-
# Strong consistency of OLS

Hayashi, *Econometrics* (2000), Prop. 2.1(a); Wooldridge (2010), Thm 4.1;
White, *Asymptotic Theory for Econometricians* (2001), Thm 3.5.

**The result.** In `y_i = x_iᵀ β + ε_i` with `(x_i, ε_i)` i.i.d. (pairwise
independence suffices), finite second moments `E[x xᵀ]`, exogeneity
`E[x ε] = 0`, and the rank condition `E[x xᵀ]` nonsingular, the OLS estimator
from the first `n` observations converges to `β` almost surely.

**Proof.** `β̂_n = S_n⁻¹ (S_n β + m_n)` with `S_n = n⁻¹ ∑ x_i x_iᵀ` and
`m_n = n⁻¹ ∑ x_i ε_i`, once `S_n` is invertible. Etemadi's strong law
(`ProbabilityTheory.strong_law_ae`) gives `S_n → E[x xᵀ]` and `m_n → 0` a.s.,
and matrix inversion is continuous at a nonsingular matrix
(`continuousAt_matrix_inv`).

**Encoding.** Hayashi's ergodic-stationary assumption is replaced by the i.i.d.
special case, the setting of Mathlib's strong law. `x_i` takes values in
`k → ℝ`; the OLS estimator is `OLS.ols` applied to the `n × k` design matrix.
-/
module

public import EconLean.Econometrics.OLS
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k : Type*} [Fintype k]

/-- The `n × k` design matrix of the first `n` observations. -/
def designMatrix (x : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin n) k ℝ :=
  Matrix.of fun i j => x i ω j

/-- The population second-moment matrix `E[x xᵀ]`. -/
noncomputable def secondMoment (μ : Measure Ω) (x : Ω → k → ℝ) : Matrix k k ℝ :=
  Matrix.of fun a b => ∫ ω, x ω a * x ω b ∂μ

omit [Fintype k] in
lemma gram_designMatrix (x : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) :
    (designMatrix x n ω)ᵀ * designMatrix x n ω
      = Matrix.of fun a b => ∑ i ∈ range n, x i ω a * x i ω b := by
  ext a b
  simp only [designMatrix, Matrix.mul_apply, Matrix.transpose_apply, of_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => x i ω a * x i ω b) n

omit [Fintype k] in
lemma transpose_designMatrix_mulVec (x : ℕ → Ω → k → ℝ) (v : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    (designMatrix x n ω)ᵀ *ᵥ (fun i : Fin n => v i)
      = fun a => ∑ i ∈ range n, x i ω a * v i := by
  funext a
  simp only [designMatrix, mulVec, dotProduct, transpose_apply, of_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => x i ω a * v i) n

variable [DecidableEq k]

/-- **Strong consistency of OLS** (Hayashi Prop. 2.1(a), i.i.d. case). -/
theorem ols_consistent [IsProbabilityMeasure μ] (x : ℕ → Ω → k → ℝ) (ε : ℕ → Ω → ℝ)
    (β : k → ℝ)
    (hindep : Pairwise fun i j =>
      (fun ω => (x i ω, ε i ω)) ⟂ᵢ[μ] (fun ω => (x j ω, ε j ω)))
    (hident : ∀ i, IdentDistrib (fun ω => (x i ω, ε i ω)) (fun ω => (x 0 ω, ε 0 ω)) μ μ)
    (hxx : ∀ a b, Integrable (fun ω => x 0 ω a * x 0 ω b) μ)
    (hxε : ∀ a, Integrable (fun ω => x 0 ω a * ε 0 ω) μ)
    (hexo : ∀ a, ∫ ω, x 0 ω a * ε 0 ω ∂μ = 0)
    (hrank : IsUnit (secondMoment μ (x 0)).det) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => OLS.ols (designMatrix x n ω)
      (fun i : Fin n => x i ω ⬝ᵥ β + ε i ω)) atTop (𝓝 β) := by
  -- The two i.i.d. sequences of products.
  let φ : (k → ℝ) × ℝ → (k → k → ℝ) := fun p a b => p.1 a * p.1 b
  let ψ : (k → ℝ) × ℝ → (k → ℝ) := fun p a => p.1 a * p.2
  have hφ : Measurable φ := by
    refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
    exact ((measurable_pi_apply a).comp measurable_fst).mul
      ((measurable_pi_apply b).comp measurable_fst)
  have hψ : Measurable ψ := by
    refine Measurable.of_eval fun a => ?_
    exact ((measurable_pi_apply a).comp measurable_fst).mul measurable_snd
  set Q : ℕ → Ω → (k → k → ℝ) := fun i ω => φ (x i ω, ε i ω)
  set M : ℕ → Ω → (k → ℝ) := fun i ω => ψ (x i ω, ε i ω)
  have hQ := strong_law_ae (μ := μ) Q
    (Integrable.of_eval fun a => Integrable.of_eval fun b => hxx a b)
    (fun i j hij => (hindep hij).comp hφ hφ) (fun i => (hident i).comp hφ)
  have hM := strong_law_ae (μ := μ) M (Integrable.of_eval fun a => hxε a)
    (fun i j hij => (hindep hij).comp hψ hψ) (fun i => (hident i).comp hψ)
  have hQlim : (∫ ω, Q 0 ω ∂μ : k → k → ℝ) = fun a b => ∫ ω, x 0 ω a * x 0 ω b ∂μ := by
    funext a b
    rw [eval_integral (fun a => Integrable.of_eval fun b => hxx a b) a,
      eval_integral (fun b => hxx a b) b]
  have hMlim : (∫ ω, M 0 ω ∂μ : k → ℝ) = 0 := by
    funext a
    rw [eval_integral (fun a => hxε a) a]
    exact hexo a
  rw [hQlim] at hQ
  rw [hMlim] at hM
  filter_upwards [hQ, hM] with ω hQω hMω
  set S : ℕ → Matrix k k ℝ :=
    fun n => Matrix.of fun a b => (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ω a * x i ω b
  set m : ℕ → k → ℝ := fun n a => (n : ℝ)⁻¹ * ∑ i ∈ range n, x i ω a * ε i ω
  have hS : Tendsto S atTop (𝓝 (secondMoment μ (x 0))) := by
    have hSeq : S = fun (n : ℕ) => ((n : ℝ)⁻¹ • ∑ i ∈ range n, Q i ω : k → k → ℝ) := by
      funext n a b
      simp [S, Q, φ, Finset.sum_apply]
    rw [hSeq]; exact hQω
  have hm : Tendsto m atTop (𝓝 0) := by
    have hmeq : m = fun (n : ℕ) => ((n : ℝ)⁻¹ • ∑ i ∈ range n, M i ω : k → ℝ) := by
      funext n a
      simp [m, M, ψ, Finset.sum_apply]
    rw [hmeq]; exact hMω
  -- The limit of `S_n⁻¹ (S_n β + m_n)` is `β`.
  have hinv : Tendsto (fun n => (S n)⁻¹) atTop (𝓝 (secondMoment μ (x 0))⁻¹) := by
    refine (continuousAt_matrix_inv _ ?_).tendsto.comp hS
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hrank.ne_zero
  have hvec : Tendsto (fun n => S n *ᵥ β + m n) atTop
      (𝓝 (secondMoment μ (x 0) *ᵥ β + 0)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _ |>.comp hS).add hm
  have hlim : Tendsto (fun n => (S n)⁻¹ *ᵥ (S n *ᵥ β + m n)) atTop (𝓝 β) := by
    have := ((continuous_fst.matrix_mulVec continuous_snd).tendsto _).comp
      (hinv.prodMk_nhds hvec)
    rwa [add_zero, mulVec_mulVec, nonsing_inv_mul _ hrank, one_mulVec] at this
  -- Eventually `S_n` is invertible and `β̂_n = S_n⁻¹ (S_n β + m_n)`.
  have hdet : ∀ᶠ n in atTop, IsUnit (S n).det := by
    have := (continuous_id.matrix_det.tendsto _).comp hS
    exact (this.eventually (isOpen_ne.mem_nhds hrank.ne_zero)).mono fun n hn => hn.isUnit
  refine hlim.congr' ?_
  filter_upwards [hdet, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hG : (designMatrix x n ω)ᵀ * designMatrix x n ω = (n : ℝ) • S n := by
    rw [gram_designMatrix]
    ext a b
    simp only [S, Matrix.smul_apply, of_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn0,
      one_mul]
  have hy : (designMatrix x n ω)ᵀ *ᵥ (fun i : Fin n => x i ω ⬝ᵥ β + ε i ω)
      = (n : ℝ) • (S n *ᵥ β + m n) := by
    rw [show (fun i : Fin n => x i ω ⬝ᵥ β + ε i ω)
        = designMatrix x n ω *ᵥ β + fun i : Fin n => ε i ω from rfl, mulVec_add, mulVec_mulVec,
      hG, Matrix.smul_mulVec, smul_add]
    congr 1
    rw [transpose_designMatrix_mulVec x (fun i => ε i ω) n ω]
    funext a
    simp only [m, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  show (S n)⁻¹ *ᵥ (S n *ᵥ β + m n) = OLS.ols _ _
  have hinvn : ((n : ℝ) • S n)⁻¹ = (n : ℝ)⁻¹ • (S n)⁻¹ :=
    inv_eq_left_inv (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hn0,
      one_smul, nonsing_inv_mul _ hn])
  rw [OLS.ols, hG, hy, hinvn, Matrix.smul_mulVec, mulVec_smul, smul_smul, inv_mul_cancel₀ hn0,
    one_smul]

/-- **Non-vacuity** of `ols_consistent`: a single constant regressor and zero
errors on a one-point probability space satisfy every hypothesis. -/
theorem ols_consistent_witness :
    let μ : Measure Unit := Measure.dirac ()
    let x : ℕ → Unit → Unit → ℝ := fun _ _ _ => 1
    let ε : ℕ → Unit → ℝ := fun _ _ => 0
    IsProbabilityMeasure μ ∧
    (Pairwise fun i j => (fun ω => (x i ω, ε i ω)) ⟂ᵢ[μ] (fun ω => (x j ω, ε j ω))) ∧
    (∀ i, IdentDistrib (fun ω => (x i ω, ε i ω)) (fun ω => (x 0 ω, ε 0 ω)) μ μ) ∧
    (∀ a b, Integrable (fun ω => x 0 ω a * x 0 ω b) μ) ∧
    (∀ a, Integrable (fun ω => x 0 ω a * ε 0 ω) μ) ∧
    (∀ a, ∫ ω, x 0 ω a * ε 0 ω ∂μ = 0) ∧ IsUnit (secondMoment μ (x 0)).det := by
  intro μ x ε
  refine ⟨inferInstance, fun i j _ => indepFun_const_left (((1 : Unit → ℝ), (0 : ℝ))) _, fun i => IdentDistrib.refl
    (aemeasurable_const (b := ((1 : Unit → ℝ), (0 : ℝ)))), fun a b => integrable_const (1 * 1 : ℝ), fun a => integrable_const (1 * 0 : ℝ),
    fun a => by simp [ε], ?_⟩
  simp [secondMoment, x, μ, Matrix.det_unique]

end Econ.Asymptotics
