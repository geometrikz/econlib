/-
# The χ² distribution and Gaussian quadratic forms

Cochran (1934); Rao, *Linear Statistical Inference* (1973) §3b.4; Hayashi, *Econometrics*
(2000), Fact on quadratic forms (§2.4 and §3.6); Johnson, Kotz and Balakrishnan (1994) ch. 18.

* `chiSq r`: the law of `Z₁² + ⋯ + Z_r²` for independent standard normals; it is a
  probability measure with mean `r` (`integral_chiSq`) and, for `r ≥ 1`, no atoms
  (`chiSq_singleton`).
* **Quadratic forms.** If `z` has independent standard normal coordinates and `M` is
  symmetric and idempotent with trace `r`, then `zᵀ M z ∼ χ²(r)`
  (`map_quadForm_idempotent`). The proof diagonalises `M` in an orthonormal eigenbasis
  (eigenvalues `0` or `1`, the number of ones being the trace) and uses rotation
  invariance of the standard Gaussian.
* More generally, if `L ∼ N(0, S)`, `A` is symmetric, `A S A = A` and `tr(A S) = r`, then
  `Lᵀ A L ∼ χ²(r)` (`map_quadForm_gaussian`).
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Econ.Asymptotics

/-- The χ² distribution with `r` degrees of freedom: the law of the sum of squares of `r`
independent standard normals. -/
noncomputable def chiSq (r : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin r => gaussianReal 0 1).map (fun z => ∑ i, z i ^ 2)

instance (r : ℕ) : IsProbabilityMeasure (chiSq r) :=
  by unfold chiSq; infer_instance

/-- The sum of squares of independent standard normals indexed by any finite type `ι` is
`χ²(|ι|)`. -/
theorem map_sum_sq_eq_chiSq (ι : Type*) [Fintype ι] :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun z => ∑ i, z i ^ 2)
      = chiSq (Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  rw [chiSq, ← hp.map_eq, Measure.map_map (by fun_prop) hp.measurable]
  congr 1
  funext z
  simp only [Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

/-- The sum of squares over a subset `J` of the coordinates is `χ²(|J|)`. -/
theorem map_sum_sq_finset_eq_chiSq {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Finset ι) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun z => ∑ i ∈ J, z i ^ 2)
      = chiSq J.card := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (· ∈ J)
  have hf : (fun z : ι → ℝ => ∑ i ∈ J, z i ^ 2)
      = (fun y : {i // i ∈ J} → ℝ => ∑ i, y i ^ 2) ∘ Prod.fst ∘
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J)) := by
    funext z
    simp only [Function.comp_apply]
    rw [← Finset.sum_coe_sort J]
    rfl
  rw [hf, ← Measure.map_map (by fun_prop) (measurable_fst.comp hp.measurable),
    ← Measure.map_map measurable_fst hp.measurable, hp.map_eq, Measure.map_fst_prod]
  simp only [measure_univ, one_smul]
  convert map_sum_sq_eq_chiSq {i // i ∈ J} using 3
  · simp

/-- The mean of `χ²(r)` is `r`. -/
theorem integral_chiSq (r : ℕ) : ∫ x, x ∂chiSq r = r := by
  have h1 : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have := variance_eq_integral (μ := gaussianReal 0 1) (X := id) aemeasurable_id
    simp only [variance_id_gaussianReal, id, integral_id_gaussianReal, sub_zero,
      NNReal.coe_one] at this
    exact this.symm
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hint : ∀ i : Fin r, Integrable (fun z : Fin r → ℝ => z i ^ 2)
      (Measure.pi fun _ => gaussianReal 0 1) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin r => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => x ^ 2) hsq
  rw [chiSq, integral_map (f := fun x : ℝ => x) (by fun_prop : Measurable (fun z : Fin r → ℝ => ∑ i, z i ^ 2)).aemeasurable aestronglyMeasurable_id,
    integral_finsetSum _ (fun i _ => hint i)]
  have he : ∀ i : Fin r, ∫ z : Fin r → ℝ, z i ^ 2 ∂(Measure.pi fun _ => gaussianReal 0 1) = 1 :=
    fun i => (integral_comp_eval (μ := fun _ : Fin r => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => x ^ 2) hsq.aestronglyMeasurable).trans h1
  simp [he]

/-- **Additivity**: if `X ∼ χ²(a)` and `Y ∼ χ²(b)` are independent then `X + Y ∼ χ²(a + b)`. -/
theorem chiSq_add (a b : ℕ) :
    ((chiSq a).prod (chiSq b)).map (fun p => p.1 + p.2) = chiSq (a + b) := by
  have hp := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin a ⊕ Fin b => gaussianReal 0 1)
  have hf : (fun z : Fin a ⊕ Fin b → ℝ => ∑ i, z i ^ 2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘
        (Prod.map (fun y : Fin a → ℝ => ∑ i, y i ^ 2) (fun y : Fin b → ℝ => ∑ i, y i ^ 2)) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)) := by
    funext z
    simp [Fintype.sum_sum_type, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have h := map_sum_sq_eq_chiSq (Fin a ⊕ Fin b)
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hf,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) hp.measurable, hp.map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)] at h
  exact h

/-- For `r ≥ 1` the χ² distribution has no atoms. -/
theorem chiSq_singleton {r : ℕ} (hr : 0 < r) (c : ℝ) : chiSq r {c} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
  set B : Set (ℝ × (Fin n → ℝ)) := {p | p.1 ^ 2 + ∑ j, p.2 j ^ 2 = c} with hB
  have hBm : MeasurableSet B := measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hpre : (fun z : Fin (n + 1) → ℝ => ∑ i, z i ^ 2) ⁻¹' {c}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹' B := by
    ext z
    simp [hB, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Fin.tail]
  rw [chiSq, Measure.map_apply (by fun_prop) (measurableSet_singleton c), hpre,
    hp.measure_preimage hBm.nullMeasurableSet, Measure.prod_apply_symm hBm]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  set t := c - ∑ j, y j ^ 2
  have hsub : (fun x => (x, y)) ⁻¹' B ⊆ {Real.sqrt t, -Real.sqrt t} := by
    intro x hx
    have hx2 : x ^ 2 = t := by simp only [Set.mem_preimage, hB, Set.mem_ofPred_eq] at hx; linarith
    have habs : |x| = Real.sqrt t := by rw [← hx2, Real.sqrt_sq_eq_abs]
    rcases abs_choice x with h | h
    · left; rw [← habs, h]
    · right; rw [← habs, h, neg_neg]; rfl
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

section Idempotent

variable {l : Type*} [Fintype l] [DecidableEq l] {M : Matrix l l ℝ}

/-- The eigenvalues of an idempotent symmetric matrix are `0` or `1`. -/
lemma eigenvalues_idempotent (hH : M.IsHermitian) (hMM : M * M = M) (i : l) :
    hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
  have h1 := hH.mulVec_eigenvectorBasis i
  have h2 : M *ᵥ (M *ᵥ ⇑(hH.eigenvectorBasis i)) = M *ᵥ ⇑(hH.eigenvectorBasis i) := by
    rw [mulVec_mulVec, hMM]
  rw [h1, mulVec_smul, h1, smul_smul] at h2
  have hne : (⇑(hH.eigenvectorBasis i) : l → ℝ) ≠ 0 := by
    simpa using (hH.eigenvectorBasis.orthonormal.ne_zero i)
  have h3 : (hH.eigenvalues i * hH.eigenvalues i - hH.eigenvalues i)
      • (⇑(hH.eigenvectorBasis i) : l → ℝ) = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · have h4 : hH.eigenvalues i * (hH.eigenvalues i - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (by linarith)
  · exact absurd h hne

/-- In the eigenbasis of a symmetric matrix the quadratic form is diagonal. -/
lemma quadForm_eigenbasis (hH : M.IsHermitian) (w : l → ℝ) :
    ofLp (∑ i, w i • hH.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ofLp (∑ i, w i • hH.eigenvectorBasis i))
      = ∑ i, hH.eigenvalues i * w i ^ 2 := by
  have hb : ∀ i j, (⇑(hH.eigenvectorBasis j) : l → ℝ) ⬝ᵥ ⇑(hH.eigenvectorBasis i)
      = if i = j then 1 else 0 := by
    intro i j
    rw [← orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal i j,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, mulVec_sum, mulVec_smul,
    hH.mulVec_eigenvectorBasis, smul_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, hb, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Quadratic forms in Gaussian vectors.** If `z` is a vector of independent standard
normals and `M` is a symmetric idempotent matrix of trace `r` (an orthogonal projection of
rank `r`), then `zᵀ M z ∼ χ²(r)`. -/
theorem map_quadForm_idempotent (hM : Mᵀ = M) (hMM : M * M = M) {r : ℕ} (htr : M.trace = r) :
    (Measure.pi fun _ : l => gaussianReal 0 1).map (fun z => z ⬝ᵥ (M *ᵥ z)) = chiSq r := by
  have hH : M.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hM]
  set J := Finset.univ.filter fun i => hH.eigenvalues i = 1 with hJ
  have hpi : Measure.pi (fun _ : l => gaussianReal 0 1)
      = (stdGaussian (EuclideanSpace ℝ l)).map ofLp := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id.symm
  rw [hpi, stdGaussian_eq_map_pi_orthonormalBasis hH.eigenvectorBasis,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun : ((fun z => z ⬝ᵥ (M *ᵥ z)) ∘ ofLp) ∘ (fun x : l → ℝ => ∑ i, x i • hH.eigenvectorBasis i)
      = fun w => ∑ i ∈ J, w i ^ 2 := by
    funext w
    simp only [Function.comp_apply]
    rw [quadForm_eigenbasis, hJ, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eigenvalues_idempotent hH hMM i with h | h <;> simp [h]
  rw [hfun, map_sum_sq_finset_eq_chiSq]
  have hcard : M.trace = J.card := by
    rw [hH.trace_eq_sum_eigenvalues, hJ, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eigenvalues_idempotent hH hMM i with h | h <;> simp [h]
  congr 1
  exact_mod_cast hcard.symm.trans htr

/-- The law of `N(0, S)` on `l → ℝ` is the image of independent standard normals under the
symmetric square root `S^{1/2}`. -/
lemma map_multivariateGaussian_eq (S : Matrix l l ℝ) :
    (multivariateGaussian 0 S).map ofLp
      = (Measure.pi fun _ : l => gaussianReal 0 1).map (fun z => CFC.sqrt S *ᵥ z) := by
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp [toEuclideanCLM_toLp]

/-- **Quadratic forms in `N(0, S)`.** If `L ∼ N(0, S)` with `S ⪰ 0`, `A` is symmetric,
`A S A = A` and `tr(A S) = r`, then `Lᵀ A L ∼ χ²(r)`. The condition `A S A = A` is
sufficient (the sharp condition is `S A S A S = S A S`); it covers the J and Wald forms. -/
theorem map_quadForm_gaussian {S A : Matrix l l ℝ} (hS : S.PosSemidef) (hA : Aᵀ = A)
    (hASA : A * S * A = A) {r : ℕ} (htr : (A * S).trace = r) :
    ((multivariateGaussian 0 S).map ofLp).map (fun y => y ⬝ᵥ (A *ᵥ y)) = chiSq r := by
  set R := CFC.sqrt S with hRdef
  have hR : Rᵀ = R := by
    have h0 : R.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
    have := h0.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  rw [map_multivariateGaussian_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  have hq : (fun y => y ⬝ᵥ (A *ᵥ y)) ∘ (fun z => R *ᵥ z)
      = fun z => z ⬝ᵥ ((R * A * R) *ᵥ z) := by
    funext z
    simp only [Function.comp_apply]
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    conv_rhs => rw [dotProduct_mulVec, ← mulVec_transpose, hR]
  rw [hq]
  refine map_quadForm_idempotent ?_ ?_ ?_
  · rw [transpose_mul, transpose_mul, hR, hA, Matrix.mul_assoc]
  · calc R * A * R * (R * A * R) = R * (A * (R * R) * A) * R := by
          simp only [Matrix.mul_assoc]
      _ = R * A * R := by rw [hRR, hASA, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hRR, htr]

end Idempotent

end Econ.Asymptotics
