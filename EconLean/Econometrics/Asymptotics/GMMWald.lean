/-
# Wald tests after efficient two-step GMM

Hansen (1982) Thm 3.2; Newey and McFadden (1994) §9.1 (Thm 9.2); Hayashi, *Econometrics*
(2000), Prop. 3.5 and §3.7 (testing linear restrictions).

After efficient GMM with weight `Ŵₙ = Ŝₙ⁻¹`, the asymptotic variance of `√n (θ̂ₙ − θ₀)` is
`V = (GᵀS⁻¹G)⁻¹`, estimated by `V̂ₙ = (ĜₙᵀŜₙ⁻¹Ĝₙ)⁻¹` (`avarHat`). For `H₀ : Rθ₀ = c` with `R`
of full row rank, the Wald statistic built from `θ̂ₙ` and `V̂ₙ` converges in distribution to
`χ²(q)` and the test rejecting when `Wₙ > a` has asymptotic rejection probability
`P(χ²(q) > a)` (`two_step_wald`).
-/
module

public import EconLean.Econometrics.Asymptotics.ChiSquaredTests

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}
  {k l q : Type*} [Fintype k] [Fintype l] [Fintype q] [DecidableEq k] [DecidableEq l]
  [DecidableEq q]

/-- The estimated efficient-GMM asymptotic variance `(ĜᵀŜ⁻¹Ĝ)⁻¹` of `p = (Ĝ, Ŝ)`. -/
noncomputable def avarHat (p : (l → k → ℝ) × (l → l → ℝ)) : k → k → ℝ :=
  invFn (Matrix.of.symm (gram (p.1, invFn p.2)))

omit [Fintype q] [DecidableEq q] in
lemma measurable_avarHat : Measurable (avarHat (k := k) (l := l)) :=
  measurable_invFn.comp (continuous_gram.measurable.comp
    (measurable_fst.prodMk (measurable_invFn.comp measurable_snd)))

omit [Fintype q] [DecidableEq q] in
lemma avarHat_eq (G : l → k → ℝ) (S : Matrix l l ℝ) :
    avarHat (G, Matrix.of.symm S) = Matrix.of.symm ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹ := by
  simp only [avarHat, gram, of_invFn_symm]
  rfl

omit [Fintype q] [DecidableEq q] in
lemma continuousAt_avarHat {G : l → k → ℝ} {S : Matrix l l ℝ} (hS : S.PosDef)
    (hG : Function.Injective (Matrix.of G *ᵥ ·)) :
    ContinuousAt (avarHat (k := k) (l := l)) (G, Matrix.of.symm S) := by
  have hSu : IsUnit (Matrix.of (Matrix.of.symm S)).det := by
    rw [Equiv.apply_symm_apply]; exact (isUnit_iff_isUnit_det _).mp hS.isUnit
  have h0 : ContinuousAt (invFn (l := l)) (Matrix.of.symm S) := continuousAt_invFn hSu
  have h1 : ContinuousAt (fun p : (l → k → ℝ) × (l → l → ℝ) => invFn p.2) (G, Matrix.of.symm S) :=
    ContinuousAt.comp (g := invFn (l := l))
      (f := (Prod.snd : (l → k → ℝ) × (l → l → ℝ) → l → l → ℝ)) (x := (G, Matrix.of.symm S))
      h0 continuousAt_snd
  have hpair : ContinuousAt (fun p : (l → k → ℝ) × (l → l → ℝ) => (p.1, invFn p.2))
      (G, Matrix.of.symm S) := continuousAt_fst.prodMk h1
  have hin : ContinuousAt (gram (k := k) (l := l) ∘ fun p : (l → k → ℝ) × (l → l → ℝ) =>
      (p.1, invFn p.2)) (G, Matrix.of.symm S) :=
    ContinuousAt.comp (g := gram (k := k) (l := l)) (x := (G, Matrix.of.symm S))
      continuous_gram.continuousAt hpair
  have hg : IsUnit (Matrix.of (gram (G, invFn (Matrix.of.symm S)) : k → k → ℝ)).det :=
    rank_two_step hS hG
  have hg' : ContinuousAt (invFn (l := k)) (gram (G, invFn (Matrix.of.symm S))) :=
    continuousAt_invFn hg
  exact ContinuousAt.comp (g := invFn (l := k)) (x := (G, Matrix.of.symm S)) hg' hin

/-- **Wald test after efficient two-step GMM** (Newey and McFadden 1994 Thm 9.2; Hayashi
§3.7): under the assumptions of `two_step_gmm` with `L ∼ N(0, S)`, `H₀ : Rθ₀ = c` and `R` of
full row rank, the Wald statistic with `V̂ₙ = (ĜₙᵀŜₙ⁻¹Ĝₙ)⁻¹` converges in distribution to
`(RAL)ᵀ(RVRᵀ)⁻¹(RAL) ∼ χ²(q)` (`A` the efficient GMM matrix, `V = (GᵀS⁻¹G)⁻¹`). Here `Ŝₙ` is
any consistent estimate of `S` (Hayashi Prop. 3.5); `FirstStepGMM` builds one from residuals.
The test rejecting when `Wₙ > a` has asymptotic rejection probability
`P(χ²(q) > a)` when `q ≥ 1`. -/
theorem two_step_wald [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Ghat : ℕ → Ω → l → k → ℝ} {Shat : ℕ → Ω → l → l → ℝ} {g : ℕ → Ω → l → ℝ}
    {G : l → k → ℝ} {S : Matrix l l ℝ} {θ₀ : k → ℝ} {L : Ω' → l → ℝ}
    (hS : S.PosDef) (hG : Function.Injective (Matrix.of G *ᵥ ·))
    (hGhat : TendstoInMeasure P Ghat atTop (fun _ => G))
    (hShat : TendstoInMeasure P Shat atTop (fun _ => Matrix.of.symm S))
    (hg : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • g n ω) atTop L
      (fun _ => P) P')
    (hGm : ∀ n, AEMeasurable (Ghat n) P) (hSm : ∀ n, AEMeasurable (Shat n) P)
    (hgm : ∀ n, AEMeasurable (g n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp)
    (R : Matrix q k ℝ) (c : q → ℝ) (hnull : R *ᵥ θ₀ = c)
    (hR : Function.Injective (Rᵀ *ᵥ ·)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => waldStat n R c (GMM.estimator (Matrix.of (invFn (Shat n ω)))
        (Matrix.of (Ghat n ω)) (Matrix.of (Ghat n ω) *ᵥ θ₀ + g n ω))
        (avarHat (Ghat n ω, Shat n ω))) atTop
      (fun ω => (R *ᵥ (Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω)) ⬝ᵥ
        ((R * ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹ * Rᵀ)⁻¹ *ᵥ
          (R *ᵥ (Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω)))) (fun _ => P) P' ∧
    P'.map (fun ω => (R *ᵥ (Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω)) ⬝ᵥ
        ((R * ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹ * Rᵀ)⁻¹ *ᵥ
          (R *ᵥ (Matrix.of (gmmA (G, invFn (Matrix.of.symm S))) *ᵥ L ω))))
      = chiSq (Fintype.card q) ∧
    (0 < Fintype.card q → ∀ a : ℝ,
      Tendsto (fun n => P {ω | a < waldStat n R c (GMM.estimator (Matrix.of (invFn (Shat n ω)))
        (Matrix.of (Ghat n ω)) (Matrix.of (Ghat n ω) *ᵥ θ₀ + g n ω))
        (avarHat (Ghat n ω, Shat n ω))}) atTop (𝓝 (chiSq (Fintype.card q) (Set.Ioi a)))) := by
  set V : Matrix k k ℝ := ((Matrix.of G)ᵀ * S⁻¹ * Matrix.of G)⁻¹ with hVdef
  have hVpd : V.PosDef := (GMM.posDef_gram hS.inv hG).inv
  have hRV : IsUnit (R * V * Rᵀ).det := by
    have := GMM.posDef_gram hVpd hR
    rw [transpose_transpose] at this
    exact (isUnit_iff_isUnit_det _).mp this.isUnit
  obtain ⟨hT, hTlaw⟩ := two_step_gmm (θ₀ := θ₀) hS hG hGhat hShat hg hGm hSm hgm
  set A := Matrix.of (gmmA (G, invFn (Matrix.of.symm S)))
  have hAL : Measurable (fun ω => A *ᵥ L ω) :=
    (by fun_prop : Continuous (fun x : l → ℝ => A *ᵥ x)).measurable.comp hL
  have hV : TendstoInMeasure P (fun n ω => avarHat (Ghat n ω, Shat n ω)) atTop
      (fun _ => Matrix.of.symm V) := by
    have h := tendstoInMeasure_comp_continuousAt
      (tendstoInMeasure_prodMk (E := l → k → ℝ) (F := l → l → ℝ) hGhat hShat)
      (continuousAt_avarHat hS hG)
    rw [avarHat_eq] at h
    exact h
  have hVm : ∀ n, AEMeasurable (fun ω => avarHat (Ghat n ω, Shat n ω)) P := fun n =>
    measurable_avarHat.comp_aemeasurable ((hGm n).prodMk (hSm n))
  have hW := wald_chiSq R c hnull hRV hVpd.posSemidef hT hV hVm hAL (hTlaw hL hlaw)
  exact ⟨wald_tendsto R c hnull hRV hT hV hVm, hW.1, hW.2⟩

/-- **Non-vacuity**: in the overidentified example of `two_step_witness` (`l = 2`, `k = 1`,
`S = diag(1, 2)`, `G = (1, 1)ᵀ`), testing `H₀ : θ = 0` (`R = 1`) with the efficient two-step
estimator and `V̂ₙ = (ĜₙᵀŜₙ⁻¹Ĝₙ)⁻¹`, the Wald test has asymptotic rejection probability
`P(χ²(1) > a)`. -/
theorem two_step_wald_witness (a : ℝ) :
    let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]
    let G : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 S).map ofLp
    ∃ _ : IsProbabilityMeasure P,
      Tendsto (fun n => P {ω | a < waldStat n (1 : Matrix (Fin 1) (Fin 1) ℝ) 0
          (GMM.estimator (Matrix.of (invFn (Matrix.of.symm S))) (Matrix.of G)
            (Matrix.of G *ᵥ 0 + (Real.sqrt n)⁻¹ • ω))
          (avarHat (G, Matrix.of.symm S))})
        atTop (𝓝 (chiSq 1 (Set.Ioi a))) := by
  intro S G P
  obtain ⟨hP, hS, hG, hGc, hSc, ⟨_, hg⟩, hL, hlaw⟩ := two_step_witness
  refine ⟨hP, ?_⟩
  have hR : Function.Injective ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ ·) := by
    intro x y h
    simpa using h
  have := (two_step_wald (θ₀ := (0 : Fin 1 → ℝ)) hS hG hGc hSc hg
    (fun _ => aemeasurable_const) (fun _ => aemeasurable_const) (fun n => by fun_prop) hL hlaw
    1 0 (mulVec_zero _) hR).2.2 (by simp) a
  simpa using this

end Econ.Asymptotics
