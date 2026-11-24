/-
# χ² limits of the J and Wald statistics

Hansen (1982) Lemma 4.2; Hayashi, *Econometrics* (2000), Prop. 3.6 and §2.4 (Prop. 2.3);
Newey and McFadden (1994) §9.1; Wald (1943).

* The efficient J limit `Lᵀ Q L` with `L ∼ N(0, S)` is `χ²(l − k)` (`jLimit_chiSq`), so the
  two-step J statistic is asymptotically `χ²(l − k)` and a test that rejects when `Jₙ > c`
  has asymptotic rejection probability `P(χ²(l − k) > c)` under correct specification
  (`two_step_jtest_chiSq`, `two_step_feasible_jtest_chiSq`).
* The Wald statistic `Wₙ = n (Rθ̂ₙ − c)ᵀ (R V̂ₙ Rᵀ)⁻¹ (Rθ̂ₙ − c)` for `H₀ : Rθ₀ = c`, with
  `√n (θ̂ₙ − θ₀) →d N(0, V)` and `V̂ₙ →p V`, converges to `χ²(q)`, `q` the number of
  restrictions (`wald_tendsto`, `wald_chiSq`).

**Scope.** "Asymptotic rejection probability" is the pointwise limit of `P(Tₙ > c)` under one
fixed data-generating process satisfying the null; uniformity over the null (size in the
modern sense), local alternatives and power are not covered. Mathlib's matrix inverse is `0`
at singular matrices, so the statistics are `0` (no rejection) when `R V̂ₙ Rᵀ` or `Ŝₙ` is
singular; since the limits are invertible this happens with probability tending to zero and
does not affect the limits.
-/
module

public import EconLean.Econometrics.Asymptotics.ChiSquared
public import EconLean.Econometrics.Asymptotics.FirstStepGMM

@[expose] public section

namespace Econ.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'}

/-- **Asymptotic rejection probability.** If `Tₙ →d Z` with `Z ∼ χ²(r)`, `r ≥ 1`, then the test
rejecting when `Tₙ > c` has `P(Tₙ > c) → P(χ²(r) > c)`. -/
theorem tendsto_prob_gt_of_chiSq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {r : ℕ} (hr : 0 < r)
    (hT : TendstoInDistribution T atTop Z (fun _ => P) P') (hZ : P'.map Z = chiSq r) (c : ℝ) :
    Tendsto (fun n => P {ω | c < T n ω}) atTop (𝓝 (chiSq r (Set.Ioi c))) := by
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hT.tendsto
    (E := Set.Ioi c) (by simp [hZ, chiSq_singleton hr])
  simp only [ProbabilityMeasure.coe_mk, hZ] at key
  refine key.congr fun n => ?_
  rw [Measure.map_apply_of_aemeasurable (hT.forall_aemeasurable n) measurableSet_Ioi]
  rfl

variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

omit [DecidableEq k] [DecidableEq l] in
lemma card_le_of_injective {G : Matrix l k ℝ} (hG : Function.Injective (G *ᵥ ·)) :
    Fintype.card k ≤ Fintype.card l := by
  have := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin G) hG
  simpa using this

/-- **The efficient J limit is χ²(l − k)**: if `L ∼ N(0, S)` then `Lᵀ Q L ∼ χ²(l − k)` for the
efficient J form `Q = S⁻¹ − S⁻¹G(GᵀS⁻¹G)⁻¹GᵀS⁻¹`. -/
theorem jLimit_chiSq {S : Matrix l l ℝ} (hS : S.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) :
    ((multivariateGaussian 0 S).map ofLp).map (fun y => y ⬝ᵥ (jForm S G *ᵥ y))
      = chiSq (Fintype.card l - Fintype.card k) :=
  map_quadForm_gaussian hS.posSemidef (jForm_transpose hS) (jForm_mul_S_mul hS hG)
    (by rw [trace_jForm_mul hS hG, Nat.cast_sub (card_le_of_injective hG)])

/-- The law of `Lᵀ Q L` for a random vector `L ∼ N(0, S)`. -/
theorem map_jLimit_chiSq {S : Matrix l l ℝ} (hS : S.PosDef) {G : Matrix l k ℝ}
    (hG : Function.Injective (G *ᵥ ·)) {L : Ω' → l → ℝ} (hL : Measurable L)
    (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp) :
    P'.map (fun ω => L ω ⬝ᵥ (jForm S G *ᵥ L ω)) = chiSq (Fintype.card l - Fintype.card k) := by
  have hc : Measurable (fun y : l → ℝ => y ⬝ᵥ (jForm S G *ᵥ y)) :=
    (by fun_prop : Continuous (fun y : l → ℝ => y ⬝ᵥ (jForm S G *ᵥ y))).measurable
  rw [show (fun ω => L ω ⬝ᵥ (jForm S G *ᵥ L ω)) = (fun y => y ⬝ᵥ (jForm S G *ᵥ y)) ∘ L from rfl,
    ← Measure.map_map hc hL, hlaw, jLimit_chiSq hS hG]

/-- **The two-step J test is asymptotically χ²(l − k)** (Hansen 1982 Lemma 4.2; Hayashi
Prop. 3.6): under the assumptions of `two_step_jtest` and `L ∼ N(0, S)`, `Jₙ →d Lᵀ Q L` with
`Lᵀ Q L ∼ χ²(l − k)`; if the model is overidentified (`k < l`), the test rejecting when
`Jₙ > c` has asymptotic rejection probability `P(χ²(l − k) > c)`. -/
theorem two_step_jtest_chiSq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Ghat : ℕ → Ω → l → k → ℝ} {Shat : ℕ → Ω → l → l → ℝ} {g : ℕ → Ω → l → ℝ}
    {G : l → k → ℝ} {S : Matrix l l ℝ} {θ₀ : k → ℝ} {L : Ω' → l → ℝ}
    (hS : S.PosDef) (hG : Function.Injective (Matrix.of G *ᵥ ·))
    (hGhat : TendstoInMeasure P Ghat atTop (fun _ => G))
    (hShat : TendstoInMeasure P Shat atTop (fun _ => Matrix.of.symm S))
    (hg : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • g n ω) atTop L
      (fun _ => P) P')
    (hGm : ∀ n, AEMeasurable (Ghat n) P) (hSm : ∀ n, AEMeasurable (Shat n) P)
    (hgm : ∀ n, AEMeasurable (g n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp) :
    TendstoInDistribution
      (fun (n : ℕ) ω => jStat n (Ghat n ω) (invFn (Shat n ω)) (Matrix.of (Ghat n ω) *ᵥ θ₀ + g n ω))
      atTop (fun ω => L ω ⬝ᵥ (jForm S (Matrix.of G) *ᵥ L ω)) (fun _ => P) P' ∧
    P'.map (fun ω => L ω ⬝ᵥ (jForm S (Matrix.of G) *ᵥ L ω))
      = chiSq (Fintype.card l - Fintype.card k) ∧
    (Fintype.card k < Fintype.card l → ∀ c : ℝ,
      Tendsto (fun n => P {ω | c < jStat n (Ghat n ω) (invFn (Shat n ω))
          (Matrix.of (Ghat n ω) *ᵥ θ₀ + g n ω)})
        atTop (𝓝 (chiSq (Fintype.card l - Fintype.card k) (Set.Ioi c)))) := by
  have hJ := (two_step_jtest (θ₀ := θ₀) hS hG hGhat hShat hg hGm hSm hgm).1
  have hmap := map_jLimit_chiSq hS hG hL hlaw
  exact ⟨hJ, hmap, fun hkl c => tendsto_prob_gt_of_chiSq (by omega) hJ hmap c⟩

/-- **Feasible two-step J test is asymptotically χ²(l − k)**: the same conclusion for the J
statistic of `twoStep`, with `Ŝₙ` built from first-step residuals (`two_step_feasible`). -/
theorem two_step_feasible_jtest_chiSq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {z : (n : ℕ) → Ω → Fin n → l → ℝ} {x : (n : ℕ) → Ω → Fin n → k → ℝ}
    {y : (n : ℕ) → Ω → Fin n → ℝ} {W1 : ℕ → Ω → l → l → ℝ}
    {G : l → k → ℝ} {W₁ : l → l → ℝ} {S : Matrix l l ℝ} {θ₀ : k → ℝ}
    {A1 : l → l → k → ℝ} {A2 : l → l → k → k → ℝ} {L : Ω' → l → ℝ}
    (hS : S.PosDef) (hG : Function.Injective (Matrix.of G *ᵥ ·))
    (hrank1 : IsUnit (gram (G, W₁)).det)
    (hGhat : TendstoInMeasure P (fun n ω => sampleG (z n ω) (x n ω)) atTop (fun _ => G))
    (hW1 : TendstoInMeasure P W1 atTop (fun _ => W₁))
    (hg : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (x n ω) (y n ω) θ₀) atTop L
      (fun _ => P) P')
    (h0 : TendstoInMeasure P (fun n ω => sHat (z n ω) (x n ω) (y n ω) θ₀) atTop
      (fun _ => Matrix.of.symm S))
    (h1 : TendstoInMeasure P (fun n ω => sCross (z n ω) (x n ω) (y n ω) θ₀) atTop (fun _ => A1))
    (h2 : TendstoInMeasure P (fun n ω => sQuad (z n ω) (x n ω)) atTop (fun _ => A2))
    (hz : ∀ n, AEMeasurable (z n) P) (hx : ∀ n, AEMeasurable (x n) P)
    (hy : ∀ n, AEMeasurable (y n) P) (hW1m : ∀ n, AEMeasurable (W1 n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 S).map ofLp)
    (hkl : Fintype.card k < Fintype.card l) (c : ℝ) :
    Tendsto (fun n => P {ω | c < jStat n (sampleG (z n ω) (x n ω))
        (secondWeight (W1 n ω) (z n ω) (x n ω) (y n ω)) (sampleZY (z n ω) (y n ω))})
      atTop (𝓝 (chiSq (Fintype.card l - Fintype.card k) (Set.Ioi c))) := by
  have hJ := (two_step_feasible (θ₀ := θ₀) hS hG hrank1 hGhat hW1 hg h0 h1 h2 hz hx hy hW1m).2.2.1
  exact tendsto_prob_gt_of_chiSq (by omega) hJ (map_jLimit_chiSq hS hG hL hlaw) c

/-- In the overidentified two-step example of `two_step_witness` (`l = 2`, `k = 1`,
`S = diag(1, 2)`), the J test has asymptotic rejection probability `P(χ²(1) > c)`. -/
theorem two_step_jtest_chiSq_witness (c : ℝ) :
    let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]
    let G : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 S).map ofLp
    ∃ _ : IsProbabilityMeasure P,
      Tendsto (fun n => P {ω | c < jStat n G (invFn (Matrix.of.symm S))
          (Matrix.of G *ᵥ 0 + (Real.sqrt n)⁻¹ • ω)})
        atTop (𝓝 (chiSq 1 (Set.Ioi c))) := by
  intro S G P
  obtain ⟨hP, hS, hG, hGc, hSc, ⟨_, hg⟩, hL, hlaw⟩ := two_step_witness
  refine ⟨hP, ?_⟩
  have := (two_step_jtest_chiSq (θ₀ := (0 : Fin 1 → ℝ)) hS hG hGc hSc hg
    (fun _ => aemeasurable_const) (fun _ => aemeasurable_const) (fun n => by fun_prop) hL hlaw).2.2
    (by simp) c
  simpa using this

section Wald

variable {q : Type*} [Fintype q] [DecidableEq q]

/-- The Wald statistic for `H₀ : Rθ = c`: `n (Rθ̂ − c)ᵀ (R V̂ Rᵀ)⁻¹ (Rθ̂ − c)`, where `V̂`
estimates the asymptotic variance of `√n θ̂`. -/
noncomputable def waldStat (n : ℕ) (R : Matrix q k ℝ) (c : q → ℝ) (θ : k → ℝ) (V : k → k → ℝ) :
    ℝ :=
  n * ((R *ᵥ θ - c) ⬝ᵥ ((R * Matrix.of V * Rᵀ)⁻¹ *ᵥ (R *ᵥ θ - c)))

/-- The Wald weight `(R V Rᵀ)⁻¹` in function form. -/
noncomputable def waldWeight (R : Matrix q k ℝ) (V : k → k → ℝ) : q → q → ℝ :=
  invFn (Matrix.of.symm (R * Matrix.of V * Rᵀ))

omit [DecidableEq k] in
lemma of_waldWeight (R : Matrix q k ℝ) (V : k → k → ℝ) :
    Matrix.of (waldWeight R V) = (R * Matrix.of V * Rᵀ)⁻¹ := by
  rw [waldWeight, of_invFn]; rfl

omit [Fintype q] [DecidableEq q] [DecidableEq k] in
lemma continuous_waldArg (R : Matrix q k ℝ) :
    Continuous (fun V : k → k → ℝ => Matrix.of.symm (R * Matrix.of V * Rᵀ)) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

omit [DecidableEq k] in
lemma continuousAt_waldWeight (R : Matrix q k ℝ) {V : k → k → ℝ}
    (h : IsUnit (R * Matrix.of V * Rᵀ).det) : ContinuousAt (waldWeight R) V :=
  (continuousAt_invFn (by rw [Equiv.apply_symm_apply]; exact h)).comp (continuous_waldArg R).continuousAt

omit [DecidableEq k] in
lemma measurable_waldWeight (R : Matrix q k ℝ) : Measurable (waldWeight R) :=
  measurable_invFn.comp (continuous_waldArg R).measurable

omit [DecidableEq k] in
/-- **The Wald statistic converges in distribution** (Wald 1943; Newey and McFadden 1994
§9.1; Hayashi Prop. 2.3): if `H₀ : Rθ₀ = c` holds, `√n (θ̂ₙ − θ₀) →d L`, `V̂ₙ →p V` and
`R V Rᵀ` is invertible, then `Wₙ →d (RL)ᵀ (R V Rᵀ)⁻¹ (RL)`. -/
theorem wald_tendsto [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (R : Matrix q k ℝ) (c : q → ℝ) (hnull : R *ᵥ θ₀ = c)
    (hR : IsUnit (R * V * Rᵀ).det)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ₀)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P) :
    TendstoInDistribution (fun n ω => waldStat n R c (T n ω) (Vhat n ω)) atTop
      (fun ω => (R *ᵥ L ω) ⬝ᵥ ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ L ω))) (fun _ => P) P' := by
  have hB : TendstoInMeasure P (fun n ω => waldWeight R (Vhat n ω)) atTop
      (fun _ => waldWeight R (Matrix.of.symm V)) :=
    tendstoInMeasure_comp_continuousAt hV (continuousAt_waldWeight R (by rw [Equiv.apply_symm_apply]; exact hR))
  have hBm : ∀ n, AEMeasurable (fun ω => waldWeight R (Vhat n ω)) P := fun n =>
    (measurable_waldWeight R).comp_aemeasurable (hVm n)
  have hRT := hT.continuous_comp (g := fun x => R *ᵥ x) (by fun_prop)
  have hS := hRT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × (q → q → ℝ) => p.1 ⬝ᵥ (Matrix.of p.2 *ᵥ p.1)) (by fun_prop) hB hBm
  have heq : (fun (n : ℕ) ω => waldStat n R c (T n ω) (Vhat n ω))
      = fun (n : ℕ) ω => (fun p : (q → ℝ) × (q → q → ℝ) => p.1 ⬝ᵥ (Matrix.of p.2 *ᵥ p.1))
        (((fun x => R *ᵥ x) ∘ fun ω => Real.sqrt n • (T n ω - θ₀)) ω, waldWeight R (Vhat n ω)) := by
    funext n ω
    have hx : R *ᵥ (Real.sqrt n • (T n ω - θ₀)) = Real.sqrt n • (R *ᵥ T n ω - c) := by
      rw [mulVec_smul, mulVec_sub, hnull]
    simp only [Function.comp_apply, waldStat, of_waldWeight]
    rw [hx, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hlim : (fun ω => (R *ᵥ L ω) ⬝ᵥ ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ L ω)))
      = fun ω => (fun p : (q → ℝ) × (q → q → ℝ) => p.1 ⬝ᵥ (Matrix.of p.2 *ᵥ p.1))
        (((fun x => R *ᵥ x) ∘ L) ω, waldWeight R (Matrix.of.symm V)) := by
    funext ω
    simp only [Function.comp_apply, of_waldWeight]
    rfl
  rw [heq, hlim]
  exact hS

/-- **The Wald limit is χ²(q)**: if moreover `L ∼ N(0, V)`, the limit
`(RL)ᵀ (R V Rᵀ)⁻¹ (RL)` is `χ²(q)`, `q` the number of restrictions, and the Wald test
rejecting when `Wₙ > c` has asymptotic size `P(χ²(q) > c)`. -/
theorem wald_chiSq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {T : ℕ → Ω → k → ℝ} {Vhat : ℕ → Ω → k → k → ℝ} {θ₀ : k → ℝ} {V : Matrix k k ℝ}
    {L : Ω' → k → ℝ} (R : Matrix q k ℝ) (c : q → ℝ) (hnull : R *ᵥ θ₀ = c)
    (hR : IsUnit (R * V * Rᵀ).det) (hVpsd : V.PosSemidef)
    (hT : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - θ₀)) atTop L
      (fun _ => P) P')
    (hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V))
    (hVm : ∀ n, AEMeasurable (Vhat n) P)
    (hL : Measurable L) (hlaw : P'.map L = (multivariateGaussian 0 V).map ofLp) :
    P'.map (fun ω => (R *ᵥ L ω) ⬝ᵥ ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ L ω))) = chiSq (Fintype.card q) ∧
    (0 < Fintype.card q → ∀ a : ℝ,
      Tendsto (fun n => P {ω | a < waldStat n R c (T n ω) (Vhat n ω)}) atTop
        (𝓝 (chiSq (Fintype.card q) (Set.Ioi a)))) := by
  set M := R * V * Rᵀ with hM
  have hRL := map_mulVec_of_gaussian hL hVpsd hlaw R
  have hMpsd : M.PosSemidef := by
    have := hVpsd.mul_mul_conjTranspose_same R
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hMt : Mᵀ = M := by
    have := hMpsd.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hc : Measurable (fun y : q → ℝ => y ⬝ᵥ (M⁻¹ *ᵥ y)) :=
    (by fun_prop : Continuous (fun y : q → ℝ => y ⬝ᵥ (M⁻¹ *ᵥ y))).measurable
  have hmv : Measurable (fun x : k → ℝ => R *ᵥ x) :=
    (by fun_prop : Continuous (fun x : k → ℝ => R *ᵥ x)).measurable
  have hRLm : Measurable (fun ω => R *ᵥ L ω) := hmv.comp hL
  have hmap : P'.map (fun ω => (R *ᵥ L ω) ⬝ᵥ (M⁻¹ *ᵥ (R *ᵥ L ω))) = chiSq (Fintype.card q) := by
    rw [show (fun ω => (R *ᵥ L ω) ⬝ᵥ (M⁻¹ *ᵥ (R *ᵥ L ω)))
        = (fun y => y ⬝ᵥ (M⁻¹ *ᵥ y)) ∘ (fun ω => R *ᵥ L ω) from rfl,
      ← Measure.map_map hc hRLm, hRL]
    refine map_quadForm_gaussian hMpsd ?_ ?_ ?_
    · rw [transpose_nonsing_inv, hMt]
    · rw [nonsing_inv_mul _ hR, Matrix.one_mul]
    · rw [nonsing_inv_mul _ hR, trace_one]
  exact ⟨hmap, fun hq a => tendsto_prob_gt_of_chiSq hq
    (wald_tendsto R c hnull hR hT hV hVm) hmap a⟩

/-- **Non-vacuity of the Wald theorem.** Testing `H₀ : θ₁ = θ₂` (`R = (1, −1)`, `c = 0`) with
`√n θ̂ₙ ∼ N(0, I₂)` and the non-constant consistent variance estimate
`V̂ₙ = (1 + 1/(n+1)) I₂`: every hypothesis of `wald_chiSq` holds, and the Wald test rejecting
when `Wₙ > a` has asymptotic rejection probability `P(χ²(1) > a)`. -/
theorem wald_witness (a : ℝ) :
    let R : Matrix (Fin 1) (Fin 2) ℝ := !![1, -1]
    let V : Matrix (Fin 2) (Fin 2) ℝ := 1
    let P : Measure (Fin 2 → ℝ) := (multivariateGaussian 0 V).map ofLp
    let T : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ := fun n ω => (Real.sqrt n)⁻¹ • ω
    let Vhat : ℕ → (Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
      fun n _ => Matrix.of.symm ((1 + 1 / ((n : ℝ) + 1)) • V)
    ∃ _ : IsProbabilityMeasure P,
      R *ᵥ 0 = 0 ∧ IsUnit (R * V * Rᵀ).det ∧ V.PosSemidef ∧
      TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt n • (T n ω - 0)) atTop id
        (fun _ => P) P ∧
      TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V) ∧
      (∀ n, AEMeasurable (Vhat n) P) ∧ Measurable (id : (Fin 2 → ℝ) → Fin 2 → ℝ) ∧
      P.map id = (multivariateGaussian 0 V).map ofLp ∧
      Tendsto (fun n => P {ω | a < waldStat n R 0 (T n ω) (Vhat n ω)})
        atTop (𝓝 (chiSq 1 (Set.Ioi a))) := by
  intro R V P T Vhat
  have hofLp : Measurable (ofLp : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff hofLp.aemeasurable).mpr inferInstance
  have hR : IsUnit (R * V * Rᵀ).det := by
    have h2 : R * V * Rᵀ = !![2] := by
      ext i j
      fin_cases i; fin_cases j
      simp [R, V, Matrix.mul_apply, Fin.sum_univ_two]
      norm_num
    rw [h2, det_fin_one_of]
    norm_num
  have hT : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • (T n ω - 0)) atTop id (fun _ => P) P := by
    refine ⟨fun n => by fun_prop, by fun_prop, ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt n ≠ 0 := by
      rw [Real.sqrt_ne_zero']; exact_mod_cast hn
    apply Subtype.ext
    simp only [T, sub_zero, smul_smul, mul_inv_cancel₀ hs, one_smul]
    rfl
  have hV : TendstoInMeasure P Vhat atTop (fun _ => Matrix.of.symm V) := by
    refine tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => ?_)
    have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1)) • Matrix.of.symm V) atTop
        (𝓝 (Matrix.of.symm V)) := by
      simpa only [one_smul] using h1.smul_const (Matrix.of.symm V)
    exact h2
  have hVm : ∀ n, AEMeasurable (Vhat n) P := fun _ => aemeasurable_const
  have hlaw : P.map id = (multivariateGaussian 0 V).map ofLp := Measure.map_id
  refine ⟨hP, mulVec_zero R, hR, PosSemidef.one, hT, hV, hVm, measurable_id, hlaw, ?_⟩
  exact (wald_chiSq R 0 (mulVec_zero R) hR PosSemidef.one hT hV hVm measurable_id hlaw).2
    (by simp) a

end Wald

end Econ.Asymptotics
