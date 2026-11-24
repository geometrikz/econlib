/-
# The Kalman filter recursion and the Riccati equation

Kalman (1960); Hamilton, *Time Series Analysis* (1994), §13.2 and §13.5;
Anderson and Moore, *Optimal Filtering* (1979), §3.1 and §4.4; Durbin and Koopman
(2012), §4.3.

**The model.** State `x_{t+1} = Fx_t + w_t`, observation `y_t = Hx_t + v_t`, and
the filter `x̂_{t+1} = F(x̂_t + K_t(y_t − Hx̂_t))` with gains `K_t = P_tHᵀS_t⁻¹`,
`S_t = HP_tHᵀ + R`, from the covariance recursion `P_{t+1} = riccati P_t`, where
`riccati P = F J_P(K*_P) Fᵀ + Q` is the Joseph-form Riccati map.

**The results.**

* `riccati_eq`: the textbook Riccati difference equation
  `P⁺ = F(P − PHᵀS⁻¹HP)Fᵀ + Q`.
* **Mean squared errors** (`filter_mse`, `kalman_filter_mse`): with
  square-integrable white noises uncorrelated with each other and with the initial
  error, a filter with any gains `K_t` has `E[(x_t − x̂_t)(x_t − x̂_t)ᵀ] = gainCov K t`,
  and for the Kalman gains this is the Riccati iterate `P_t`. Orthogonality of the
  error to current and future noise is derived, not assumed.
* **Optimality** (`kalman_optimal_gains`): every gain sequence has error
  covariance at least `P_t` in the Loewner order at every date.
* `riccati_posSemidef`, `covSeq_posSemidef`: the recursion stays positive
  semidefinite. `riccati_mono`: the Riccati map is monotone in the Loewner order;
  `covSeq_mono_zero`: from `P₀ = 0` the recursion is nondecreasing.
* **Steady state** (`riccati_steady_state`): from `P₀ = 0`, if the recursion is
  bounded above it converges to a positive semidefinite solution of the algebraic
  Riccati equation `P = riccati P`.
* Witnesses: the scalar model `F = H = Q = R = 1` has steady state the golden
  ratio (`riccati_scalar_witness`); a random walk with Rademacher noises satisfies
  every hypothesis of the MSE theorem (`kalman_mse_witness`).

**Scope.** Boundedness of the recursion, which follows from detectability /
observability, is a hypothesis of the steady-state theorem; uniqueness and
stability of the stabilising solution are not formalised. "Covariance" means
second moments of errors (MSE matrices); no Gaussianity is assumed.
-/
module

public import EconLean.Econometrics.TimeSeries.Kalman
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.MonotoneConvergence
public import EconLean.Econometrics.TimeSeries.WhiteNoise

@[expose] public section

namespace Econ.TimeSeries.Kalman

open Matrix MeasureTheory Filter Topology Econ.OLS

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  {F : Matrix n n ℝ} {H : Matrix m n ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma posSemidef_congr {X : Matrix n n ℝ} (hX : X.PosSemidef) (A : Matrix m n ℝ) :
    (A * X * Aᵀ).PosSemidef := by
  have := hX.mul_mul_conjTranspose_same A
  rwa [conjTranspose_eq_transpose_of_trivial] at this

omit [DecidableEq m] in
/-- The Joseph form of any gain is positive semidefinite. -/
lemma joseph_posSemidef {P : Matrix n n ℝ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    (K : Matrix n m ℝ) : (joseph P H R K).PosSemidef :=
  (posSemidef_congr hP _).add (posSemidef_congr hR K)

/-- The **Riccati map** `P ↦ F J_P(K*_P) Fᵀ + Q`: posterior covariance of the
optimal update, propagated through the transition. -/
noncomputable def riccati (F : Matrix n n ℝ) (H : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P : Matrix n n ℝ) : Matrix n n ℝ :=
  F * joseph P H R (gain P H R) * Fᵀ + Q

/-- The **Riccati difference equation** in its textbook form (Hamilton eq. 13.2.22):
`P⁺ = F (P − PHᵀ(HPHᵀ + R)⁻¹HP) Fᵀ + Q`. -/
theorem riccati_eq {P : Matrix n n ℝ} (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hS : IsUnit (innovCov P H R).det) :
    riccati F H Q R P = F * (P - P * Hᵀ * (innovCov P H R)⁻¹ * (H * P)) * Fᵀ + Q := by
  rw [riccati, joseph_gain hP hR hS]

/-- The Riccati map preserves positive semidefiniteness. -/
theorem riccati_posSemidef {P : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hR : R.PosSemidef) : (riccati F H Q R P).PosSemidef :=
  (posSemidef_congr (joseph_posSemidef hP hR _) F).add hQ

omit [DecidableEq m] in
/-- For a fixed gain, the Joseph form is monotone in the prior covariance:
`J_{P'}(K) − J_P(K) = (I − KH)(P' − P)(I − KH)ᵀ`. -/
lemma joseph_sub_joseph (P P' : Matrix n n ℝ) (K : Matrix n m ℝ) :
    joseph P' H R K - joseph P H R K = (1 - K * H) * (P' - P) * (1 - K * H)ᵀ := by
  simp only [joseph, Matrix.mul_sub, Matrix.sub_mul]; abel

/-- **Monotonicity of the Riccati map** (Anderson–Moore §4.4): if `P ≤ P'` in
the Loewner order (both positive semidefinite) and `R` is positive definite,
then `riccati P ≤ riccati P'`. -/
theorem riccati_mono {P P' : Matrix n n ℝ} (hP : P.PosSemidef) (hR : R.PosDef) (hle : (P' - P).PosSemidef) :
    (riccati F H Q R P' - riccati F H Q R P).PosSemidef := by
  set K' := gain P' H R
  have h1 := joseph_sub_joseph (H := H) (R := R) P P' K'
  have h2 := kalman_gain_optimal (H := H) hP hR.posSemidef (isUnit_innovCov hP hR) K'
  have hsum : joseph P' H R K' - joseph P H R (gain P H R)
      = (1 - K' * H) * (P' - P) * (1 - K' * H)ᵀ
        + (joseph P H R K' - joseph P H R (gain P H R)) := by
    rw [← h1]; abel
  have hd : riccati F H Q R P' - riccati F H Q R P
      = F * (joseph P' H R K' - joseph P H R (gain P H R)) * Fᵀ := by
    simp only [riccati, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [hd, hsum]
  exact posSemidef_congr ((posSemidef_congr hle _).add h2) F

/-- The **covariance recursion** `P₀, P₁ = riccati P₀, …` of the Kalman filter. -/
noncomputable def covSeq (F : Matrix n n ℝ) (H : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (P₀ : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => P₀
  | t + 1 => riccati F H Q R (covSeq F H Q R P₀ t)

theorem covSeq_posSemidef {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosSemidef) (hQ : Q.PosSemidef)
    (hR : R.PosSemidef) (t : ℕ) : (covSeq F H Q R P₀ t).PosSemidef := by
  induction t with
  | zero => exact hP₀
  | succ t ih => exact riccati_posSemidef ih hQ hR

/-- **Monotone convergence from a zero prior** (Anderson–Moore §4.4): started at
`P₀ = 0`, the covariance recursion is nondecreasing in the Loewner order. -/
theorem covSeq_mono_zero (hQ : Q.PosSemidef) (hR : R.PosDef) (t : ℕ) :
    (covSeq F H Q R 0 (t + 1) - covSeq F H Q R 0 t).PosSemidef := by
  induction t with
  | zero =>
    simp only [covSeq, sub_zero]
    exact riccati_posSemidef PosSemidef.zero hQ hR.posSemidef
  | succ t ih =>
    exact riccati_mono (covSeq_posSemidef PosSemidef.zero hQ hR.posSemidef t) hR ih

/-- The Riccati map is continuous wherever the innovation covariance is invertible. -/
lemma continuousAt_riccati {P : Matrix n n ℝ} (hS : IsUnit (innovCov P H R).det) :
    ContinuousAt (riccati F H Q R) P := by
  have hinv : ContinuousAt (fun P : Matrix n n ℝ => (innovCov P H R)⁻¹) P := by
    have hc : Continuous (fun P : Matrix n n ℝ => innovCov P H R) := by
      unfold innovCov; fun_prop
    exact (continuousAt_matrix_inv (innovCov P H R) (by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hS.ne_zero)).comp
        (f := fun P : Matrix n n ℝ => innovCov P H R) hc.continuousAt
  have hΦ : Continuous (fun p : Matrix n n ℝ × Matrix m m ℝ =>
      F * joseph p.1 H R (p.1 * Hᵀ * p.2) * Fᵀ + Q) := by
    unfold joseph; fun_prop
  exact hΦ.continuousAt.comp (f := fun P => (P, (innovCov P H R)⁻¹))
    (continuousAt_id.prodMk hinv)

omit [Fintype m] [DecidableEq m] in
lemma single_dotProduct_mulVec_single (P : Matrix n n ℝ) (i j : n) :
    Pi.single i 1 ⬝ᵥ (P *ᵥ Pi.single j 1) = P i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

/-- **Steady state of the Riccati recursion** (Anderson–Moore §4.4; Hamilton
§13.5): started at `P₀ = 0`, if the covariance recursion is bounded above (as it
is under detectability), it converges to a positive semidefinite solution `P∞` of
the **algebraic Riccati equation** `P∞ = riccati P∞`. -/
theorem riccati_steady_state (hQ : Q.PosSemidef) (hR : R.PosDef) {M : Matrix n n ℝ}
    (hM : ∀ t, (M - covSeq F H Q R 0 t).PosSemidef) :
    ∃ Pinf : Matrix n n ℝ, Pinf.PosSemidef ∧
      Tendsto (covSeq F H Q R 0) atTop (𝓝 Pinf) ∧ riccati F H Q R Pinf = Pinf := by
  set Pt := covSeq F H Q R 0
  have hpsd : ∀ t, (Pt t).PosSemidef := covSeq_posSemidef PosSemidef.zero hQ hR.posSemidef
  have hsymm : ∀ t, (Pt t)ᵀ = Pt t := fun t => by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact (hpsd t).1
  -- quadratic forms are monotone and bounded
  let f : (n → ℝ) → ℕ → ℝ := fun v t => v ⬝ᵥ (Pt t *ᵥ v)
  have hmono : ∀ v, Monotone (f v) := fun v => monotone_nat_of_le_succ fun t => by
    have := (covSeq_mono_zero (F := F) (H := H) hQ hR t).dotProduct_mulVec_nonneg v
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at this
    exact this
  have hbdd : ∀ v, BddAbove (Set.range (f v)) := fun v => ⟨v ⬝ᵥ (M *ᵥ v), by
    rintro _ ⟨t, rfl⟩
    have := (hM t).dotProduct_mulVec_nonneg v
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at this
    exact this⟩
  have hlim : ∀ v, Tendsto (f v) atTop (𝓝 (⨆ t, f v t)) := fun v =>
    tendsto_atTop_ciSup (hmono v) (hbdd v)
  -- entries by polarisation
  let e : n → n → ℝ := fun i => Pi.single i 1
  have hpol : ∀ t i j, Pt t i j = (f (e i + e j) t - f (e i) t - f (e j) t) / 2 := by
    intro t i j
    have hji : Pt t j i = Pt t i j := by
      rw [← transpose_apply (Pt t) i j, hsymm]
    simp only [f, e, mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct_mulVec_single,
      hji]
    ring
  set Pinf : Matrix n n ℝ := Matrix.of fun i j =>
    ((⨆ t, f (e i + e j) t) - (⨆ t, f (e i) t) - (⨆ t, f (e j) t)) / 2
  have hconv : Tendsto Pt atTop (𝓝 Pinf) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [hpol]
    exact (((hlim _).sub (hlim _)).sub (hlim _)).div_const 2
  -- the limit is positive semidefinite
  have hPinf : Pinf.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
      have h1 : Tendsto (fun t => (Pt t)ᵀ) atTop (𝓝 Pinfᵀ) :=
        (continuous_id.matrix_transpose.tendsto _).comp hconv
      simp only [hsymm] at h1
      exact tendsto_nhds_unique h1 hconv
    · have hq : Tendsto (fun t => star v ⬝ᵥ (Pt t *ᵥ v)) atTop (𝓝 (star v ⬝ᵥ (Pinf *ᵥ v))) :=
        ((by fun_prop : Continuous fun A : Matrix n n ℝ => star v ⬝ᵥ (A *ᵥ v)).tendsto _).comp hconv
      exact ge_of_tendsto' hq fun t => (hpsd t).dotProduct_mulVec_nonneg v
  refine ⟨Pinf, hPinf, hconv, ?_⟩
  have h1 : Tendsto (fun t => Pt (t + 1)) atTop (𝓝 Pinf) := (tendsto_add_atTop_iff_nat 1).2 hconv
  have h2 : Tendsto (fun t => Pt (t + 1)) atTop (𝓝 (riccati F H Q R Pinf)) :=
    (continuousAt_riccati (isUnit_innovCov hPinf hR)).tendsto.comp hconv
  exact tendsto_nhds_unique h2 h1

/-! ## The filter's mean squared errors follow the Riccati recursion -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq m] in
/-- **Error recursion of the filter**: with `x' = Fx + w`, `y = Hx + v` and the
filter `x̂' = F(x̂ + K(y − Hx̂))`, the new error is
`F(I − KH)(x − x̂) − FKv + w`. -/
lemma filter_error_succ (K : Matrix n m ℝ) {x x' xh w : n → ℝ} {v y : m → ℝ}
    (hx : x' = F *ᵥ x + w) (hy : y = H *ᵥ x + v) :
    x' - F *ᵥ (xh + K *ᵥ (y - H *ᵥ xh))
      = (F * (1 - K * H)) *ᵥ (x - xh) + (-(F * K)) *ᵥ v + w := by
  subst hx hy
  simp only [mulVec_add, mulVec_sub, Matrix.mul_sub, sub_mulVec, Matrix.mul_one, neg_mulVec,
    ← mulVec_mulVec]
  abel

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
lemma memLp_mulVec_apply {a : Ω → m → ℝ} (ha : ∀ k, MemLp (fun ω => a ω k) 2 μ)
    (A : Matrix n m ℝ) (i : n) : MemLp (fun ω => (A *ᵥ a ω) i) 2 μ := by
  simp only [mulVec, dotProduct]
  exact memLp_finsetSum _ fun k _ => (ha k).const_mul (A i k)

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
lemma integral_mulVec_apply_mul {a : Ω → m → ℝ} {g : Ω → ℝ}
    (hag : ∀ k, Integrable (fun ω => a ω k * g ω) μ) (A : Matrix n m ℝ) (i : n) :
    ∫ ω, (A *ᵥ a ω) i * g ω ∂μ = ∑ k, A i k * ∫ ω, a ω k * g ω ∂μ := by
  simp only [mulVec, dotProduct, Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => by simpa only [mul_assoc] using (hag k).const_mul (A i k)]
  exact Finset.sum_congr rfl fun k _ => by rw [← integral_const_mul]; simp only [mul_assoc]

/-- The **error-covariance recursion of an arbitrary gain sequence** `K_t`:
`P_{t+1} = F J_{P_t}(K_t) Fᵀ + Q`. -/
noncomputable def gainCov (F : Matrix n n ℝ) (H : Matrix m n ℝ) (Q : Matrix n n ℝ)
    (R : Matrix m m ℝ) (K : ℕ → Matrix n m ℝ) (P₀ : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => P₀
  | t + 1 => F * joseph (gainCov F H Q R K P₀ t) H R (K t) * Fᵀ + Q

omit [DecidableEq m] in
/-- **Mean squared errors of a linear filter with any gains** (Anderson–Moore §3.1):
state `x_{t+1} = Fx_t + w_t`, observation `y_t = Hx_t + v_t`, filter
`x̂_{t+1} = F(x̂_t + K_t(y_t − Hx̂_t))` for any deterministic gains `K_t`. If the
initial error and the noises are square integrable, the noises are white
(`E[v_s v_tᵀ] = R·[s = t]`, `E[w_s w_tᵀ] = Q·[s = t]`, `E[v_s w_tᵀ] = 0`) and
uncorrelated with the initial error, whose second moment is `P₀`, then
`E[(x_t − x̂_t)(x_t − x̂_t)ᵀ] = gainCov K P₀ t`. -/
theorem filter_mse (K : ℕ → Matrix n m ℝ) {x xh w : ℕ → Ω → n → ℝ} {y v : ℕ → Ω → m → ℝ}
    {P₀ : Matrix n n ℝ}
    (hx : ∀ t ω, x (t + 1) ω = F *ᵥ x t ω + w t ω)
    (hy : ∀ t ω, y t ω = H *ᵥ x t ω + v t ω)
    (hxh : ∀ t ω, xh (t + 1) ω = F *ᵥ (xh t ω + K t *ᵥ (y t ω - H *ᵥ xh t ω)))
    (he0 : ∀ i, MemLp (fun ω => x 0 ω i - xh 0 ω i) 2 μ)
    (hv : ∀ t i, MemLp (fun ω => v t ω i) 2 μ) (hw : ∀ t i, MemLp (fun ω => w t ω i) 2 μ)
    (hP₀ : secondMoments μ (fun ω => x 0 ω - xh 0 ω) = P₀)
    (hvv : ∀ s t i j, ∫ ω, v s ω i * v t ω j ∂μ = if s = t then R i j else 0)
    (hww : ∀ s t i j, ∫ ω, w s ω i * w t ω j ∂μ = if s = t then Q i j else 0)
    (hvw : ∀ s t i j, ∫ ω, v s ω i * w t ω j ∂μ = 0)
    (he0v : ∀ t i j, ∫ ω, (x 0 ω i - xh 0 ω i) * v t ω j ∂μ = 0)
    (he0w : ∀ t i j, ∫ ω, (x 0 ω i - xh 0 ω i) * w t ω j ∂μ = 0) (t : ℕ) :
    secondMoments μ (fun ω => x t ω - xh t ω) = gainCov F H Q R K P₀ t := by
  set e : ℕ → Ω → n → ℝ := fun t ω => x t ω - xh t ω with he_def
  have hrec : ∀ t ω, e (t + 1) ω
      = (F * (1 - K t * H)) *ᵥ e t ω + (-(F * K t)) *ᵥ v t ω + w t ω := fun t ω => by
    simp only [he_def]; rw [hxh t ω]; exact filter_error_succ (K t) (hx t ω) (hy t ω)
  have hrec_i : ∀ t ω i, e (t + 1) ω i
      = ((F * (1 - K t * H)) *ᵥ e t ω) i + ((-(F * K t)) *ᵥ v t ω) i + w t ω i := fun t ω i => by
    rw [hrec t ω]; rfl
  have hL2 : ∀ t i, MemLp (fun ω => e t ω i) 2 μ := by
    intro t
    induction t with
    | zero => exact he0
    | succ t ih =>
      intro i
      simp only [hrec_i]
      exact ((memLp_mulVec_apply ih _ i).add (memLp_mulVec_apply (hv t) _ i)).add (hw t i)
  have hint : ∀ {f g : Ω → ℝ}, MemLp f 2 μ → MemLp g 2 μ → Integrable (fun ω => f ω * g ω) μ :=
    fun hf hg => hf.integrable_mul hg
  -- expanding a covariance of the new error with a square-integrable `g`
  have hexp : ∀ t (g : Ω → ℝ), MemLp g 2 μ → ∀ i, ∫ ω, e (t + 1) ω i * g ω ∂μ
      = ∑ k, (F * (1 - K t * H) : Matrix n n ℝ) i k * ∫ ω, e t ω k * g ω ∂μ
        + ∑ k, (-(F * K t) : Matrix n m ℝ) i k * ∫ ω, v t ω k * g ω ∂μ + ∫ ω, w t ω i * g ω ∂μ := by
    intro t g hg i
    simp only [hrec_i, add_mul]
    have h1 : Integrable (fun ω => ((F * (1 - K t * H)) *ᵥ e t ω) i * g ω) μ :=
      hint (memLp_mulVec_apply (hL2 t) _ i) hg
    have h2 : Integrable (fun ω => ((-(F * K t)) *ᵥ v t ω) i * g ω) μ :=
      hint (memLp_mulVec_apply (hv t) _ i) hg
    have h3 : Integrable (fun ω => w t ω i * g ω) μ := hint (hw t i) hg
    have h12 : Integrable (fun ω => ((F * (1 - K t * H)) *ᵥ e t ω) i * g ω
        + ((-(F * K t)) *ᵥ v t ω) i * g ω) μ := h1.add h2
    rw [integral_add h12 h3, integral_add h1 h2,
      integral_mulVec_apply_mul (fun k => hint (hL2 t k) hg),
      integral_mulVec_apply_mul (fun k => hint (hv t k) hg)]
  -- the error is uncorrelated with current and future noise
  have horth : ∀ t s, t ≤ s → (∀ i j, ∫ ω, e t ω i * v s ω j ∂μ = 0) ∧
      ∀ i j, ∫ ω, e t ω i * w s ω j ∂μ = 0 := by
    intro t
    induction t with
    | zero => intro s _; exact ⟨he0v s, he0w s⟩
    | succ t ih =>
      intro s hs
      have hts : t ≠ s := by omega
      constructor
      · intro i j
        rw [hexp t _ (hv s j) i]
        simp only [(ih s (by omega)).1 _ j, hvv t s, hts, ↓reduceIte, mul_zero,
          Finset.sum_const_zero, zero_add]
        rw [← hvw s t j i]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      · intro i j
        rw [hexp t _ (hw s j) i]
        simp only [(ih s (by omega)).2 _ j, hvw t s, hww t s, hts, ↓reduceIte, mul_zero,
          Finset.sum_const_zero, zero_add]
  induction t with
  | zero => exact hP₀
  | succ t ih =>
    let z : Ω → (n ⊕ m) ⊕ n → ℝ := fun ω => Sum.elim (Sum.elim (e t ω) (v t ω)) (w t ω)
    let C : Matrix n ((n ⊕ m) ⊕ n) ℝ := fromCols (fromCols (F * (1 - K t * H)) (-(F * K t))) 1
    have hz_eq : (fun ω => e (t + 1) ω) = fun ω => C *ᵥ z ω := by
      funext ω
      rw [hrec t ω]
      simp only [C, z, fromCols_mulVec_sumElim, one_mulVec]
    have hzL2 : ∀ a, MemLp (fun ω => z ω a) 2 μ := by
      rintro ((a | a) | a)
      · exact hL2 t a
      · exact hv t a
      · exact hw t a
    have hzz : ∀ a b, Integrable (fun ω => z ω a * z ω b) μ := fun a b => hint (hzL2 a) (hzL2 b)
    have hcomm : ∀ (f g : Ω → ℝ), ∫ ω, f ω * g ω ∂μ = ∫ ω, g ω * f ω ∂μ := fun f g =>
      integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    have hSig : secondMoments μ z = fromBlocks (fromBlocks (gainCov F H Q R K P₀ t) 0 0 R) 0 0 Q := by
      ext a b
      have hent : ∀ i j, ∫ ω, e t ω i * e t ω j ∂μ = gainCov F H Q R K P₀ t i j := fun i j => by
        rw [← ih]; rfl
      rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
        simp only [secondMoments, of_apply, z, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁,
          fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]
      · exact hent a b
      · exact (horth t t le_rfl).1 a b
      · exact (horth t t le_rfl).2 a b
      · rw [hcomm]; exact (horth t t le_rfl).1 b a
      · rw [hvv t t a b]; simp
      · exact hvw t t a b
      · rw [hcomm]; exact (horth t t le_rfl).2 b a
      · rw [hcomm]; exact hvw t t b a
      · rw [hww t t a b]; simp
    have hsm : secondMoments μ (fun ω => e (t + 1) ω) = C * secondMoments μ z * Cᵀ := by
      rw [hz_eq]
      ext a b
      exact integral_mulVec_mul_mulVec hzz C C a b
    change secondMoments μ (fun ω => e (t + 1) ω)
      = F * joseph (gainCov F H Q R K P₀ t) H R (K t) * Fᵀ + Q
    rw [hsm, hSig]
    simp only [C, fromCols_mul_fromBlocks, transpose_fromCols, fromCols_mul_fromRows,
      Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one,
      transpose_one, joseph]
    simp only [transpose_mul, transpose_neg, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg]


/-- With the Kalman gains, the error-covariance recursion is the Riccati recursion. -/
lemma covSeq_eq_gainCov (P₀ : Matrix n n ℝ) (t : ℕ) :
    covSeq F H Q R P₀ t = gainCov F H Q R (fun t => gain (covSeq F H Q R P₀ t) H R) P₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change riccati F H Q R (covSeq F H Q R P₀ t) = F * joseph (gainCov F H Q R _ P₀ t) H R _ * Fᵀ + Q
    rw [riccati, ← ih]

/-- **The Kalman filter's mean squared errors follow the Riccati recursion**
(Kalman 1960; Hamilton §13.2; Anderson–Moore §3.1). State `x_{t+1} = Fx_t + w_t`,
observation `y_t = Hx_t + v_t`, filter `x̂_{t+1} = F(x̂_t + K_t(y_t − Hx̂_t))` with
the gains `K_t = P_tHᵀ(HP_tHᵀ + R)⁻¹` of the covariance recursion `P_t`. If the
initial error and the noises are square integrable, the noises are white
(`E[v_s v_tᵀ] = R·[s = t]`, `E[w_s w_tᵀ] = Q·[s = t]`, `E[v_s w_tᵀ] = 0`) and
uncorrelated with the initial error, whose second moment is `P₀`, then
`E[(x_t − x̂_t)(x_t − x̂_t)ᵀ] = P_t` for every `t`. -/
theorem kalman_filter_mse {x xh w : ℕ → Ω → n → ℝ} {y v : ℕ → Ω → m → ℝ} {P₀ : Matrix n n ℝ}
    (hx : ∀ t ω, x (t + 1) ω = F *ᵥ x t ω + w t ω)
    (hy : ∀ t ω, y t ω = H *ᵥ x t ω + v t ω)
    (hxh : ∀ t ω, xh (t + 1) ω
      = F *ᵥ (xh t ω + gain (covSeq F H Q R P₀ t) H R *ᵥ (y t ω - H *ᵥ xh t ω)))
    (he0 : ∀ i, MemLp (fun ω => x 0 ω i - xh 0 ω i) 2 μ)
    (hv : ∀ t i, MemLp (fun ω => v t ω i) 2 μ) (hw : ∀ t i, MemLp (fun ω => w t ω i) 2 μ)
    (hP₀ : secondMoments μ (fun ω => x 0 ω - xh 0 ω) = P₀)
    (hvv : ∀ s t i j, ∫ ω, v s ω i * v t ω j ∂μ = if s = t then R i j else 0)
    (hww : ∀ s t i j, ∫ ω, w s ω i * w t ω j ∂μ = if s = t then Q i j else 0)
    (hvw : ∀ s t i j, ∫ ω, v s ω i * w t ω j ∂μ = 0)
    (he0v : ∀ t i j, ∫ ω, (x 0 ω i - xh 0 ω i) * v t ω j ∂μ = 0)
    (he0w : ∀ t i j, ∫ ω, (x 0 ω i - xh 0 ω i) * w t ω j ∂μ = 0) (t : ℕ) :
    secondMoments μ (fun ω => x t ω - xh t ω) = covSeq F H Q R P₀ t := by
  rw [covSeq_eq_gainCov]
  exact filter_mse (fun t => gain (covSeq F H Q R P₀ t) H R) hx hy hxh he0 hv hw hP₀ hvv hww hvw
    he0v he0w t

/-- **Optimality of the Kalman filter among linear filters** (Kalman 1960;
Anderson–Moore §3.1): for every gain sequence `K_t`, the error covariance
`gainCov K P₀ t` exceeds the Kalman filter's `covSeq P₀ t` in the Loewner order.
Combined with `filter_mse`, no linear filter of this form has a smaller mean
squared error at any date. -/
theorem kalman_optimal_gains {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosSemidef) (hQ : Q.PosSemidef)
    (hR : R.PosDef) (K : ℕ → Matrix n m ℝ) (t : ℕ) :
    (gainCov F H Q R K P₀ t - covSeq F H Q R P₀ t).PosSemidef := by
  induction t with
  | zero => simpa [gainCov, covSeq] using PosSemidef.zero
  | succ t ih =>
    set P := covSeq F H Q R P₀ t
    set P' := gainCov F H Q R K P₀ t
    have hP : P.PosSemidef := covSeq_posSemidef hP₀ hQ hR.posSemidef t
    have h1 := joseph_sub_joseph (H := H) (R := R) P P' (K t)
    have h2 := kalman_gain_optimal (H := H) hP hR.posSemidef (isUnit_innovCov hP hR) (K t)
    have hd : gainCov F H Q R K P₀ (t + 1) - covSeq F H Q R P₀ (t + 1)
        = F * ((1 - K t * H) * (P' - P) * (1 - K t * H)ᵀ
          + (joseph P H R (K t) - joseph P H R (gain P H R))) * Fᵀ := by
      change F * joseph P' H R (K t) * Fᵀ + Q - riccati F H Q R P = _
      rw [← h1, riccati]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [hd]
    exact posSemidef_congr ((posSemidef_congr ih _).add h2) F

/-! ## Non-vacuity: the scalar steady state is the golden ratio -/

lemma riccati_scalar {c : ℝ} (hc : 0 ≤ c) :
    riccati (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 (c • 1) = (c / (c + 1) + 1) • 1 := by
  have hc1 : c + 1 ≠ 0 := by positivity
  have hS : innovCov (c • (1 : Matrix Unit Unit ℝ)) (1 : Matrix Unit Unit ℝ) 1 = (c + 1) • 1 := by
    rw [innovCov, add_smul, one_smul]; simp
  have hSi : (innovCov (c • (1 : Matrix Unit Unit ℝ)) (1 : Matrix Unit Unit ℝ) 1)⁻¹ = (c + 1)⁻¹ • 1 := by
    rw [hS, inv_eq_left_inv]
    rw [smul_mul_smul, Matrix.one_mul, inv_mul_cancel₀ hc1, one_smul]
  ext i j
  simp only [riccati, joseph, gain, hSi]
  simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  field_simp
  ring

/-- **Non-vacuity of the steady-state theorem**: for the scalar model
`F = H = Q = R = 1` started at `P₀ = 0`, the covariance recursion stays in `[0, 2]`,
and its limit is the golden ratio `(1 + √5)/2`, the positive root of the algebraic
Riccati equation `P = P/(P + 1) + 1`. -/
theorem riccati_scalar_witness :
    ∃ Pinf : Matrix Unit Unit ℝ,
      Tendsto (covSeq (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 0) atTop (𝓝 Pinf) ∧
      Pinf () () = (1 + Real.sqrt 5) / 2 := by
  have hseq : ∀ t, ∃ c : ℝ, 0 ≤ c ∧ c ≤ 2 ∧
      covSeq (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 0 t = c • 1 := by
    intro t
    induction t with
    | zero => exact ⟨0, le_rfl, by norm_num, by simp [covSeq]⟩
    | succ t ih =>
      obtain ⟨c, hc0, hc2, hc⟩ := ih
      refine ⟨c / (c + 1) + 1, by positivity, ?_, ?_⟩
      · have : c / (c + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
        linarith
      · change riccati 1 1 1 1 (covSeq (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 0 t) = _
        rw [hc, riccati_scalar hc0]
  have hM : ∀ t, ((2 : ℝ) • (1 : Matrix Unit Unit ℝ) - covSeq (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 0 t).PosSemidef := by
    intro t
    obtain ⟨c, _, hc2, hc⟩ := hseq t
    rw [hc, ← sub_smul]
    exact PosSemidef.one.smul (by linarith)
  obtain ⟨Pinf, hPsd, hlim, hfix⟩ := riccati_steady_state (F := (1 : Matrix Unit Unit ℝ))
    (H := (1 : Matrix Unit Unit ℝ)) PosSemidef.one PosDef.one hM
  refine ⟨Pinf, hlim, ?_⟩
  set c := Pinf () ()
  have hP : Pinf = c • 1 := by ext i j; simp [c]
  have hc0 : 0 ≤ c := hPsd.diag_nonneg
  rw [hP, riccati_scalar hc0] at hfix
  have hfix' : c / (c + 1) + 1 = c := by
    have := congrFun (congrFun hfix ()) ()
    simpa using this
  have hc1 : c + 1 ≠ 0 := by positivity
  have hq : c ^ 2 - c - 1 = 0 := by
    field_simp at hfix'; nlinarith [hfix']
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 1 < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hfac : (c - (1 + Real.sqrt 5) / 2) * (c - (1 - Real.sqrt 5) / 2) = 0 := by
    nlinarith [hq, h5]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · nlinarith

/-! ## Non-vacuity of the MSE recursion: a random walk observed with noise -/

section Witness

open Econ.TimeSeries.WhiteNoise

/-- Measurement noise `v_t = r_{2t}` (Rademacher). -/
def wnV (t : ℕ) (ω : ℕ → Bool) : Unit → ℝ := fun _ => rad (2 * t) ω

/-- State noise `w_t = r_{2t+1}` (Rademacher). -/
def wnW (t : ℕ) (ω : ℕ → Bool) : Unit → ℝ := fun _ => rad (2 * t + 1) ω

/-- The random-walk state `x_0 = 0`, `x_{t+1} = x_t + w_t`. -/
def wnX : ℕ → (ℕ → Bool) → Unit → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => (1 : Matrix Unit Unit ℝ) *ᵥ wnX t ω + wnW t ω

/-- Observations `y_t = x_t + v_t`. -/
def wnY (t : ℕ) (ω : ℕ → Bool) : Unit → ℝ := (1 : Matrix Unit Unit ℝ) *ᵥ wnX t ω + wnV t ω

/-- The Kalman filter started at `x̂_0 = 0`. -/
noncomputable def wnXh : ℕ → (ℕ → Bool) → Unit → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => (1 : Matrix Unit Unit ℝ) *ᵥ (wnXh t ω +
      gain (covSeq (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 0 t) 1 1 *ᵥ
        (wnY t ω - (1 : Matrix Unit Unit ℝ) *ᵥ wnXh t ω))

/-- **Non-vacuity of `kalman_filter_mse`**: a random walk with Rademacher
state noise (`Q = 1`), observed with independent Rademacher noise (`R = 1`), from a
known start (`P₀ = 0`). All hypotheses hold, so the filter's mean squared error at
every date is the Riccati iterate; at `t = 1` it equals `1`. -/
theorem kalman_mse_witness :
    (∀ t, secondMoments (coins ℕ) (fun ω => wnX t ω - wnXh t ω)
      = covSeq (1 : Matrix Unit Unit ℝ) (1 : Matrix Unit Unit ℝ) 1 1 0 t) ∧
    secondMoments (coins ℕ) (fun ω => wnX 1 ω - wnXh 1 ω) = 1 := by
  have hmse := fun t => kalman_filter_mse (μ := coins ℕ) (F := (1 : Matrix Unit Unit ℝ))
    (H := (1 : Matrix Unit Unit ℝ)) (Q := 1) (R := 1) (P₀ := 0)
    (x := wnX) (xh := wnXh) (y := wnY) (v := wnV) (w := wnW)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => by simp [wnX, wnXh])
    (fun t _ => memLp_rad _ 2) (fun t _ => memLp_rad _ 2)
    (by ext; simp [secondMoments, wnX, wnXh])
    (fun s t i j => by
      simp only [wnV]; rw [integral_rad_mul]
      by_cases h : s = t
      · subst h; simp
      · simp [h])
    (fun s t i j => by
      simp only [wnW]; rw [integral_rad_mul]
      by_cases h : s = t
      · subst h; simp
      · simp [h])
    (fun s t i j => by
      simp only [wnV, wnW]; rw [integral_rad_mul]; simp only [ite_eq_right_iff]; omega)
    (fun t i j => by simp [wnX, wnXh])
    (fun t i j => by simp [wnX, wnXh]) t
  refine ⟨hmse, ?_⟩
  rw [hmse 1]
  change riccati 1 1 1 1 (0 : Matrix Unit Unit ℝ) = 1
  have := riccati_scalar (c := 0) le_rfl
  simpa using this

end Witness

end Econ.TimeSeries.Kalman
