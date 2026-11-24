/-
# Positive definiteness of autocovariance matrices

Brockwell and Davis (1991), §5.1; Hamilton, *Time Series Analysis* (1994),
§3.4.

**The results.**

* `toeplitz_posDef`: if each `x_t` has an innovation `ε_t` orthogonal to the past
  with `E[ε_t x_t] = σ² > 0`, every Toeplitz autocovariance matrix
  `Γ = [γ(i − j)]` is positive definite. If `aᵀΓa = E[(Σ aᵢx_{−i})²] = 0` then
  `Σ aᵢx_{−i} = 0` a.s., and pairing with the innovation at the first nonzero
  coefficient gives `a_{i₀}σ² = 0`.
* `yule_walker_unique`: hence the Yule–Walker system identifies the AR
  coefficients with no rank hypothesis.
* `white_noise_witness`: Rademacher white noise (`σ² = 1`) satisfies every
  hypothesis; `ma1_witness`: so does an MA(1), whose Toeplitz matrices are
  tridiagonal rather than the identity.

As in `YuleWalker.lean`, moments are uncentred second moments and the AR model
with parameter `p` has `p + 1` lags.
-/
module

public import EconLean.Econometrics.TimeSeries.YuleWalker
public import EconLean.Econometrics.TimeSeries.WhiteNoise

@[expose] public section

namespace Econ.TimeSeries.YuleWalker

open MeasureTheory Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Toeplitz matrix of an even autocovariance is symmetric. -/
lemma toeplitz_transpose {x : ℤ → Ω → ℝ} {γ : ℤ → ℝ} (hγ : Autocov μ x γ) (q : ℕ) :
    (toeplitz (p := q) γ)ᵀ = toeplitz γ := by
  ext i j
  simp only [toeplitz, transpose_apply, of_apply]
  rw [← autocov_neg hγ, neg_sub]

/-- The quadratic form of the Toeplitz matrix is the second moment of a linear
combination of lags: `aᵀΓa = E[(Σᵢ aᵢ x_{−i})²]`. -/
lemma toeplitz_quadForm {x : ℤ → Ω → ℝ} {γ : ℤ → ℝ} (hγ : Autocov μ x γ)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ) {q : ℕ} (a : Fin (q + 1) → ℝ) :
    a ⬝ᵥ (toeplitz γ *ᵥ a) = ∫ ω, (∑ i, a i * x (-(i : ℤ)) ω) ^ 2 ∂μ := by
  have hsq : ∀ ω, (∑ i : Fin (q + 1), a i * x (-(i : ℤ)) ω) ^ 2
      = ∑ i, ∑ j, a i * a j * (x (-(i : ℤ)) ω * x (-(j : ℤ)) ω) := fun ω => by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hsq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hxx _ _).const_mul _]
  simp only [dotProduct, mulVec, toeplitz, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hxx _ _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hγ, show -(i : ℤ) - -(j : ℤ) = -((i : ℤ) - j) by ring, autocov_neg hγ]
  ring

/-- **The autocovariance matrix of a process with nondegenerate innovations is
positive definite** (cf. Brockwell–Davis §5.1, whose Prop. 5.1.1 uses `γ(0) > 0`
and `γ(h) → 0` instead; Hamilton §3.4): if each `x_t`
has an innovation `ε_t` orthogonal to the past with `E[ε_t x_t] = σ² > 0`, then the
Toeplitz matrix `Γ = [γ(i − j)]` of every order is positive definite. -/
theorem toeplitz_posDef {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) (hσ : 0 < σ2) (q : ℕ) :
    (toeplitz (p := q) γ).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, toeplitz_transpose hγ]
  simp only [star_trivial]
  rw [toeplitz_quadForm hγ hxx]
  set Y : Ω → ℝ := fun ω => ∑ i : Fin (q + 1), a i * x (-(i : ℤ)) ω
  have hYi : Integrable (fun ω => Y ω ^ 2) μ := by
    have : (fun ω => Y ω ^ 2) = fun ω => ∑ i : Fin (q + 1), ∑ j : Fin (q + 1),
        a i * a j * (x (-(i : ℤ)) ω * x (-(j : ℤ)) ω) := funext fun ω => by
      simp only [Y]; rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hxx _ _).const_mul _
  refine lt_of_le_of_ne (integral_nonneg fun ω => sq_nonneg _) fun h0 => ?_
  -- `Y = 0` almost everywhere
  have hY0 : (fun ω => Y ω ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hYi).mp h0.symm
  -- the first nonzero coefficient
  have hne : (Finset.univ.filter fun i : Fin (q + 1) => a i ≠ 0).Nonempty := by
    by_contra hemp
    apply ha
    funext i
    by_contra hi
    exact hemp ⟨i, by simpa using hi⟩
  set i0 := (Finset.univ.filter fun i : Fin (q + 1) => a i ≠ 0).min' hne
  have hi0 : a i0 ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hbelow : ∀ i : Fin (q + 1), i < i0 → a i = 0 := fun i hi => by
    by_contra h
    exact absurd (Finset.min'_le _ i (by simp [h])) (not_le.mpr hi)
  -- `E[ε_{−i0} Y] = a_{i0} σ²`
  have hεY : ∫ ω, ε (-(i0 : ℤ)) ω * Y ω ∂μ = a i0 * σ2 := by
    have hexp : (fun ω => ε (-(i0 : ℤ)) ω * Y ω)
        = fun ω => ∑ i : Fin (q + 1), a i * (ε (-(i0 : ℤ)) ω * x (-(i : ℤ)) ω) := funext fun ω => by
      simp only [Y, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp, integral_finsetSum _ fun i _ => (hεx _ _).const_mul _,
      Finset.sum_eq_single i0]
    · rw [integral_const_mul, hε.2]
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · simp [hbelow i hlt]
      · rw [integral_const_mul, hε.1 _ _ (by
          have : (i0 : ℕ) < i := hgt
          omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hY0' : (fun ω => ε (-(i0 : ℤ)) ω * Y ω) =ᵐ[μ] 0 := by
    filter_upwards [hY0] with ω hω
    simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hω ⊢
    rw [hω, mul_zero]
  rw [integral_congr_ae hY0', Pi.zero_def, integral_zero] at hεY
  exact hi0 (by
    rcases mul_eq_zero.mp hεY.symm with h | h
    · exact h
    · exact absurd h hσ.ne')

/-- **Yule–Walker identification without a rank hypothesis**: for an AR process
with nondegenerate innovations, `φ = Γ⁻¹ (γ(1), …, γ(p+1))`. -/
theorem yule_walker_unique {p : ℕ} {φ : Fin (p + 1) → ℝ} {x ε : ℤ → Ω → ℝ} {γ : ℤ → ℝ} {σ2 : ℝ}
    (hx : IsAR φ x ε) (hγ : Autocov μ x γ) (hε : Innovation μ x ε σ2)
    (hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) μ)
    (hεx : ∀ t s, Integrable (fun ω => ε t ω * x s ω) μ) (hσ : 0 < σ2) :
    φ = (toeplitz γ)⁻¹ *ᵥ fun i : Fin (p + 1) => γ ((i : ℤ) + 1) :=
  (yule_walker_identify hx hγ hε hxx hεx).2
    ((isUnit_iff_isUnit_det _).mp (toeplitz_posDef hγ hε hxx hεx hσ p).isUnit)

open Econ.TimeSeries.WhiteNoise in
/-- **Non-vacuity with nondegenerate innovations**: Rademacher white noise
`x_t = ε_t = ±1` (independent fair signs, `σ² = 1`) is an AR process with
`φ = 0`, stationary second moments `γ(h) = [h = 0]` and innovations, so every
Toeplitz matrix is positive definite and Yule–Walker recovers `φ = 0`. -/
theorem white_noise_witness (q : ℕ) :
    let γ : ℤ → ℝ := fun h => if h = 0 then 1 else 0
    IsAR (p := 0) (fun _ => 0) (rad : ℤ → (ℤ → Bool) → ℝ) rad ∧
      Autocov (coins ℤ) rad γ ∧ Innovation (coins ℤ) rad rad 1 ∧
      (∀ t s, Integrable (fun ω => rad t ω * rad s ω) (coins ℤ)) ∧
      (toeplitz (p := q) γ).PosDef ∧
      (fun _ : Fin 1 => (0 : ℝ)) = (toeplitz γ)⁻¹ *ᵥ fun i : Fin 1 => γ ((i : ℤ) + 1) := by
  intro γ
  have hAR : IsAR (p := 0) (fun _ => 0) (rad : ℤ → (ℤ → Bool) → ℝ) rad := fun t ω => by simp
  have hint : ∀ t s, Integrable (fun ω => rad t ω * rad s ω) (coins ℤ) := fun t s =>
    (memLp_rad t 2).integrable_mul (memLp_rad s 2)
  have hγ : Autocov (coins ℤ) rad γ := fun t s => by
    rw [integral_rad_mul]; simp only [γ, sub_eq_zero]
  have hε : Innovation (coins ℤ) rad rad 1 :=
    ⟨fun t s hst => by rw [integral_rad_mul]; simp [hst.ne'], fun t => by
      rw [integral_rad_mul]; simp⟩
  exact ⟨hAR, hγ, hε, hint, toeplitz_posDef hγ hε hint hint one_pos q,
    yule_walker_unique hAR hγ hε hint hint one_pos⟩

open Econ.TimeSeries.WhiteNoise in
/-- **Non-vacuity with a non-diagonal Toeplitz matrix**: the MA(1) process
`x_t = ε_t + ε_{t−1}/2` driven by Rademacher white noise has autocovariances
`γ(0) = 5/4`, `γ(±1) = 1/2`, `γ(h) = 0` otherwise, and innovations `ε_t` with
`σ² = 1`; so its tridiagonal Toeplitz matrices are positive definite. -/
theorem ma1_witness (q : ℕ) :
    let x : ℤ → (ℤ → Bool) → ℝ := fun t ω => rad t ω + 2⁻¹ * rad (t - 1) ω
    let γ : ℤ → ℝ := fun h => if h = 0 then 5 / 4 else if h = 1 ∨ h = -1 then 1 / 2 else 0
    Autocov (coins ℤ) x γ ∧ Innovation (coins ℤ) x rad 1 ∧
      (∀ t s, Integrable (fun ω => x t ω * x s ω) (coins ℤ)) ∧
      (∀ t s, Integrable (fun ω => rad t ω * x s ω) (coins ℤ)) ∧
      (toeplitz (p := q) γ).PosDef := by
  intro x γ
  have hL2 : ∀ t, MemLp (x t) 2 (coins ℤ) := fun t =>
    (memLp_rad t 2).add ((memLp_rad (t - 1) 2).const_mul 2⁻¹)
  have hxx : ∀ t s, Integrable (fun ω => x t ω * x s ω) (coins ℤ) := fun t s =>
    (hL2 t).integrable_mul (hL2 s)
  have hεx : ∀ t s, Integrable (fun ω => rad t ω * x s ω) (coins ℤ) := fun t s =>
    (memLp_rad t 2).integrable_mul (hL2 s)
  have hI : ∀ a b : ℤ, Integrable (fun ω => rad a ω * rad b ω) (coins ℤ) := fun a b =>
    (memLp_rad a 2).integrable_mul (memLp_rad b 2)
  -- `E[ε_a x_s] = [a = s] + [a = s − 1]/2`
  have hεxv : ∀ a s, ∫ ω, rad a ω * x s ω ∂(coins ℤ)
      = (if a = s then 1 else 0) + 2⁻¹ * (if a = s - 1 then 1 else 0) := fun a s => by
    have : (fun ω => rad a ω * x s ω)
        = fun ω => rad a ω * rad s ω + 2⁻¹ * (rad a ω * rad (s - 1) ω) := funext fun ω => by
      simp only [x]; ring
    rw [this, integral_add (hI a s) ((hI a (s - 1)).const_mul 2⁻¹), integral_const_mul,
      integral_rad_mul, integral_rad_mul]
  have hγ : Autocov (coins ℤ) x γ := fun t s => by
    have : (fun ω => x t ω * x s ω)
        = fun ω => rad t ω * x s ω + 2⁻¹ * (rad (t - 1) ω * x s ω) := funext fun ω => by
      simp only [x]; ring
    rw [this, integral_add (hεx t s) ((hεx (t - 1) s).const_mul 2⁻¹), integral_const_mul,
      hεxv, hεxv]
    rcases (by omega : t = s ∨ t = s + 1 ∨ t = s - 1 ∨ (t ≠ s ∧ t ≠ s + 1 ∧ t ≠ s - 1)) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h
      norm_num [γ, show t ≠ t - 1 by omega, show t - 1 ≠ t by omega]
    · subst h
      norm_num [γ, show s + 1 ≠ s by omega, show s + 1 ≠ s - 1 by omega, show s ≠ s - 1 by omega]
    · subst h
      norm_num [γ, show s - 1 ≠ s by omega, show s - 1 - 1 ≠ s by omega,
        show s - 1 - 1 ≠ s - 1 by omega]
    · norm_num [γ, h1, h3, show t - 1 ≠ s by omega, show t - 1 ≠ s - 1 by omega,
        show t - s ≠ 0 by omega, show t - s ≠ 1 by omega, show t - s ≠ -1 by omega]
  have hε : Innovation (coins ℤ) x rad 1 :=
    ⟨fun t s hst => by
      rw [hεxv]; norm_num [show t ≠ s by omega, show t ≠ s - 1 by omega],
     fun t => by rw [hεxv]; norm_num [show t ≠ t - 1 by omega]⟩
  exact ⟨hγ, hε, hxx, hεx, toeplitz_posDef hγ hε hxx hεx one_pos q⟩

end Econ.TimeSeries.YuleWalker
