/-
# An overidentified data-level example for the feasible J test

Two instruments, one regressor (`l = 2`, `k = 1`). The design is deterministic apart from a
two-dimensional standard normal `ω`:

* instruments `zᵢ = (1, (−1)ⁱ)`, regressor `xᵢ = 1`, true parameter `θ₀ = 0`;
* errors `uᵢ = eᵢ + wᵢ/√n` with `wᵢ = ω₀ + (−1)ⁱ ω₁` and a deterministic "spike" `eᵢ`,
  equal to `√n/2` for `i ∈ {0, 1}`, `−√n/2` for `i ∈ {2, 3}` and `0` otherwise.

The spike gives the residual variance its scale (`n⁻¹ Σ eᵢ² zᵢzᵢᵀ = I`) without contributing to
the moments (`Σ eᵢ zᵢ = 0`), while `w` produces `√n ĝₙ(θ₀) → (ω₀, ω₁) ∼ N(0, I)`. All sample
moments converge for every `ω`, so every hypothesis of `two_step_feasible_jtest_chiSq` holds
with `G = (1, 0)ᵀ`, `S = I`, and the feasible J test has asymptotic rejection probability
`P(χ²(1) > c)` (`feasible_jtest_witness`).

**Caveats.** This is a triangular-array example with a deterministic design, a non-vacuity
witness for the high-level hypotheses, not an i.i.d. sampling model. The spike makes individual
`E[zᵢuᵢ]` nonzero for `i < 4` (they cancel in the sum), and `Ŝₙ → I` matches the variance of the
moment limit because `Cov(ω) = I` was chosen to match. The witness statement lists the
hypotheses with content; the remaining ones (`S = I` positive definite, constant first-step
weight, measurability of the constant data, `Measurable id`, `k < l`) are discharged in the proof.
-/
module

public import EconLean.Econometrics.Asymptotics.ChiSquaredTests

@[expose] public section

namespace Econ.Asymptotics.FeasibleJ

open MeasureTheory ProbabilityTheory Filter Topology Matrix WithLp

/-- The deterministic error spike. -/
noncomputable def spike (n i : ℕ) : ℝ :=
  if i < 2 then Real.sqrt n / 2 else if i < 4 then -(Real.sqrt n / 2) else 0

/-- Instruments `zᵢ = (1, (−1)ⁱ)`. -/
noncomputable def zJ (i : ℕ) : Fin 2 → ℝ := ![1, (-1) ^ i]

/-- The stochastic error component `wᵢ = ω₀ + (−1)ⁱ ω₁`. -/
noncomputable def wJ (ω : Fin 2 → ℝ) (i : ℕ) : ℝ := ω 0 + (-1) ^ i * ω 1

/-- The errors `uᵢ = eᵢ + wᵢ/√n`. -/
noncomputable def uJ (n : ℕ) (ω : Fin 2 → ℝ) (i : ℕ) : ℝ := spike n i + (Real.sqrt n)⁻¹ * wJ ω i

lemma sum_spike_mul {n : ℕ} (hn : 4 ≤ n) (g : ℕ → ℝ) :
    ∑ i : Fin n, spike n i * g i = Real.sqrt n / 2 * (g 0 + g 1 - g 2 - g 3) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => spike n i * g i)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  rw [Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range m, spike (4 + m) (4 + x) * g (4 + x) = 0 :=
    Finset.sum_eq_zero fun x _ => by
      simp [spike, show ¬ 4 + x < 2 by omega, show ¬ 4 + x < 4 by omega]
  rw [h0, add_zero]
  simp [Finset.sum_range_succ, spike]
  ring

lemma sum_spike_sq_mul {n : ℕ} (hn : 4 ≤ n) (g : ℕ → ℝ) :
    ∑ i : Fin n, spike n i ^ 2 * g i = n / 4 * (g 0 + g 1 + g 2 + g 3) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => spike n i ^ 2 * g i)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  rw [Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range m, spike (4 + m) (4 + x) ^ 2 * g (4 + x) = 0 :=
    Finset.sum_eq_zero fun x _ => by
      simp [spike, show ¬ 4 + x < 2 by omega, show ¬ 4 + x < 4 by omega]
  rw [h0, add_zero]
  have hs : Real.sqrt (4 + (m : ℝ)) ^ 2 = 4 + (m : ℝ) := Real.sq_sqrt (by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, spike]
  norm_num
  rw [div_pow, hs]
  ring

lemma sum_range_neg_one_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with h | h
    · simp [h, h.neg_one_pow, Nat.even_add_one]
    · simp [h.neg_one_pow, Nat.even_add_one, Nat.not_even_iff_odd.mpr h]

lemma abs_sum_neg_one_pow (n : ℕ) : |∑ i : Fin n, (-1 : ℝ) ^ (i : ℕ)| ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℝ) ^ i), sum_range_neg_one_pow]
  split_ifs <;> norm_num

lemma tendsto_avg_neg_one_pow :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, (-1 : ℝ) ^ (i : ℕ)) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n => ?_) tendsto_inv_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
  exact mul_le_of_le_one_right (by positivity) (abs_sum_neg_one_pow n)

/-- A uniformly bounded average with an extra vanishing factor tends to zero. -/
lemma tendsto_scaled_sum {c : ℕ → ℝ} (hc : Tendsto (fun n : ℕ => c n * n) atTop (𝓝 0))
    {f : ℕ → ℕ → ℝ} {K : ℝ} (hf : ∀ n i, |f n i| ≤ K) :
    Tendsto (fun n : ℕ => c n * ∑ i : Fin n, f n i) atTop (𝓝 0) := by
  have hb : ∀ n : ℕ, ‖c n * ∑ i : Fin n, f n i‖ ≤ |c n * n| * K := fun n => by
    rw [Real.norm_eq_abs, abs_mul]
    have : |∑ i : Fin n, f n i| ≤ n * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun (i : Fin n) _ => hf n i).trans ?_
      simp
    calc |c n| * |∑ i : Fin n, f n i| ≤ |c n| * (n * K) := by gcongr
      _ = |c n * n| * K := by rw [abs_mul, Nat.abs_cast]; ring
  refine squeeze_zero_norm hb ?_
  simpa using (hc.abs.mul_const K)

lemma sum_spike_mul_eq_zero {n : ℕ} (hn : 4 ≤ n) (g : ℕ → ℝ) (h02 : g 0 = g 2) (h13 : g 1 = g 3) :
    ∑ i : Fin n, spike n i * g i = 0 := by
  rw [sum_spike_mul hn, h02, h13]; ring

lemma zJ_zero_two : zJ 0 = zJ 2 := by funext a; fin_cases a <;> simp [zJ]
lemma zJ_one_three : zJ 1 = zJ 3 := by funext a; fin_cases a <;> norm_num [zJ]
lemma wJ_zero_two (ω : Fin 2 → ℝ) : wJ ω 0 = wJ ω 2 := by simp [wJ]
lemma wJ_one_three (ω : Fin 2 → ℝ) : wJ ω 1 = wJ ω 3 := by simp [wJ]; ring

lemma abs_zJ_le (i : ℕ) (a : Fin 2) : |zJ i a| ≤ 1 := by
  fin_cases a <;> simp [zJ]

lemma abs_wJ_le (ω : Fin 2 → ℝ) (i : ℕ) : |wJ ω i| ≤ |ω 0| + |ω 1| := by
  unfold wJ
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

lemma sqrt_inv_sq (n : ℕ) : (Real.sqrt n)⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The residual-variance estimate is `I + n⁻² Σ wᵢ² zᵢzᵢᵀ`. -/
lemma sHat_eq {n : ℕ} (hn : 4 ≤ n) (ω : Fin 2 → ℝ) (a b : Fin 2) :
    sHat (fun i : Fin n => zJ i) (fun _ _ => (1 : ℝ)) (fun i : Fin n => uJ n ω i)
      (0 : Fin 1 → ℝ) a b
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) a b
        + ((n : ℝ) ^ 2)⁻¹ * ∑ i : Fin n, wJ ω i ^ 2 * (zJ i a * zJ i b) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hexp : ∀ i : Fin n, (uJ n ω i - (fun _ => (1 : ℝ)) ⬝ᵥ (0 : Fin 1 → ℝ)) ^ 2
      * (zJ i a * zJ i b) = spike n i ^ 2 * (zJ i a * zJ i b)
        + 2 * (Real.sqrt n)⁻¹ * (spike n i * (wJ ω i * (zJ i a * zJ i b)))
        + (n : ℝ)⁻¹ * (wJ ω i ^ 2 * (zJ i a * zJ i b)) := fun i => by
    rw [dotProduct_zero, sub_zero, uJ, ← sqrt_inv_sq n]; ring
  have h1 := sum_spike_sq_mul hn (fun j => zJ j a * zJ j b)
  have h2 := sum_spike_mul_eq_zero hn (fun j => wJ ω j * (zJ j a * zJ j b))
    (by simp only [wJ_zero_two, zJ_zero_two]) (by simp only [wJ_one_three, zJ_one_three])
  simp only [sHat]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
  have hI : (n : ℝ) / 4 * (zJ 0 a * zJ 0 b + zJ 1 a * zJ 1 b + zJ 2 a * zJ 2 b + zJ 3 a * zJ 3 b)
      = n * (1 : Matrix (Fin 2) (Fin 2) ℝ) a b := by
    fin_cases a <;> fin_cases b <;> norm_num [zJ]
  rw [hI]
  field_simp
  ring

/-- The cross moment is `(n√n)⁻¹ Σ wᵢ zᵢzᵢᵀ`. -/
lemma sCross_eq {n : ℕ} (hn : 4 ≤ n) (ω : Fin 2 → ℝ) (a b : Fin 2) (c : Fin 1) :
    sCross (fun i : Fin n => zJ i) (fun _ _ => (1 : ℝ)) (fun i : Fin n => uJ n ω i)
      (0 : Fin 1 → ℝ) a b c
      = ((n : ℝ) * Real.sqrt n)⁻¹ * ∑ i : Fin n, wJ ω i * (zJ i a * zJ i b) := by
  have hexp : ∀ i : Fin n, (uJ n ω i - (fun _ => (1 : ℝ)) ⬝ᵥ (0 : Fin 1 → ℝ)) * 1
      * (zJ i a * zJ i b) = spike n i * (zJ i a * zJ i b)
        + (Real.sqrt n)⁻¹ * (wJ ω i * (zJ i a * zJ i b)) := fun i => by
    rw [dotProduct_zero, sub_zero, uJ]; ring
  have h2 := sum_spike_mul_eq_zero hn (fun j => zJ j a * zJ j b)
    (by simp only [zJ_zero_two]) (by simp only [zJ_one_three])
  simp only [sCross]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, ← Finset.mul_sum, h2,
    zero_add, ← mul_assoc, mul_inv]

/-- `√n ĝₙ(θ₀) = n⁻¹ Σ wᵢ zᵢ`. -/
lemma sqrt_sampleMoment_eq {n : ℕ} (hn : 4 ≤ n) (ω : Fin 2 → ℝ) (a : Fin 2) :
    (Real.sqrt n • sampleMoment (fun i : Fin n => zJ i) (fun _ _ => (1 : ℝ))
      (fun i : Fin n => uJ n ω i) (0 : Fin 1 → ℝ)) a
      = (n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a * wJ ω i := by
  have hs : Real.sqrt n ≠ 0 := by
    rw [Real.sqrt_ne_zero']; exact_mod_cast (by omega : 0 < n)
  have hexp : ∀ i : Fin n, zJ i a * (uJ n ω i - (fun _ => (1 : ℝ)) ⬝ᵥ (0 : Fin 1 → ℝ))
      = spike n i * zJ i a + (Real.sqrt n)⁻¹ * (zJ i a * wJ ω i) := fun i => by
    rw [dotProduct_zero, sub_zero, uJ]; ring
  have h2 := sum_spike_mul_eq_zero hn (fun j => zJ j a)
    (by simp only [zJ_zero_two]) (by simp only [zJ_one_three])
  simp only [sampleMoment, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, ← Finset.mul_sum, h2,
    zero_add]
  field_simp

lemma sum_zJ_zero (n : ℕ) : ∑ i : Fin n, zJ i 0 = n := by simp [zJ]

lemma sum_zJ_one (n : ℕ) : ∑ i : Fin n, zJ i 1 = ∑ i : Fin n, (-1 : ℝ) ^ (i : ℕ) := by simp [zJ]

lemma zJ_one_sq (i : ℕ) : zJ i 1 * zJ i 1 = 1 := by
  simp [zJ, ← pow_add, ← two_mul, pow_mul]

lemma tendsto_avg_const : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * n) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [inv_mul_cancel₀ (by exact_mod_cast (by omega : n ≠ 0))])

lemma tendsto_avg_zJ (a : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a) atTop
      (𝓝 (if a = 0 then 1 else 0)) := by
  fin_cases a
  · simpa [sum_zJ_zero] using tendsto_avg_const
  · simpa [sum_zJ_one] using tendsto_avg_neg_one_pow

lemma tendsto_avg_zJ_mul (a b : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a * zJ i b) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℝ) a b)) := by
  fin_cases a <;> fin_cases b
  · simpa [zJ] using tendsto_avg_const
  · simpa [zJ] using tendsto_avg_neg_one_pow
  · simpa [zJ] using tendsto_avg_neg_one_pow
  · simpa [zJ_one_sq] using tendsto_avg_const

lemma tendsto_avg_zJ_wJ (ω : Fin 2 → ℝ) (a : Fin 2) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a * wJ ω i) atTop (𝓝 (ω a)) := by
  have hsplit : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a * wJ ω i
      = ω 0 * ((n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a)
        + ω 1 * ((n : ℝ)⁻¹ * ∑ i : Fin n, zJ i a * zJ i 1) := fun n => by
    simp only [wJ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring)
      (Finset.sum_congr rfl fun i _ => by simp [zJ]; ring)
  simp_rw [hsplit]
  have h1 := (tendsto_avg_zJ a).const_mul (ω 0)
  have h2 := (tendsto_avg_zJ_mul a 1).const_mul (ω 1)
  convert h1.add h2 using 2
  fin_cases a <;> simp [Matrix.one_apply]

lemma tendsto_sq_inv_mul : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ * n) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp)

lemma tendsto_sqrt_inv_mul :
    Tendsto (fun n : ℕ => ((n : ℝ) * Real.sqrt n)⁻¹ * n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  show (Real.sqrt n)⁻¹ = _
  field_simp

lemma abs_wJ_sq_zz_le (ω : Fin 2 → ℝ) (i : ℕ) (a b : Fin 2) :
    |wJ ω i ^ 2 * (zJ i a * zJ i b)| ≤ (|ω 0| + |ω 1|) ^ 2 := by
  rw [abs_mul, abs_mul, abs_pow]
  have h1 := abs_zJ_le i a
  have h2 := abs_zJ_le i b
  have h3 := abs_wJ_le ω i
  calc |wJ ω i| ^ 2 * (|zJ i a| * |zJ i b|) ≤ (|ω 0| + |ω 1|) ^ 2 * (1 * 1) := by
        gcongr
    _ = _ := by ring

lemma abs_wJ_zz_le (ω : Fin 2 → ℝ) (i : ℕ) (a b : Fin 2) :
    |wJ ω i * (zJ i a * zJ i b)| ≤ |ω 0| + |ω 1| := by
  rw [abs_mul, abs_mul]
  have h1 := abs_zJ_le i a
  have h2 := abs_zJ_le i b
  have h3 := abs_wJ_le ω i
  calc |wJ ω i| * (|zJ i a| * |zJ i b|) ≤ (|ω 0| + |ω 1|) * (1 * 1) := by gcongr
    _ = _ := by ring

lemma measurable_uJ (n : ℕ) : Measurable (fun ω : Fin 2 → ℝ => fun i : Fin n => uJ n ω i) := by
  unfold uJ wJ; fun_prop

/-- **Non-vacuity of the feasible J test in an overidentified model.** With two instruments
`zᵢ = (1, (−1)ⁱ)`, one regressor `xᵢ = 1`, `θ₀ = 0` and errors `uᵢ = eᵢ + (ω₀ + (−1)ⁱω₁)/√n`
(`ω ∼ N(0, I₂)`, `e` a deterministic spike), every hypothesis of
`two_step_feasible_jtest_chiSq` holds with `G = (1, 0)ᵀ`, `S = I₂`, first-step weight `I₂`,
and the feasible J test has asymptotic rejection probability `P(χ²(1) > c)`. -/
theorem feasible_jtest_witness (c : ℝ) :
    let P : Measure (Fin 2 → ℝ) :=
      (multivariateGaussian 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)).map ofLp
    let z : (n : ℕ) → (Fin 2 → ℝ) → Fin n → Fin 2 → ℝ := fun _ _ i => zJ i
    let x : (n : ℕ) → (Fin 2 → ℝ) → Fin n → Fin 1 → ℝ := fun _ _ _ _ => 1
    let y : (n : ℕ) → (Fin 2 → ℝ) → Fin n → ℝ := fun n ω i => uJ n ω i
    let G : Fin 2 → Fin 1 → ℝ := fun a _ => if a = 0 then 1 else 0
    let I2 : Fin 2 → Fin 2 → ℝ := Matrix.of.symm 1
    ∃ _ : IsProbabilityMeasure P,
      Function.Injective (Matrix.of G *ᵥ ·) ∧ IsUnit (gram (G, I2)).det ∧
      TendstoInMeasure P (fun n ω => sampleG (z n ω) (x n ω)) atTop (fun _ => G) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (x n ω) (y n ω) 0) atTop id
        (fun _ => P) P ∧
      TendstoInMeasure P (fun n ω => sHat (z n ω) (x n ω) (y n ω) 0) atTop (fun _ => I2) ∧
      TendstoInMeasure P (fun n ω => sCross (z n ω) (x n ω) (y n ω) 0) atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun n ω => sQuad (z n ω) (x n ω)) atTop
        (fun _ => fun a b _ _ => I2 a b) ∧
      (∀ n, Measurable (y n)) ∧ P.map id = (multivariateGaussian 0 1).map ofLp ∧
      Tendsto (fun n => P {ω | c < jStat n (sampleG (z n ω) (x n ω))
          (secondWeight I2 (z n ω) (x n ω) (y n ω))
          (sampleZY (z n ω) (y n ω))})
        atTop (𝓝 (chiSq 1 (Set.Ioi c))) := by
  intro P z x y G I2
  have hofLp : Measurable (ofLp : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff hofLp.aemeasurable).mpr inferInstance
  have hev := eventually_ge_atTop (4 : ℕ)
  have hdet : ∀ {E : Type} [PseudoMetricSpace E] {d : ℕ → E} {d₀ : E}, Tendsto d atTop (𝓝 d₀) →
      TendstoInMeasure P (fun n (_ : Fin 2 → ℝ) => d n) atTop (fun _ => d₀) := fun h =>
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun _ => h)
  have hym : ∀ n, Measurable (y n) := measurable_uJ
  -- the Jacobian
  have hGd : Tendsto (fun n => sampleG (z n 0) (x n 0)) atTop (𝓝 G) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun _ => ?_
    simpa [sampleG, z, x, G] using tendsto_avg_zJ a
  have hGhat : TendstoInMeasure P (fun n ω => sampleG (z n ω) (x n ω)) atTop (fun _ => G) :=
    hdet hGd
  -- the moment CLT
  have hgm : ∀ n : ℕ, Measurable (fun ω => Real.sqrt n • sampleMoment (z n ω) (x n ω) (y n ω) 0) :=
    fun n => by
      have h : Measurable (fun ω => sampleMoment (z n ω) (x n ω) (y n ω) 0) :=
        (continuous_sampleMoment (N := n) (k := Fin 1) (l := Fin 2) 0).measurable.comp
          (f := fun ω => (z n ω, x n ω, y n ω))
          (measurable_const.prodMk (measurable_const.prodMk (hym n)))
      exact h.const_smul (Real.sqrt n)
  have hTIM : TendstoInMeasure P
      (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (x n ω) (y n ω) 0) atTop id :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hgm n).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => tendsto_pi_nhds.2 fun a =>
        (tendsto_avg_zJ_wJ ω a).congr' (by
          filter_upwards [hev] with n hn
          exact (sqrt_sampleMoment_eq hn ω a).symm))
  have hTID : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt n • sampleMoment (z n ω) (x n ω) (y n ω) 0) atTop id
      (fun _ => P) P :=
    hTIM.tendstoInDistribution_of_aemeasurable (fun n => (hgm n).aemeasurable)
      aemeasurable_id
  -- the residual variance
  have hSm : ∀ n : ℕ, Measurable (fun ω => sHat (z n ω) (x n ω) (y n ω) 0) := fun n =>
    (continuous_sHat (N := n) (k := Fin 1) (l := Fin 2)).measurable.comp
      (f := fun ω => (z n ω, x n ω, y n ω, (0 : Fin 1 → ℝ)))
      (measurable_const.prodMk (measurable_const.prodMk ((hym n).prodMk measurable_const)))
  have hShat : TendstoInMeasure P (fun n ω => sHat (z n ω) (x n ω) (y n ω) 0) atTop
      (fun _ => I2) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hSm n).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => by
        have h := (tendsto_const_nhds (x := (1 : Matrix (Fin 2) (Fin 2) ℝ) a b)).add
          (tendsto_scaled_sum tendsto_sq_inv_mul
            (f := fun _ i => wJ ω i ^ 2 * (zJ i a * zJ i b)) (fun _ i => abs_wJ_sq_zz_le ω i a b))
        rw [add_zero] at h
        refine h.congr' ?_
        filter_upwards [hev] with n hn
        exact (sHat_eq hn ω a b).symm)
  have hCm : ∀ n : ℕ, Measurable (fun ω => sCross (z n ω) (x n ω) (y n ω) 0) := fun n => by
    simp only [z, x, y]
    unfold sCross dotProduct uJ wJ; fun_prop
  have hCross : TendstoInMeasure P (fun n ω => sCross (z n ω) (x n ω) (y n ω) 0) atTop
      (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hCm n).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b =>
        tendsto_pi_nhds.2 fun c' => by
          have h := tendsto_scaled_sum tendsto_sqrt_inv_mul
            (f := fun _ i => wJ ω i * (zJ i a * zJ i b)) (fun _ i => abs_wJ_zz_le ω i a b)
          refine h.congr' ?_
          filter_upwards [hev] with n hn
          exact (sCross_eq hn ω a b c').symm)
  have hQuad : TendstoInMeasure P (fun n ω => sQuad (z n ω) (x n ω)) atTop
      (fun _ => fun a b _ _ => I2 a b) := by
    have hd : Tendsto (fun n => sQuad (z n 0) (x n 0)) atTop
        (𝓝 (fun a b (_ _ : Fin 1) => I2 a b)) := by
      refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b =>
        tendsto_pi_nhds.2 fun _ => tendsto_pi_nhds.2 fun _ => ?_
      simpa [sQuad, z, x, I2] using tendsto_avg_zJ_mul a b
    exact hdet hd
  have hinj : Function.Injective (Matrix.of G *ᵥ ·) := by
    intro u v h
    have := congrFun h 0
    simp only [mulVec, dotProduct, of_apply, G, Finset.univ_unique, Finset.sum_singleton,
      ite_true, one_mul] at this
    funext i; rw [Subsingleton.elim i 0]; simpa using this
  have hrank : IsUnit (gram (G, I2)).det := by
    simp [gram, Matrix.det_unique, Matrix.mul_apply, G, I2]
  refine ⟨hP, hinj, hrank, hGhat, hTID, hShat, hCross, hQuad, hym, Measure.map_id, ?_⟩
  have := two_step_feasible_jtest_chiSq (θ₀ := (0 : Fin 1 → ℝ)) (W₁ := I2) PosDef.one hinj hrank
    hGhat (hdet (tendsto_const_nhds (x := I2))) hTID hShat hCross hQuad (fun _ => aemeasurable_const)
    (fun _ => aemeasurable_const) (fun n => (hym n).aemeasurable) (fun _ => aemeasurable_const)
    measurable_id Measure.map_id (by simp) c
  simpa using this

end Econ.Asymptotics.FeasibleJ
