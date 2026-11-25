/-
# Stochastic growth: the invariant distribution of capital

Brock–Mirman (1972); Stokey–Lucas–Prescott ch. 13.3 (and Exercise 13.5);
Hopenhayn–Prescott (1992); Ljungqvist–Sargent ch. 3.

In the stochastic Brock–Mirman model (log utility, Cobb–Douglas output
`A(z) k^α`, full depreciation, i.i.d. productivity `A(z)`), the optimal policy
is `k' = αβ A(z) k^α`. In logs, `x = log k` follows the linear autoregression

  `x' = μ(z) + α x`,  `μ(z) = log(αβ) + log A(z)`,

with `z` i.i.d. This file studies that process with a two-state shock.

**The ergodic set** (`LogCapital.S`). With `μ(0) ≤ μ(1)` and `0 ≤ α < 1`,
the interval `[x_lo, x_hi] = [μ(0)/(1-α), μ(1)/(1-α)]` between the fixed points
of the worst-shock and best-shock maps is invariant.

**Existence and uniqueness** (`exists_stationary`, `stationary_unique`).
The process on `[x_lo, x_hi] × {0, 1}` has exactly one stationary
distribution. Existence is Krylov–Bogoliubov for the Feller kernel; uniqueness
is the monotone-mixing theorem `unique_invariant_of_splitting`: the transition
is increasing in `(x, z)`, and from any state a run of `n` bad shocks brings
`x` below the midpoint while a run of good shocks brings it above, where
`α^n ≤ 1/2`.

**Moments** (`marginal_eq`, `integral_x`). Under any stationary distribution
the shock is distributed as `q`, and mean log capital is
`E[x] = E[μ(z)] / (1 - α)`.

**Brock–Mirman** (`brockMirman`, `brockMirman_policy`,
`brockMirman_mean_log_capital`). With `μ(z) = log(αβ) + log A(z)` the map is
the log of the policy `k' = αβ A(z) k^α`, and the stationary mean of log
capital is `(log(αβ) + E[log A]) / (1 - α)`.

**Scope.** Optimality of `k' = αβ A(z) k^α` in the stochastic model is not
re-proved here (the deterministic closed form is verified in `BrockMirman`);
the theorems are about the capital process that this policy generates. The
shock has two values and is i.i.d.; the process is started inside the ergodic
interval (outside it, log capital converges to it geometrically, which is not
formalized). Convergence of distributions to the stationary one is not
formalized.
-/
module

public import EconLean.Macro.HA.StationaryUnique

@[expose] public section

namespace Econ

open Set Filter Topology MeasureTheory ProbabilityTheory BoundedContinuousFunction

/-- **Chains of one-step lower bounds**: if from every state `κ(x, A₀) ≥ p`,
and from every `y ∈ Aₙ`, `κ(y, Aₙ₊₁) ≥ q`, then `κ^{n+1}(x, Aₙ) ≥ p qⁿ`. -/
theorem le_pow_real_of_chain {X : Type*} [MeasurableSpace X] {κ : Kernel X X} [IsMarkovKernel κ]
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n)) {p q : ℝ} (hq : 0 ≤ q)
    (h0 : ∀ x, p ≤ (κ x).real (A 0)) (hstep : ∀ n, ∀ y ∈ A n, q ≤ (κ y).real (A (n + 1))) :
    ∀ n x, p * q ^ n ≤ ((κ ^ (n + 1)) x).real (A n) := by
  intro n
  induction n with
  | zero => intro x; rw [pow_zero, mul_one, zero_add, pow_one]; exact h0 x
  | succ n ih =>
    intro x
    have := isMarkovKernel_pow κ (n + 1)
    rw [pow_succ' κ (n + 1), pow_succ, ← mul_assoc]
    exact le_comp_real (hAm n) (hAm (n + 1)) hq ih (hstep n) x

/-- The log-capital process `x' = μ(z) + α x` with an i.i.d. two-state shock
`z ∈ {0, 1}` (bad, good) drawn with probabilities `q`. -/
structure LogCapital where
  α : ℝ
  μ : Fin 2 → ℝ
  q : Fin 2 → ℝ
  α_nonneg : 0 ≤ α
  α_lt_one : α < 1
  μ_le : μ 0 ≤ μ 1
  q_pos : ∀ z, 0 < q z
  q_sum : q 0 + q 1 = 1

namespace LogCapital

variable (P : LogCapital)

/-- Fixed point of the bad-shock map. -/
noncomputable def xlo : ℝ := P.μ 0 / (1 - P.α)
/-- Fixed point of the good-shock map. -/
noncomputable def xhi : ℝ := P.μ 1 / (1 - P.α)

theorem one_sub_α_pos : 0 < 1 - P.α := by linarith [P.α_lt_one]

theorem xlo_eq : P.xlo = P.μ 0 + P.α * P.xlo := by
  have := P.one_sub_α_pos
  unfold xlo; field_simp; ring

theorem xhi_eq : P.xhi = P.μ 1 + P.α * P.xhi := by
  have := P.one_sub_α_pos
  unfold xhi; field_simp; ring

theorem xlo_le_xhi : P.xlo ≤ P.xhi :=
  div_le_div_of_nonneg_right P.μ_le P.one_sub_α_pos.le

theorem μ_ge (z : Fin 2) : P.μ 0 ≤ P.μ z := by
  fin_cases z
  · exact le_rfl
  · exact P.μ_le

theorem μ_le' (z : Fin 2) : P.μ z ≤ P.μ 1 := by
  fin_cases z
  · exact P.μ_le
  · exact le_rfl

theorem μ_mono : Monotone P.μ := by
  intro a b h
  fin_cases a <;> fin_cases b
  · exact le_rfl
  · exact P.μ_le
  · exact absurd h (by decide)
  · exact le_rfl

/-- The ergodic interval `[x_lo, x_hi]`. -/
abbrev S : Type := Icc P.xlo P.xhi

instance : Nonempty P.S := ⟨⟨P.xlo, le_rfl, P.xlo_le_xhi⟩⟩

instance : CompactSpace P.S := isCompact_iff_compactSpace.1 isCompact_Icc

/-- The transition `x' = μ(z) + α x`, which maps `[x_lo, x_hi]` into itself. -/
noncomputable def g (s : P.S × Fin 2) : P.S :=
  ⟨P.μ s.2 + P.α * s.1, by
    have h1 := s.1.2.1
    have h2 := s.1.2.2
    constructor
    · nlinarith [P.xlo_eq, P.μ_ge s.2, P.α_nonneg, mul_le_mul_of_nonneg_left h1 P.α_nonneg]
    · nlinarith [P.xhi_eq, P.μ_le' s.2, P.α_nonneg, mul_le_mul_of_nonneg_left h2 P.α_nonneg]⟩

theorem g_coe (s : P.S × Fin 2) : (P.g s : ℝ) = P.μ s.2 + P.α * s.1 := rfl

theorem continuous_g : Continuous P.g :=
  Continuous.subtype_mk (((continuous_of_discreteTopology (f := P.μ)).comp continuous_snd).add
    (continuous_const.mul (continuous_subtype_val.comp continuous_fst))) _

theorem measurable_g : Measurable P.g := P.continuous_g.measurable

theorem monotone_g : Monotone P.g := fun s s' h => by
  show P.μ s.2 + P.α * s.1 ≤ P.μ s'.2 + P.α * s'.1
  have hz : P.μ s.2 ≤ P.μ s'.2 := P.μ_mono h.2
  have hx : (s.1 : ℝ) ≤ s'.1 := h.1
  nlinarith [P.α_nonneg]

/-- The i.i.d. shock matrix: every row is `q`. -/
def Q : Fin 2 → Fin 2 → ℝ := fun _ z' => P.q z'

theorem Q_nonneg (z z' : Fin 2) : 0 ≤ P.Q z z' := (P.q_pos z').le

theorem Q_sum (z : Fin 2) : ∑ z', P.Q z z' = 1 := by
  simp [Q, Fin.sum_univ_two, P.q_sum]

/-- The transition kernel of `(x, z)`. -/
noncomputable def K : Kernel (P.S × Fin 2) (P.S × Fin 2) := policyKernel P.Q P.g P.measurable_g

instance : IsMarkovKernel P.K := isMarkovKernel_policyKernel P.Q_nonneg P.Q_sum _ _

/-- **Existence of a stationary distribution** of `(x, z)` (Krylov–Bogoliubov:
the kernel is Feller on a compact space). -/
theorem exists_stationary :
    ∃ π : Measure (P.S × Fin 2), IsProbabilityMeasure π ∧ Kernel.Invariant P.K π :=
  exists_invariant_of_feller P.K (isFeller_policyKernel P.Q_nonneg P.continuous_g _)

theorem K_real_ge (s : P.S × Fin 2) {U : Set (P.S × Fin 2)} (hU : MeasurableSet U) {z₀ : Fin 2}
    (hz₀ : (P.g s, z₀) ∈ U) : P.q z₀ ≤ (P.K s).real U :=
  le_policyKernel_real P.Q_nonneg P.g P.measurable_g s hU hz₀

/-- **Uniqueness of the stationary distribution** (Hopenhayn–Prescott): the
process `x' = μ(z) + α x` with i.i.d. two-state shocks has at most one
stationary distribution on `[x_lo, x_hi] × {0, 1}`. (Every stationary
distribution of the process on all of `ℝ` lives on this interval, since the
distance to it shrinks by the factor `α`; that equivalence is not formalized.) -/
theorem stationary_unique {π π' : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    [IsProbabilityMeasure π'] (hπ : Kernel.Invariant P.K π) (hπ' : Kernel.Invariant P.K π') :
    π' = π := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) P.α_lt_one
  set D := P.xhi - P.xlo
  have hD : 0 ≤ D := sub_nonneg.2 P.xlo_le_xhi
  have hαn : ∀ m : ℕ, 0 ≤ P.α ^ m := fun m => pow_nonneg P.α_nonneg m
  -- bad runs
  let A : ℕ → Set (P.S × Fin 2) := fun m =>
    {p | (p.1 : ℝ) ≤ P.xlo + P.α ^ m * D} ∩ Prod.snd ⁻¹' {0}
  have hAm : ∀ m, MeasurableSet (A m) := fun m =>
    (measurableSet_le (continuous_subtype_val.comp continuous_fst).measurable measurable_const).inter
      (measurable_snd (measurableSet_singleton 0))
  have hlowA := le_pow_real_of_chain (κ := P.K) hAm (p := P.q 0) (P.q_pos 0).le
    (fun x => P.K_real_ge x (hAm 0) ⟨by
      show (P.g x : ℝ) ≤ P.xlo + P.α ^ 0 * D
      simp only [pow_zero, one_mul, D]; linarith [(P.g x).2.2], rfl⟩)
    (fun m y hy => P.K_real_ge y (hAm (m + 1)) ⟨by
      show (P.g y : ℝ) ≤ P.xlo + P.α ^ (m + 1) * D
      have hy0 : y.2 = 0 := hy.2
      have hy1 : (y.1 : ℝ) ≤ P.xlo + P.α ^ m * D := hy.1
      rw [P.g_coe, hy0, pow_succ]
      have := mul_le_mul_of_nonneg_left hy1 P.α_nonneg
      nlinarith [P.xlo_eq], rfl⟩)
  -- good runs
  let B : ℕ → Set (P.S × Fin 2) := fun m =>
    {p | P.xhi - P.α ^ m * D ≤ (p.1 : ℝ)} ∩ Prod.snd ⁻¹' {1}
  have hBm : ∀ m, MeasurableSet (B m) := fun m =>
    (measurableSet_le measurable_const (continuous_subtype_val.comp continuous_fst).measurable).inter
      (measurable_snd (measurableSet_singleton 1))
  have hupB := le_pow_real_of_chain (κ := P.K) hBm (p := P.q 1) (P.q_pos 1).le
    (fun x => P.K_real_ge x (hBm 0) ⟨by
      show P.xhi - P.α ^ 0 * D ≤ (P.g x : ℝ)
      simp only [pow_zero, one_mul, D]; linarith [(P.g x).2.1], rfl⟩)
    (fun m y hy => P.K_real_ge y (hBm (m + 1)) ⟨by
      show P.xhi - P.α ^ (m + 1) * D ≤ (P.g y : ℝ)
      have hy0 : y.2 = 1 := hy.2
      have hy1 : P.xhi - P.α ^ m * D ≤ (y.1 : ℝ) := hy.1
      rw [P.g_coe, hy0, pow_succ]
      have := mul_le_mul_of_nonneg_left hy1 P.α_nonneg
      nlinarith [P.xhi_eq], rfl⟩)
  -- the splitting state: the midpoint, bad shock
  let xm : P.S := ⟨(P.xlo + P.xhi) / 2, by constructor <;> linarith [P.xlo_le_xhi]⟩
  let c : P.S × Fin 2 := (xm, 0)
  have hsmall : P.α ^ n * D ≤ D / 2 := by nlinarith
  set δ := min (P.q 0 * P.q 0 ^ n) (P.q 1 * P.q 1 ^ n)
  have hδ : 0 < δ := lt_min (by have := P.q_pos 0; positivity) (by have := P.q_pos 1; positivity)
  have hIic : MeasurableSet (Iic c) := by
    have : Iic c = Prod.fst ⁻¹' Iic c.1 ∩ Prod.snd ⁻¹' Iic c.2 := by
      ext p; exact Prod.le_def
    rw [this]
    exact (measurable_fst measurableSet_Iic).inter (measurable_snd (toFinite _).measurableSet)
  have := isMarkovKernel_pow P.K (n + 1)
  refine unique_invariant_of_splitting (κ := P.K) (N := n + 1) (c := c)
    (isMonotoneKernel_policyKernel P.Q_nonneg (fun _ _ _ => rfl) P.measurable_g P.monotone_g)
    generateFrom_upperSets_prod hδ hIic (fun x => ?_) (fun x => ?_) hπ hπ'
  · have hsub : A n ⊆ Iic c := by
      rintro p ⟨hp1, hp2⟩
      refine Prod.mk_le_mk.2 ⟨?_, le_of_eq hp2⟩
      show (p.1 : ℝ) ≤ (P.xlo + P.xhi) / 2
      have : (p.1 : ℝ) ≤ P.xlo + P.α ^ n * D := hp1
      simp only [D] at hsmall this; linarith
    exact (min_le_left _ _).trans ((hlowA n x).trans (measureReal_mono hsub (measure_ne_top _ _)))
  · have hsub : B n ⊆ Ici c := by
      rintro p ⟨hp1, -⟩
      refine Prod.mk_le_mk.2 ⟨?_, Fin.zero_le _⟩
      show (P.xlo + P.xhi) / 2 ≤ (p.1 : ℝ)
      have : P.xhi - P.α ^ n * D ≤ (p.1 : ℝ) := hp1
      simp only [D] at hsmall this; linarith
    exact (min_le_right _ _).trans ((hupB n x).trans (measureReal_mono hsub (measure_ne_top _ _)))

/-- `(K ∘ π)(U) = ∫ K(s, U) dπ` for stationary `π`. -/
theorem real_eq_integral {π : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant P.K π) {U : Set (P.S × Fin 2)} (hU : MeasurableSet U) :
    π.real U = ∫ s, (P.K s).real U ∂π := by
  rw [← comp_real_eq_integral P.K π hU, (hπ : P.K ∘ₘ π = π)]

/-- **The shock is distributed as `q` under every stationary distribution.** -/
theorem marginal_eq {π : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant P.K π) (z : Fin 2) :
    π.real (Prod.snd ⁻¹' {z}) = P.q z := by
  have hU : MeasurableSet (Prod.snd ⁻¹' {z} : Set (P.S × Fin 2)) :=
    measurable_snd (measurableSet_singleton z)
  rw [P.real_eq_integral hπ hU]
  have : ∀ s, (P.K s).real (Prod.snd ⁻¹' {z}) = P.q z := fun s => by
    rw [K, policyKernel_real_apply P.Q_nonneg P.g P.measurable_g s hU, Fin.sum_univ_two]
    fin_cases z <;> simp [Q, Set.indicator]
  simp only [this, integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- Log capital as a bounded continuous function of the state. -/
noncomputable def xfun : P.S × Fin 2 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun s => (s.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩

/-- **Mean log capital under the stationary distribution**:
`E[x] = (q(0) μ(0) + q(1) μ(1)) / (1 - α)`. -/
theorem integral_x {π : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant P.K π) :
    ∫ s, (s.1 : ℝ) ∂π = (P.q 0 * P.μ 0 + P.q 1 * P.μ 1) / (1 - P.α) := by
  have hint : Integrable (fun s : P.S × Fin 2 => (s.1 : ℝ)) π := P.xfun.integrable _
  -- stationarity: `E[x] = E[μ(z)] + α E[x]`
  have hstat : ∫ s, (s.1 : ℝ) ∂π = ∫ s, (P.μ s.2 + P.α * s.1) ∂π := by
    conv_lhs => rw [← (hπ : P.K ∘ₘ π = π)]
    rw [integral_comp_measure (f := fun s : P.S × Fin 2 => (s.1 : ℝ)) (P.xfun.integrable _)]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show ∫ y, P.xfun y ∂(P.K s) = _
    rw [K, integral_policyKernel P.Q_nonneg]
    show ∑ z', P.Q s.2 z' * (P.g s : ℝ) = _
    rw [← Finset.sum_mul, P.Q_sum, one_mul, P.g_coe]
  -- `E[μ(z)] = q(0) μ(0) + q(1) μ(1)`
  have hm : ∀ z : Fin 2, MeasurableSet (Prod.snd ⁻¹' {z} : Set (P.S × Fin 2)) :=
    fun z => measurable_snd (measurableSet_singleton z)
  have hsplit : (fun s : P.S × Fin 2 => P.μ s.2) = fun s =>
      P.μ 0 * (Prod.snd ⁻¹' {(0 : Fin 2)}).indicator 1 s +
      P.μ 1 * (Prod.snd ⁻¹' {(1 : Fin 2)}).indicator 1 s := by
    funext s
    obtain ⟨x, z⟩ := s
    fin_cases z <;> simp [Set.indicator]
  have hi : ∀ z : Fin 2, Integrable ((Prod.snd ⁻¹' {z}).indicator (1 : P.S × Fin 2 → ℝ)) π :=
    fun z => (integrable_const (1 : ℝ)).indicator (hm z)
  have hμint : Integrable (fun s : P.S × Fin 2 => P.μ s.2) π := by
    rw [hsplit]; exact ((hi 0).const_mul _).add ((hi 1).const_mul _)
  have hμ : ∫ s, P.μ s.2 ∂π = P.q 0 * P.μ 0 + P.q 1 * P.μ 1 := by
    rw [hsplit, integral_add ((hi 0).const_mul _) ((hi 1).const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator_one (hm 0), integral_indicator_one (hm 1),
      P.marginal_eq hπ 0, P.marginal_eq hπ 1]
    ring
  rw [integral_add hμint (hint.const_mul _), integral_const_mul, hμ] at hstat
  rw [eq_div_iff P.one_sub_α_pos.ne']
  linarith

/-- **Exactly one stationary distribution.** -/
theorem exists_unique_stationary :
    ∃ π : Measure (P.S × Fin 2), IsProbabilityMeasure π ∧ Kernel.Invariant P.K π ∧
      ∀ π' : Measure (P.S × Fin 2), IsProbabilityMeasure π' → Kernel.Invariant P.K π' → π' = π := by
  obtain ⟨π, hπ, hinv⟩ := P.exists_stationary
  exact ⟨π, hπ, hinv, fun π' _ hπ' => P.stationary_unique hinv hπ'⟩

/-- **The stochastic Brock–Mirman model in logs**: `α, β ∈ (0, 1)`,
productivity `A(0) ≤ A(1)` (positive), i.i.d. with probabilities `q`, and
`μ(z) = log(αβ) + log A(z)` (meaningful for `β > 0`; `β < 1` is not needed
for the capital process). -/
noncomputable def brockMirman (α β : ℝ) (A q : Fin 2 → ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hA : ∀ z, 0 < A z) (hA01 : A 0 ≤ A 1) (hq : ∀ z, 0 < q z)
    (hqs : q 0 + q 1 = 1) : LogCapital where
  α := α
  μ := fun z => Real.log (α * β) + Real.log (A z)
  q := q
  α_nonneg := hα0.le
  α_lt_one := hα1
  μ_le := by
    show Real.log (α * β) + Real.log (A 0) ≤ Real.log (α * β) + Real.log (A 1)
    linarith [Real.log_le_log (hA 0) hA01]
  q_pos := hq
  q_sum := hqs

section BrockMirman

variable {α β : ℝ} {A q : Fin 2 → ℝ} {hα0 : 0 < α} {hα1 : α < 1}
  {hA : ∀ z, 0 < A z} {hA01 : A 0 ≤ A 1} {hq : ∀ z, 0 < q z} {hqs : q 0 + q 1 = 1}

/-- **The map is the Brock–Mirman policy in logs**: for `k > 0`,
`μ(z) + α log k = log(αβ A(z) k^α)`. -/
theorem brockMirman_policy (hβ0 : 0 < β) (z : Fin 2) {k : ℝ} (hk : 0 < k) :
    (brockMirman α β A q hα0 hα1 hA hA01 hq hqs).μ z +
      (brockMirman α β A q hα0 hα1 hA hA01 hq hqs).α * Real.log k =
      Real.log (α * β * A z * k ^ α) := by
  show Real.log (α * β) + Real.log (A z) + α * Real.log k = _
  have hab : 0 < α * β := mul_pos hα0 hβ0
  rw [Real.log_mul (by have := hA z; positivity) (Real.rpow_pos_of_pos hk α).ne',
    Real.log_mul hab.ne' (hA z).ne', Real.log_rpow hk]

/-- **Mean log capital in the stochastic Brock–Mirman model**: under the
(unique) stationary distribution,
`E[log k] = (log(αβ) + E[log A]) / (1 - α)`. -/
theorem brockMirman_mean_log_capital
    {π : Measure ((brockMirman α β A q hα0 hα1 hA hA01 hq hqs).S × Fin 2)}
    [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (brockMirman α β A q hα0 hα1 hA hA01 hq hqs).K π) :
    ∫ s, (s.1 : ℝ) ∂π =
      (Real.log (α * β) + (q 0 * Real.log (A 0) + q 1 * Real.log (A 1))) / (1 - α) := by
  rw [integral_x _ hπ]
  show (q 0 * (Real.log (α * β) + Real.log (A 0)) + q 1 * (Real.log (α * β) + Real.log (A 1))) /
    (1 - α) = _
  congr 1
  linear_combination Real.log (α * β) * hqs

end BrockMirman

end LogCapital

end Econ
