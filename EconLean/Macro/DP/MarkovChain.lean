/-
# Finite Markov chains: invariant distributions

Stokey–Lucas (SL) ch. 11 (§11.1–11.2, Thm 11.4); Ljungqvist–Sargent ch. 2;
PLAN gap F11.

**The economics.** Exogenous shocks in macro models (productivity, idiosyncratic
income) are usually finite Markov chains: a **stochastic matrix** `Q`, with
`Q(z, z')` the probability of moving from `z` to `z'`. A distribution `μ` over
states moves to `μQ`, `(μQ)(z') = Σ_z μ(z) Q(z, z')`. An **invariant
(stationary) distribution** satisfies `π Q = π`: the long-run cross-section of
a continuum of agents facing these shocks, or the long-run frequency of each
state. Stationary distributions are the backbone of heterogeneous-agent
(Bewley/Aiyagari) equilibria.

**Results.**
* `exists_invariant` (SL Thm 11.1, finite case): every stochastic matrix on a
  finite nonempty state space has an invariant distribution (Krylov–Bogolyubov:
  a limit point of time-averaged distributions).
* `doeblin` (SL Thm 11.4 / Doeblin's condition): if every transition has
  probability at least `ε > 0`, the invariant distribution is **unique** and
  from any initial `μ`, `μQ^n → π` geometrically in ℓ¹ (twice total
  variation): `Σ_z |μQ^n(z) - π(z)| ≤ 2 (1 - |Z| ε)^n`.

**Documented deviation.** Doeblin is proved under the one-step condition
`Q(z, z') ≥ ε` for all `z, z'`, stronger than SL's Condition D / Thm 11.4
(an `N`-step minorization).
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Sequences

@[expose] public section

namespace Econ

open Filter Topology Set Finset Matrix

variable {Z : Type*} [Fintype Z]

/-- A **stochastic (Markov) matrix**: nonnegative entries, rows summing to 1. -/
def IsStochastic (Q : Matrix Z Z ℝ) : Prop := (∀ z z', 0 ≤ Q z z') ∧ ∀ z, ∑ z', Q z z' = 1

/-- **Probability distributions** on the finite set `Z`. -/
def Distributions (Z : Type*) [Fintype Z] : Set (Z → ℝ) := {μ | (∀ z, 0 ≤ μ z) ∧ ∑ z, μ z = 1}

/-- `π` is an **invariant distribution** of `Q`: a distribution with `π Q = π`. -/
def IsInvariant (Q : Matrix Z Z ℝ) (π : Z → ℝ) : Prop := π ∈ Distributions Z ∧ π ᵥ* Q = π

/-- The **ℓ¹ distance** `Σ_z |μ(z) - ν(z)|` between two vectors on `Z`. For
distributions this is *twice* the total variation distance
`sup_A |μ(A) - ν(A)|`. -/
def l1Dist (μ ν : Z → ℝ) : ℝ := ∑ z, |μ z - ν z|

theorem vecMul_apply' (μ : Z → ℝ) (Q : Matrix Z Z ℝ) (z' : Z) :
    (μ ᵥ* Q) z' = ∑ z, μ z * Q z z' := rfl

/-- A stochastic matrix maps distributions to distributions. -/
theorem IsStochastic.vecMul_mem {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) {μ : Z → ℝ}
    (hμ : μ ∈ Distributions Z) : μ ᵥ* Q ∈ Distributions Z := by
  refine ⟨fun z' => sum_nonneg fun z _ => mul_nonneg (hμ.1 z) (hQ.1 z z'), ?_⟩
  simp only [vecMul_apply']
  rw [sum_comm]
  simp only [← mul_sum, hQ.2, mul_one, hμ.2]

theorem IsStochastic.pow_vecMul_mem [DecidableEq Z] {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) {μ : Z → ℝ}
    (hμ : μ ∈ Distributions Z) (n : ℕ) : μ ᵥ* (Q ^ n) ∈ Distributions Z := by
  induction n with
  | zero => simpa using hμ
  | succ n ih => rw [pow_succ, ← vecMul_vecMul]; exact hQ.vecMul_mem ih

theorem isCompact_distributions : IsCompact (Distributions Z) := by
  have hsub : Distributions Z ⊆ Set.pi univ fun _ => Icc (0 : ℝ) 1 := by
    intro μ hμ z _
    refine ⟨hμ.1 z, ?_⟩
    rw [← hμ.2]
    exact single_le_sum (fun z _ => hμ.1 z) (mem_univ z)
  have hcl : IsClosed (Distributions Z) := by
    have : Distributions Z = (⋂ z, {μ : Z → ℝ | 0 ≤ μ z}) ∩ {μ | ∑ z, μ z = 1} := by
      ext μ; simp [Distributions]
    rw [this]
    exact (isClosed_iInter fun z => isClosed_le continuous_const (continuous_apply z)).inter
      (isClosed_eq (continuous_finsetSum _ fun z _ => continuous_apply z) continuous_const)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

/-- **Existence of an invariant distribution** (finite Markov chains;
Krylov–Bogolyubov). -/
theorem exists_invariant [Nonempty Z] {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) :
    ∃ π, IsInvariant Q π := by
  classical
  -- start from a point mass
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  set μ₀ : Z → ℝ := Pi.single z₀ 1
  have hμ₀ : μ₀ ∈ Distributions Z :=
    ⟨fun z => by by_cases h : z = z₀ <;> simp [μ₀, h], by simp [μ₀]⟩
  set a : ℕ → Z → ℝ := fun t => μ₀ ᵥ* (Q ^ t)
  have ha : ∀ t, a t ∈ Distributions Z := fun t => hQ.pow_vecMul_mem hμ₀ t
  -- Cesàro averages `ν_n = (1/(n+1)) Σ_{t ≤ n} a_t`
  set ν : ℕ → Z → ℝ := fun n => (1 / ((n : ℝ) + 1)) • ∑ t ∈ range (n + 1), a t
  have hν : ∀ n, ν n ∈ Distributions Z := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine ⟨fun z => ?_, ?_⟩
    · simp only [ν, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (sum_nonneg fun t _ => (ha t).1 z)
    · simp only [ν, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_sum]
      rw [sum_comm]
      simp only [fun t => (ha t).2, sum_const, card_range, nsmul_eq_mul, mul_one]
      push_cast
      field_simp
  obtain ⟨π, hπ, φ, hφ, hlim⟩ := isCompact_distributions.tendsto_subseq hν
  refine ⟨π, hπ, ?_⟩
  -- `ν_n Q - ν_n = (a_{n+1} - a_0)/(n+1) → 0`
  have hdiff : ∀ n, ν n ᵥ* Q - ν n = (1 / ((n : ℝ) + 1)) • (a (n + 1) - a 0) := by
    intro n
    have hshift : (∑ t ∈ range (n + 1), a t) ᵥ* Q = ∑ t ∈ range (n + 1), a (t + 1) := by
      rw [Matrix.sum_vecMul]
      refine sum_congr rfl fun t _ => ?_
      simp only [a, vecMul_vecMul, pow_succ]
    simp only [ν, Matrix.smul_vecMul, hshift, ← smul_sub]
    congr 1
    rw [← sum_sub_distrib, sum_range_sub]
  have hcont : Continuous fun μ : Z → ℝ => μ ᵥ* Q - μ :=
    (continuous_id.matrix_vecMul continuous_const).sub continuous_id
  have h1 : Tendsto (fun k => ν (φ k) ᵥ* Q - ν (φ k)) atTop (𝓝 (π ᵥ* Q - π)) :=
    (hcont.tendsto π).comp hlim
  have h2 : Tendsto (fun n => ν n ᵥ* Q - ν n) atTop (𝓝 0) := by
    simp only [hdiff]
    rw [tendsto_pi_nhds]
    intro z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    have hb : ∀ n, |a (n + 1) z - a 0 z| ≤ 1 := by
      intro n
      have h1 := (ha (n + 1)).1 z
      have h2 := (ha 0).1 z
      have h3 : a (n + 1) z ≤ 1 := by
        rw [← (ha (n + 1)).2]; exact single_le_sum (fun z _ => (ha (n + 1)).1 z) (mem_univ z)
      have h4 : a 0 z ≤ 1 := by
        rw [← (ha 0).2]; exact single_le_sum (fun z _ => (ha 0).1 z) (mem_univ z)
      rw [abs_le]; constructor <;> linarith
    have hlim0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero_norm (fun n => ?_) hlim0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    exact mul_le_of_le_one_right (by positivity) (hb n)
  have h3 := tendsto_nhds_unique h1 (h2.comp hφ.tendsto_atTop)
  exact sub_eq_zero.1 h3

/-- **Doeblin contraction**: if `ε ≤ Q(z, z')` everywhere, then for any `d`
with `Σ d = 0`, `‖d Q‖₁ ≤ (1 - |Z| ε) ‖d‖₁`. -/
theorem l1Dist_contract {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) {ε : ℝ}
    (hε : ∀ z z', ε ≤ Q z z') {μ ν : Z → ℝ} (hμ : μ ∈ Distributions Z)
    (hν : ν ∈ Distributions Z) :
    l1Dist (μ ᵥ* Q) (ν ᵥ* Q) ≤ (1 - Fintype.card Z * ε) * l1Dist μ ν := by
  set d : Z → ℝ := fun z => μ z - ν z
  have hd : ∑ z, d z = 0 := by simp only [d, sum_sub_distrib, hμ.2, hν.2, sub_self]
  -- subtract the common floor `ε`: `(dQ)(z') = Σ_z d(z) (Q(z,z') - ε)`
  have key : ∀ z', (μ ᵥ* Q) z' - (ν ᵥ* Q) z' = ∑ z, d z * (Q z z' - ε) := by
    intro z'
    have e : ∀ z, d z * (Q z z' - ε) = (μ z * Q z z' - ν z * Q z z') - d z * ε := fun z => by
      simp only [d]; ring
    rw [eq_comm, sum_congr rfl (fun z _ => e z), sum_sub_distrib, sum_sub_distrib, ← sum_mul, hd,
      zero_mul, sub_zero]
    rfl
  unfold l1Dist
  calc ∑ z', |(μ ᵥ* Q) z' - (ν ᵥ* Q) z'| = ∑ z', |∑ z, d z * (Q z z' - ε)| := by
        simp only [key]
    _ ≤ ∑ z', ∑ z, |d z| * (Q z z' - ε) := sum_le_sum fun z' _ =>
        (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun z _ => by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hε z z'))]))
    _ = ∑ z, |d z| * (1 - Fintype.card Z * ε) := by
        rw [sum_comm]
        refine sum_congr rfl fun z _ => ?_
        rw [← mul_sum, sum_sub_distrib, hQ.2, sum_const, card_univ, nsmul_eq_mul]
    _ = (1 - Fintype.card Z * ε) * ∑ z, |μ z - ν z| := by rw [← sum_mul, mul_comm]

theorem l1Dist_le_two {μ ν : Z → ℝ} (hμ : μ ∈ Distributions Z) (hν : ν ∈ Distributions Z) :
    l1Dist μ ν ≤ 2 := by
  unfold l1Dist
  calc ∑ z, |μ z - ν z| ≤ ∑ z, (μ z + ν z) := sum_le_sum fun z _ => by
        rw [abs_le]; constructor <;> linarith [hμ.1 z, hν.1 z]
    _ = 2 := by rw [sum_add_distrib, hμ.2, hν.2]; norm_num

theorem l1Dist_self (μ : Z → ℝ) : l1Dist μ μ = 0 := by simp [l1Dist]

theorem l1Dist_eq_zero {μ ν : Z → ℝ} (h : l1Dist μ ν = 0) : μ = ν := by
  funext z
  have := (sum_eq_zero_iff_of_nonneg (fun z _ => abs_nonneg (μ z - ν z))).1 h z (mem_univ z)
  linarith [abs_eq_zero.1 this]

/-- **Doeblin's theorem** (SL Thm 11.4, finite case). If every transition
probability is at least `ε > 0`, then `Q` has a **unique** invariant
distribution `π`, and every initial distribution converges to it
geometrically in total variation: `‖μQ^n - π‖₁ ≤ 2 (1 - |Z| ε)^n`. -/
theorem doeblin [Nonempty Z] [DecidableEq Z] {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ z z', ε ≤ Q z z') :
    ∃ π, IsInvariant Q π ∧ (∀ π', IsInvariant Q π' → π' = π) ∧ ∀ μ ∈ Distributions Z, ∀ n : ℕ,
      l1Dist (μ ᵥ* (Q ^ n)) π ≤ 2 * (1 - Fintype.card Z * ε) ^ n := by
  obtain ⟨π, hπ⟩ := exists_invariant hQ
  set r := 1 - Fintype.card Z * ε
  -- `r ∈ [0, 1)`: a row sums to 1 and has `|Z|` entries `≥ ε`
  have hr0 : 0 ≤ r := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    have : ∑ z', ε ≤ ∑ z', Q z z' := sum_le_sum fun z' _ => hε z z'
    rw [hQ.2, sum_const, card_univ, nsmul_eq_mul] at this
    simp only [r]; linarith
  have hr1 : r < 1 := by
    have : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
    simp only [r]; nlinarith
  have hiter : ∀ μ ∈ Distributions Z, ∀ n : ℕ,
      l1Dist (μ ᵥ* (Q ^ n)) π ≤ r ^ n * l1Dist μ π := by
    intro μ hμ n
    induction n with
    | zero => simp
    | succ n ih =>
      have hπn : π ᵥ* (Q ^ (n + 1)) = π := by
        induction n + 1 with
        | zero => simp
        | succ m ihm => rw [pow_succ, ← vecMul_vecMul, ihm, hπ.2]
      calc l1Dist (μ ᵥ* (Q ^ (n + 1))) π
          = l1Dist ((μ ᵥ* (Q ^ n)) ᵥ* Q) (π ᵥ* Q) := by rw [pow_succ, ← vecMul_vecMul, hπ.2]
        _ ≤ r * l1Dist (μ ᵥ* (Q ^ n)) π :=
            l1Dist_contract hQ hε (hQ.pow_vecMul_mem hμ n) hπ.1
        _ ≤ r * (r ^ n * l1Dist μ π) := mul_le_mul_of_nonneg_left ih hr0
        _ = r ^ (n + 1) * l1Dist μ π := by ring
  refine ⟨π, hπ, ?_, fun μ hμ n => ?_⟩
  rotate_left
  · calc l1Dist (μ ᵥ* (Q ^ n)) π ≤ r ^ n * l1Dist μ π := hiter μ hμ n
      _ ≤ r ^ n * 2 := mul_le_mul_of_nonneg_left (l1Dist_le_two hμ hπ.1) (pow_nonneg hr0 n)
      _ = 2 * r ^ n := by ring
  · -- uniqueness: another invariant `π'` stays at distance `≤ r^n · 2 → 0`
    intro π' hπ'
    have hfix : ∀ n : ℕ, π' ᵥ* (Q ^ n) = π' := by
      intro n
      induction n with
      | zero => simp
      | succ m ihm => rw [pow_succ, ← vecMul_vecMul, ihm, hπ'.2]
    have hle : ∀ n : ℕ, l1Dist π' π ≤ r ^ n * 2 := fun n => by
      have := hiter π' hπ'.1 n
      rw [hfix] at this
      exact this.trans (mul_le_mul_of_nonneg_left (l1Dist_le_two hπ'.1 hπ.1) (pow_nonneg hr0 n))
    have hlim : Tendsto (fun n : ℕ => r ^ n * 2) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const 2
    have h0 : l1Dist π' π ≤ 0 := ge_of_tendsto' hlim hle
    exact l1Dist_eq_zero (le_antisymm h0 (sum_nonneg fun z _ => abs_nonneg _))

end Econ
