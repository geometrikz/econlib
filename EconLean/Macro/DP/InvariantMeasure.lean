/-
# Invariant distributions of Feller Markov kernels (Krylov–Bogolyubov)

Stokey–Lucas (SL) §8.1 and §12.1, Thm 12.10; Krylov–Bogolyubov.

A Markov kernel `κ` on a state space `X` (the law of tomorrow's state given
today's) is **Feller** if it maps bounded continuous functions to continuous
functions: `x ↦ ∫ f dκ(x)` is continuous for every bounded continuous `f`.
A probability measure `μ` is **invariant** (a stationary distribution) if
`κ ∘ₘ μ = μ`. Mathlib calls this `ProbabilityTheory.Kernel.Invariant`.

**Theorem** (SL Thm 12.10). A Feller Markov kernel on a compact metrizable
space has an invariant probability measure.

**Proof** (Krylov–Bogolyubov). Fix `x`. Let `μₙ = δₓ κⁿ` be the
distribution after `n` steps, and let `νₙ = (n+1)⁻¹ Σ_{k≤n} μ_k` be their
Cesàro averages. For bounded continuous `f`, write `Kf(x) = ∫ f dκ(x)`.
Then `∫ Kf dνₙ - ∫ f dνₙ = (∫ f dμ_{n+1} - ∫ f dμ₀)/(n+1) → 0`. The space of
probability measures on a compact space is compact (Prokhorov), so `(νₙ)` has
a cluster point `ν`. Along an ultrafilter converging to `ν`, the integrals
converge, so `∫ Kf dν = ∫ f dν` for every `f`. Since `∫ f d(κ ∘ₘ ν) = ∫ Kf dν`
and finite Borel measures are determined by their integrals of bounded
continuous functions, `κ ∘ₘ ν = ν`.

This is the stochastic counterpart of Mathlib's
`exists_measurePreserving_probabilityMeasure` (deterministic maps), and the
proof follows it.
-/
module

public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A Markov kernel is **Feller** if `x ↦ ∫ f dκ(x)` is continuous for every
bounded continuous `f`. -/
def IsFeller [TopologicalSpace X] (κ : Kernel X X) : Prop :=
  ∀ f : X →ᵇ ℝ, Continuous fun x => ∫ y, f y ∂(κ x)

/-- Integral against `κ ∘ₘ μ`: `∫ f d(κ ∘ₘ μ) = ∫ (∫ f dκ(x)) dμ(x)`. -/
theorem integral_comp_measure {κ : Kernel X X} {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f (κ ∘ₘ μ)) : ∫ y, f y ∂(κ ∘ₘ μ) = ∫ x, ∫ y, f y ∂(κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf]
  simp [Kernel.const_apply]

/-- The distribution after `n` steps from `x`: `δₓ κⁿ`. -/
noncomputable def distIter (κ : Kernel X X) (x : X) : ℕ → Measure X
  | 0 => Measure.dirac x
  | n + 1 => κ ∘ₘ distIter κ x n

theorem isProbabilityMeasure_distIter (κ : Kernel X X) [IsMarkovKernel κ] (x : X) :
    ∀ n, IsProbabilityMeasure (distIter κ x n)
  | 0 => by unfold distIter; infer_instance
  | n + 1 => by
    have := isProbabilityMeasure_distIter κ x n
    unfold distIter; infer_instance

/-- `Σ_{k<n} δₓ κᵏ`, by recursion. -/
noncomputable def distSum (κ : Kernel X X) (x : X) : ℕ → Measure X
  | 0 => 0
  | n + 1 => distSum κ x n + distIter κ x n

theorem distSum_univ (κ : Kernel X X) [IsMarkovKernel κ] (x : X) :
    ∀ n, distSum κ x n Set.univ = n
  | 0 => by simp [distSum]
  | n + 1 => by
    have := isProbabilityMeasure_distIter κ x n
    rw [distSum, add_apply, distSum_univ κ x n, measure_univ]
    push_cast; rfl

instance isFiniteMeasure_distSum (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (n : ℕ) :
    IsFiniteMeasure (distSum κ x n) :=
  ⟨by rw [distSum_univ]; exact ENNReal.natCast_lt_top n⟩

/-- Cesàro average of the first `n + 1` step distributions. -/
noncomputable def cesaro (κ : Kernel X X) (x : X) (n : ℕ) : Measure X :=
  ((n + 1 : ℝ≥0∞)⁻¹) • distSum κ x (n + 1)

theorem isProbabilityMeasure_cesaro (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (n : ℕ) :
    IsProbabilityMeasure (cesaro κ x n) := by
  constructor
  rw [cesaro, smul_apply, distSum_univ, smul_eq_mul]
  push_cast
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

variable [TopologicalSpace X] [OpensMeasurableSpace X]

theorem integral_distSum (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (f : X →ᵇ ℝ) :
    ∀ n, ∫ y, f y ∂(distSum κ x n) = ∑ k ∈ range n, ∫ y, f y ∂(distIter κ x k)
  | 0 => by simp [distSum]
  | n + 1 => by
    have := isProbabilityMeasure_distIter κ x n
    rw [distSum, integral_add_measure (f.integrable _) (f.integrable _), integral_distSum κ x f n,
      Finset.sum_range_succ]

theorem integral_cesaro (κ : Kernel X X) [IsMarkovKernel κ] (x : X) (n : ℕ) (f : X →ᵇ ℝ) :
    ∫ y, f y ∂(cesaro κ x n) = (n + 1 : ℝ)⁻¹ * ∑ k ∈ range (n + 1), ∫ y, f y ∂(distIter κ x k) := by
  rw [cesaro, integral_smul_measure, integral_distSum, smul_eq_mul]
  congr 1
  rw [ENNReal.toReal_inv]
  norm_cast

/-- The **Markov operator** `Kf(x) = ∫ f dκ(x)` on bounded continuous functions. -/
noncomputable def markovOp (κ : Kernel X X) [IsMarkovKernel κ] (hκ : IsFeller κ) (f : X →ᵇ ℝ) :
    X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ∫ y, f y ∂(κ x)) (hκ f) ‖f‖
    fun x => f.norm_integral_le_norm (μ := κ x)

theorem integral_distIter_succ (κ : Kernel X X) [IsMarkovKernel κ] (hκ : IsFeller κ) (x : X)
    (k : ℕ) (f : X →ᵇ ℝ) :
    ∫ y, f y ∂(distIter κ x (k + 1)) = ∫ y, markovOp κ hκ f y ∂(distIter κ x k) := by
  have := isProbabilityMeasure_distIter κ x k
  rw [show distIter κ x (k + 1) = κ ∘ₘ distIter κ x k from rfl]
  rw [integral_comp_measure (f.integrable _)]
  rfl

/-- `∫ Kf dνₙ - ∫ f dνₙ → 0` along the Cesàro averages. -/
theorem tendsto_integral_markovOp_sub (κ : Kernel X X) [IsMarkovKernel κ] (hκ : IsFeller κ)
    (x : X) (f : X →ᵇ ℝ) :
    Tendsto (fun n => ∫ y, markovOp κ hκ f y ∂(cesaro κ x n) - ∫ y, f y ∂(cesaro κ x n))
      atTop (𝓝 0) := by
  set a : ℕ → ℝ := fun k => ∫ y, f y ∂(distIter κ x k)
  have ha : ∀ k, |a k| ≤ ‖f‖ := fun k => by
    have := isProbabilityMeasure_distIter κ x k
    simpa [a, Real.norm_eq_abs] using f.norm_integral_le_norm (μ := distIter κ x k)
  have heq : ∀ n, ∫ y, markovOp κ hκ f y ∂(cesaro κ x n) - ∫ y, f y ∂(cesaro κ x n) =
      (n + 1 : ℝ)⁻¹ * (a (n + 1) - a 0) := by
    intro n
    rw [integral_cesaro, integral_cesaro, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    simp_rw [← integral_distIter_succ κ hκ x]
    exact Finset.sum_range_sub a (n + 1)
  simp_rw [heq]
  have hb : ∀ n : ℕ, |(n + 1 : ℝ)⁻¹ * (a (n + 1) - a 0)| ≤ 2 * ‖f‖ * (n + 1 : ℝ)⁻¹ := by
    intro n
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    have : |a (n + 1) - a 0| ≤ 2 * ‖f‖ := by
      have := abs_sub (a (n + 1)) (a 0); linarith [ha (n + 1), ha 0]
    nlinarith [inv_pos.2 (by positivity : (0 : ℝ) < n + 1)]
  have hlim : Tendsto (fun n : ℕ => 2 * ‖f‖ * (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp
      (tendsto_add_atTop_nat 1)
    simpa using this.const_mul (2 * ‖f‖)
  exact squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hb n) hlim

variable [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

/-- **Existence of an invariant distribution** (Krylov–Bogolyubov; SL Thm 12.10):
a Feller Markov kernel on a nonempty compact metrizable space has an
invariant probability measure. -/
theorem exists_invariant_of_feller [CompactSpace X] [Nonempty X] (κ : Kernel X X)
    [IsMarkovKernel κ] (hκ : IsFeller κ) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ Kernel.Invariant κ μ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let u : ℕ → ProbabilityMeasure X := fun n =>
    ⟨cesaro κ x n, isProbabilityMeasure_cesaro κ x n⟩
  obtain ⟨ν, -, hν⟩ := isCompact_univ.exists_mapClusterPt (u := u) (f := atTop) (by simp)
  have hint : ∀ f : X →ᵇ ℝ, ∫ y, markovOp κ hκ f y ∂(ν : Measure X) = ∫ y, f y ∂(ν : Measure X) := by
    intro f
    rcases mapClusterPt_iff_ultrafilter.mp hν with ⟨U, hUl, hUν⟩
    have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hUν (markovOp κ hκ f)
    have h2 : Tendsto (fun n => ∫ y, markovOp κ hκ f y ∂(u n : Measure X)) U
        (𝓝 (∫ y, f y ∂(ν : Measure X))) := by
      have h3 := ((tendsto_integral_markovOp_sub κ hκ x f).mono_left hUl).add
        (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hUν f)
      simp only [zero_add] at h3
      exact h3.congr fun n => sub_add_cancel _ _
    exact tendsto_nhds_unique h1 h2
  refine ⟨ν, inferInstance, ?_⟩
  show κ ∘ₘ (ν : Measure X) = ν
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_comp_measure (f.integrable _)]
  exact hint f

end Econ
