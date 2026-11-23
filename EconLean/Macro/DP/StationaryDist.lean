/-
# Stationary distributions of optimally controlled Markov processes

Stokey–Lucas (SL) §9.6 and Thm 12.10, for finitely many shocks.

Take a policy function `g(x, z)` and a shock transition matrix `Q`. They
generate a Markov process on `(x, z)`: tomorrow's state is `x' = g(x, z)`, and
the shock `z'` is drawn from `Q(z, ·)`. Its transition kernel is

  `κ((x, z), ·) = Σ_{z'} Q(z, z') δ_{(g(x, z), z')}`.

If `g` is continuous, `κ` is Feller, so on a compact state space it has an
invariant distribution (`exists_invariant_of_feller`). Combined with the
continuous-policy theorem (`StochDynProg.exists_continuous_policy`), every
concave stochastic DP on a compact convex state space has a stationary
distribution of `(x, z)` under its optimal policy (SL Thm 12.10 applied to SL
§9.6). This is existence only: if some state is absorbing (`g(x₀, z) = x₀` for
every `z`), the point mass there is already invariant. Uniqueness and global stability need extra conditions (SL Thms
12.12–12.13, Hopenhayn–Prescott), and they are not formalised here.
-/
module

public import EconLean.Macro.DP.InvariantMeasure
public import EconLean.Macro.DP.StochasticConcavity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction Finset
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z]

theorem measurable_shock (Q : Z → Z → ℝ) (z' : Z) :
    Measurable (Function.uncurry fun (s : X × Z) (_ : X × Z) => ENNReal.ofReal (Q s.2 z')) :=
  (ENNReal.measurable_ofReal.comp ((measurable_of_countable fun z => Q z z').comp
    measurable_snd)).comp measurable_fst

/-- The transition kernel of `(x, z)` under the policy `g`:
`κ((x, z), ·) = Σ_{z'} Q(z, z') δ_{(g(x, z), z')}`. -/
noncomputable def policyKernel (Q : Z → Z → ℝ) (g : X × Z → X) (hg : Measurable g) :
    Kernel (X × Z) (X × Z) :=
  ∑ z', Kernel.withDensity (Kernel.deterministic (fun s => (g s, z')) (hg.prodMk measurable_const))
    fun s _ => ENNReal.ofReal (Q s.2 z')

theorem policyKernel_apply (Q : Z → Z → ℝ) (g : X × Z → X) (hg : Measurable g) (s : X × Z) :
    policyKernel Q g hg s = ∑ z', ENNReal.ofReal (Q s.2 z') • Measure.dirac (g s, z') := by
  simp only [policyKernel, sum_apply]
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [Kernel.withDensity_apply _ (measurable_shock Q z'), Kernel.deterministic_apply,
    withDensity_const]

theorem isMarkovKernel_policyKernel {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) (g : X × Z → X) (hg : Measurable g) :
    IsMarkovKernel (policyKernel Q g hg) := by
  refine ⟨fun s => ⟨?_⟩⟩
  rw [policyKernel_apply, sum_apply]
  simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z' _ => hQ0 _ _, hQ1, ENNReal.ofReal_one]

variable [TopologicalSpace X] [TopologicalSpace Z] [DiscreteTopology Z]
  [OpensMeasurableSpace (X × Z)] [MeasurableSingletonClass (X × Z)]

omit [DiscreteTopology Z] in
theorem integral_policyKernel {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    (g : X × Z → X) (hg : Measurable g) (s : X × Z) (f : X × Z →ᵇ ℝ) :
    ∫ y, f y ∂(policyKernel Q g hg s) = ∑ z', Q s.2 z' * f (g s, z') := by
  rw [policyKernel_apply, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun z' _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hQ0 _ _), smul_eq_mul]
  · intro z' _
    exact (f.integrable _).smul_measure ENNReal.ofReal_ne_top

/-- **The policy kernel is Feller** when the policy is continuous. -/
theorem isFeller_policyKernel {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    {g : X × Z → X} (hgc : Continuous g) (hg : Measurable g) :
    IsFeller (policyKernel Q g hg) := by
  intro f
  simp_rw [integral_policyKernel hQ0 g hg]
  exact continuous_finsetSum _ fun z' _ =>
    ((continuous_of_discreteTopology (f := fun z => Q z z')).comp continuous_snd).mul
      (f.continuous.comp (hgc.prodMk continuous_const))

namespace StochDynProg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Set E} [BorelSpace Z]

/-- **Existence of a stationary distribution under the optimal policy** (SL §9.6
with Thm 12.10). Suppose the stochastic DP has a compact convex nonempty state
space, convex technology, and a concave return that is strictly concave in the
choice. Then the optimal policy is a continuous function `g`, and the Markov
process `x' = g(x, z)`, `z' ~ Q(z, ·)` has an invariant probability
distribution on `S × Z`. -/
theorem exists_stationary (hS : Convex ℝ S) (hSc : IsCompact S) [Nonempty S] [Nonempty Z]
    (P : StochDynProg S Z) (hΓ : P.ConvexTech) (hF : P.ConcaveRet) :
    ∃ g : S × Z → S, Continuous g ∧ (∀ s, P.policy s = {g s}) ∧
      ∃ (hg : Measurable g) (μ : Measure (S × Z)), IsProbabilityMeasure μ ∧
        Kernel.Invariant (policyKernel P.Q g hg) μ := by
  obtain ⟨g, hgc, hsing⟩ := P.exists_continuous_policy hS hΓ hF
  have : CompactSpace S := isCompact_iff_compactSpace.1 hSc
  have hgm : Measurable g := hgc.measurable
  have := isMarkovKernel_policyKernel P.Q_nonneg P.Q_sum g hgm
  obtain ⟨μ, hμ, hinv⟩ := exists_invariant_of_feller (policyKernel P.Q g hgm)
    (isFeller_policyKernel P.Q_nonneg hgc hgm)
  exact ⟨g, hgc, hsing, hgm, μ, hμ, hinv⟩

end StochDynProg

end Econ
