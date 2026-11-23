/-
# Frozen statements: Ramsey global convergence, stochastic plans, invariant
# distributions, stochastic concavity, stationary distributions (M8/M11, F10, F12)

These are the headline statements of the following files:
`Macro/Growth/RamseyGlobal.lean`, `Macro/DP/StochasticPlan.lean`,
`Macro/DP/InvariantMeasure.lean`, `Macro/DP/StochasticConcavity.lean`,
`Macro/DP/StationaryDist.lean` and `Macro/HA/StochSavings.lean`.

They were copied verbatim after the context-isolated adversarial review of
2026-11-23 (record in `Audit/REVIEW-ha-stochastic.md`). Each statement is closed
by the library theorem, so this file stops compiling if a library statement is
ever weakened. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Growth.RamseyGlobal
public import EconLean.Macro.HA.StochSavings

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ BoundedContinuousFunction MeasureTheory ProbabilityTheory

section RamseyGlobal

variable (M : RCKModel)

theorem frozen_exists_mgr (hI : M.Inada) :
    ∃ kstar : M.S, 0 < (kstar : ℝ) ∧ (kstar : ℝ) < M.kbar ∧ M.β * deriv M.f kstar = 1 :=
  RCKModel.exists_mgr hI

theorem frozen_global_convergence (hI : M.Inada) :
    ∃ g : M.S → M.S, (∀ k, M.toDynProg.policy k = {g k}) ∧
      ∃ kstar : M.S, 0 < (kstar : ℝ) ∧ (kstar : ℝ) < M.f kstar ∧
        M.β * deriv M.f kstar = 1 ∧
        (∀ k f' : ℝ, 0 ≤ k → HasDerivAt M.f f' k → M.β * f' = 1 → k = kstar) ∧
        g kstar = kstar ∧
        ∀ k₀ : M.S, 0 < (k₀ : ℝ) → (Monotone (planOf g k₀) ∨ Antitone (planOf g k₀)) ∧
          Tendsto (planOf g k₀) atTop (𝓝 kstar) :=
  RCKModel.global_convergence hI

theorem frozen_sqrtExample_inada : RCKModel.sqrtExample.Inada := RCKModel.sqrtExample_inada

end RamseyGlobal

section StochasticPlan

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] [DiscreteTopology Z]
  [Fintype Z] (P : StochDynProg X Z)

theorem frozen_tendsto_expectedPayoff {σ : List Z → X} {s : X × Z} (hσ : P.IsFeasible σ s) :
    Tendsto (fun n => P.payoffN n σ s) atTop (𝓝 (P.expectedPayoff σ s)) :=
  P.tendsto_expectedPayoff hσ

theorem frozen_isGreatest_expectedPayoff (s : X × Z) :
    IsGreatest {w | ∃ σ, P.IsFeasible σ s ∧ P.expectedPayoff σ s = w} (P.value s) :=
  P.isGreatest_expectedPayoff s

theorem frozen_expectedPayoff_policyPlan {g : X × Z → X} (hg : ∀ s, g s ∈ P.policy s)
    (s : X × Z) : P.expectedPayoff (StochDynProg.policyPlan g s) s = P.value s :=
  P.expectedPayoff_policyPlan hg s

theorem frozen_policy_of_optimal {σ : List Z → X} {s : X × Z} (hσ : P.IsFeasible σ s)
    (hopt : P.expectedPayoff σ s = P.value s) : σ [] ∈ P.policy s :=
  P.policy_of_optimal hσ hopt

end StochasticPlan

section Feller

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]

theorem frozen_exists_invariant_of_feller [CompactSpace X] [Nonempty X] (κ : Kernel X X)
    [IsMarkovKernel κ] (hκ : IsFeller κ) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ Kernel.Invariant κ μ :=
  exists_invariant_of_feller κ hκ

end Feller

section StochConcavity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
  {Z : Type*} [TopologicalSpace Z] [DiscreteTopology Z] [Fintype Z]

theorem frozen_stoch_value_concave (hS : Convex ℝ S) (P : StochDynProg S Z) (hΓ : P.ConvexTech)
    (hF : P.ConcaveRet) (z : Z) : ConcaveFn fun x : S => P.value (x, z) :=
  P.value_concave hS hΓ hF z

theorem frozen_stoch_exists_continuous_policy (hS : Convex ℝ S) (P : StochDynProg S Z)
    (hΓ : P.ConvexTech) (hF : P.ConcaveRet) :
    ∃ g : S × Z → S, Continuous g ∧ ∀ s, P.policy s = {g s} :=
  P.exists_continuous_policy hS hΓ hF

end StochConcavity

section Stationary

variable {X Z : Type*} [MeasurableSpace X] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z]

theorem frozen_isMarkovKernel_policyKernel {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    (hQ1 : ∀ z, ∑ z', Q z z' = 1) (g : X × Z → X) (hg : Measurable g) :
    IsMarkovKernel (policyKernel Q g hg) :=
  isMarkovKernel_policyKernel hQ0 hQ1 g hg

variable [TopologicalSpace X] [TopologicalSpace Z]
  [OpensMeasurableSpace (X × Z)] [MeasurableSingletonClass (X × Z)]

theorem frozen_integral_policyKernel {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    (g : X × Z → X) (hg : Measurable g) (s : X × Z) (f : X × Z →ᵇ ℝ) :
    ∫ y, f y ∂(policyKernel Q g hg s) = ∑ z', Q s.2 z' * f (g s, z') :=
  integral_policyKernel hQ0 g hg s f

theorem frozen_isFeller_policyKernel [DiscreteTopology Z] {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    {g : X × Z → X} (hgc : Continuous g) (hg : Measurable g) :
    IsFeller (policyKernel Q g hg) :=
  isFeller_policyKernel hQ0 hgc hg

end Stationary

section StationaryDP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Set E} {Z : Type*} [TopologicalSpace Z] [DiscreteTopology Z] [Fintype Z]
  [MeasurableSpace Z] [BorelSpace Z]

theorem frozen_stoch_exists_stationary [MeasurableSingletonClass Z] (hS : Convex ℝ S) (hSc : IsCompact S) [Nonempty S]
    [Nonempty Z] (P : StochDynProg S Z) (hΓ : P.ConvexTech) (hF : P.ConcaveRet) :
    ∃ g : S × Z → S, Continuous g ∧ (∀ s, P.policy s = {g s}) ∧
      ∃ (hg : Measurable g) (μ : Measure (S × Z)), IsProbabilityMeasure μ ∧
        Kernel.Invariant (policyKernel P.Q g hg) μ :=
  P.exists_stationary hS hSc hΓ hF

theorem frozen_stochSavings_exists_stationary [Nonempty Z] (M : StochSavings Z) :
    ∃ g : M.S × Z → M.S, Continuous g ∧ (∀ s, M.toStochDynProg.policy s = {g s}) ∧
      ∃ (hg : Measurable g) (μ : Measure (M.S × Z)), IsProbabilityMeasure μ ∧
        Kernel.Invariant (policyKernel M.Q g hg) μ :=
  M.exists_stationary

end StationaryDP

end Econ.Audit
