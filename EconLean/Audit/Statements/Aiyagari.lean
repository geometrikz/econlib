/-
# Frozen statements: Doeblin, parametric invariant distributions, Aiyagari

Headline statements of `Macro/DP/Doeblin.lean`, `Macro/DP/ParamInvariant.lean`,
`Macro/HA/Aiyagari.lean` and the `N`-step `doeblin_pow` in
`Macro/DP/MarkovChain.lean`.

Copied verbatim after the context-isolated adversarial review (record in
`Audit/REVIEW-aiyagari.md`). Each statement is closed by the library theorem,
so this file stops compiling if a library statement is ever weakened. Do not
edit a statement here without a new review.
-/
module

public import EconLean.Macro.HA.Aiyagari
public import EconLean.Macro.DP.MarkovChain

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ BoundedContinuousFunction MeasureTheory ProbabilityTheory Matrix

section Doeblin

variable {X : Type*} [MeasurableSpace X]

theorem frozen_doeblin_convergence {K : Kernel X X} [IsMarkovKernel K] {φ : Measure X}
    [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ K x A)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    |(iterComp K μ n).real A - π.real A| ≤ (1 - ε) ^ n :=
  doeblin_convergence hε0 hε1 hmin hπ μ n hA

theorem frozen_doeblin_unique {K : Kernel X X} [IsMarkovKernel K] {φ : Measure X}
    [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ K x A)
    {π π' : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant K π) (hπ' : Kernel.Invariant K π') : π' = π :=
  doeblin_unique hε0 hε1 hmin hπ hπ'

theorem frozen_unique_invariant_of_pow {κ : Kernel X X} [IsMarkovKernel κ] {N : ℕ} {φ : Measure X}
    [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ (κ ^ N) x A)
    {π π' : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π') : π' = π :=
  unique_invariant_of_pow hε0 hε1 hmin hπ hπ'

theorem frozen_doeblin_convergence_pow {κ : Kernel X X} [IsMarkovKernel κ] {N : ℕ}
    {φ : Measure X} [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ (κ ^ N) x A)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Kernel.Invariant κ π)
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    |(iterComp κ μ n).real A - π.real A| ≤ (1 - ε) ^ (n / N) :=
  doeblin_convergence_pow hε0 hε1 hmin hπ μ n hA

end Doeblin

section FiniteDoeblin

variable {Z : Type*} [Fintype Z]

theorem frozen_doeblin_pow [Nonempty Z] [DecidableEq Z] {Q : Matrix Z Z ℝ} (hQ : IsStochastic Q)
    {N : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε : ∀ z z', ε ≤ (Q ^ N) z z') :
    ∃ π, IsInvariant Q π ∧ (∀ π', IsInvariant Q π' → π' = π) ∧ ∀ μ ∈ Distributions Z, ∀ n : ℕ,
      l1Dist (μ ᵥ* (Q ^ n)) π ≤ 2 * (1 - Fintype.card Z * ε) ^ (n / N) :=
  doeblin_pow hQ hε0 hε

end FiniteDoeblin

section ParamInvariant

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [CompactSpace X]
  {Θ : Type*} [TopologicalSpace Θ]

omit [T2Space X] in
theorem frozen_isClosed_invariant_graph (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ) :
    IsClosed {p : Θ × ProbabilityMeasure X | Kernel.Invariant (κ p.1) p.2} :=
  isClosed_invariant_graph κ hκ

theorem frozen_tendsto_invariant_of_unique (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ) (θ₀ : Θ)
    (huniq : ∀ μ ν : ProbabilityMeasure X, Kernel.Invariant (κ θ₀) μ →
      Kernel.Invariant (κ θ₀) ν → μ = ν)
    (π : Θ → ProbabilityMeasure X) (hπ : ∀ θ, Kernel.Invariant (κ θ) (π θ)) :
    Tendsto π (𝓝 θ₀) (𝓝 (π θ₀)) :=
  tendsto_invariant_of_unique κ hκ θ₀ huniq π hπ

theorem frozen_continuous_integral_invariant (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ)
    (huniq : ∀ θ, ∀ μ ν : ProbabilityMeasure X, Kernel.Invariant (κ θ) μ →
      Kernel.Invariant (κ θ) ν → μ = ν)
    (π : Θ → ProbabilityMeasure X) (hπ : ∀ θ, Kernel.Invariant (κ θ) (π θ)) (f : X →ᵇ ℝ) :
    Continuous fun θ => ∫ x, f x ∂(π θ : Measure X) :=
  continuous_integral_invariant κ hκ huniq π hπ f

end ParamInvariant

section Aiyagari

variable {Θ Z : Type*} [TopologicalSpace Θ] [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z]
  (M : ParamSavings Θ Z) [CompactSpace Θ] [T2Space Θ]

theorem frozen_value_slice (θ : Θ) (k : M.S) (z : Z) :
    M.aug.value ((θ, k), z) = (M.slice θ).toStochDynProg.value (k, z) :=
  M.value_slice θ k z

theorem frozen_exists_joint_policy :
    ∃ g : Θ → M.S × Z → M.S, Continuous (fun p : (Θ × M.S) × Z => g p.1.1 (p.1.2, p.2)) ∧
      ∀ θ s, (M.slice θ).toStochDynProg.policy s = {g θ s} :=
  M.exists_joint_policy

theorem frozen_continuous_aggregate [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]
    (huniq : ∀ θ, M.UniqueStationary θ) :
    ∃ (g : Θ → M.S × Z → M.S) (hgm : ∀ θ, Measurable (g θ)) (π : Θ → ProbabilityMeasure (M.S × Z)),
      Continuous (fun p : (Θ × M.S) × Z => g p.1.1 (p.1.2, p.2)) ∧
      (∀ θ s, (M.slice θ).toStochDynProg.policy s = {g θ s}) ∧
      (∀ θ, Kernel.Invariant (policyKernel M.Q (g θ) (hgm θ)) (π θ)) ∧
      Continuous π ∧ Continuous fun θ => ∫ s, M.assets s ∂(π θ : Measure (M.S × Z)) :=
  M.continuous_aggregate huniq

end Aiyagari

theorem frozen_exists_asset_market_clearing {Z : Type*} [Fintype Z] [TopologicalSpace Z]
    [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z] {rlo rhi : ℝ}
    (hr : rlo ≤ rhi) (M : ParamSavings (Icc rlo rhi) Z)
    (Kd : ℝ → ℝ) (hKd : ContinuousOn Kd (Icc rlo rhi))
    (hlo : M.kbar ≤ Kd rlo)
    (hhi : ∀ (g : M.S × Z → M.S) (hg : Measurable g),
      (∀ s, (M.slice ⟨rhi, hr, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (M.S × Z), Kernel.Invariant (policyKernel M.Q g hg) μ ∧
        Kd rhi ≤ ∫ s, M.assets s ∂(μ : Measure (M.S × Z))) :
    ∃ r : Icc rlo rhi, ∃ (g : M.S × Z → M.S) (hg : Measurable g) (π : ProbabilityMeasure (M.S × Z)),
      (∀ s, (M.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel M.Q g hg) π ∧
      ∫ s, M.assets s ∂(π : Measure (M.S × Z)) = Kd r :=
  ParamSavings.exists_asset_market_clearing hr M Kd hKd hlo hhi

theorem frozen_noReturn_uniqueStationary (θ : Icc (0 : ℝ) 1) :
    ParamSavings.noReturn.UniqueStationary θ :=
  ParamSavings.noReturn_uniqueStationary θ

end Econ.Audit
