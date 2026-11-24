/-
# Frozen statements: uniqueness of the stationary distribution

Headline statements of `Macro/DP/MonotoneMixing.lean` and
`Macro/HA/StationaryUnique.lean`, copied verbatim after the context-isolated
adversarial review (record in `Audit/REVIEW-stationary-unique.md`). Each
statement is closed by the library theorem, so this file stops compiling if a
library statement is ever weakened.
-/
module

public import EconLean.Macro.HA.StationaryUnique

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ MeasureTheory ProbabilityTheory

theorem frozen_integral_le_of_upper {X : Type*} [MeasurableSpace X] [Preorder X] {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ∀ U, IsUpperSet U → MeasurableSet U → μ.real U ≤ ν.real U)
    {f : X → ℝ} (hf : Monotone f) (hfm : Measurable f) {m l : ℝ}
    (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ m + l) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν :=
  integral_le_of_upper hμν hf hfm hlo hhi

theorem frozen_abs_integral_sub_le_of_upper {X : Type*} [MeasurableSpace X] [Preorder X] {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {D : ℝ}
    (hD : ∀ U, IsUpperSet U → MeasurableSet U → |μ.real U - ν.real U| ≤ D)
    {f : X → ℝ} (hf : Monotone f) (hfm : Measurable f) {m l : ℝ} (hl : 0 ≤ l)
    (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ m + l) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ l * D :=
  abs_integral_sub_le_of_upper hD hf hfm hl hlo hhi

theorem frozen_isMonotoneKernel_pow {X : Type*} [MeasurableSpace X] [Preorder X] {κ : Kernel X X} [IsMarkovKernel κ]
    (hκ : IsMonotoneKernel κ) (n : ℕ) : IsMonotoneKernel (κ ^ n) :=
  hκ.pow n

theorem frozen_unique_invariant_of_splitting {X : Type*} [MeasurableSpace X] [Preorder X] {κ : Kernel X X} [IsMarkovKernel κ]
    (hmono : IsMonotoneKernel κ)
    (hgen : ‹MeasurableSpace X› =
      MeasurableSpace.generateFrom {U | IsUpperSet U ∧ MeasurableSet U})
    {N : ℕ} {c : X} {δ : ℝ} (hδ : 0 < δ) (hIic : MeasurableSet (Iic c))
    (hlow : ∀ x, δ ≤ ((κ ^ N) x).real (Iic c)) (hup : ∀ x, δ ≤ ((κ ^ N) x).real (Ici c))
    {π π' : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π') : π' = π :=
  unique_invariant_of_splitting hmono hgen hδ hIic hlow hup hπ hπ'

theorem frozen_generateFrom_upperSets_prod {S Z : Type*} [LinearOrder S] [TopologicalSpace S]
    [OrderTopology S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    [LinearOrder Z] [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] :
    (inferInstance : MeasurableSpace (S × Z)) =
      MeasurableSpace.generateFrom {U | IsUpperSet U ∧ MeasurableSet U} :=
  generateFrom_upperSets_prod

theorem frozen_isMonotoneKernel_policyKernel {X Z : Type*} [MeasurableSpace X] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] [Preorder X] [Preorder Z] {Q : Z → Z → ℝ}
    (hQ0 : ∀ z z', 0 ≤ Q z z') (hiid : ∀ z₁ z₂ z', Q z₁ z' = Q z₂ z')
    {g : X × Z → X} (hg : Measurable g) (hmono : Monotone g) :
    IsMonotoneKernel (policyKernel Q g hg) :=
  isMonotoneKernel_policyKernel hQ0 hiid hg hmono

section Savings

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] {M : StochSavings Z}

theorem frozen_su_policy_monotone [Preorder Z] {g : M.S × Z → M.S}
    (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hh : ∀ (a a' : M.S) (z z' : Z), (a : ℝ) ≤ a' → z ≤ z' → M.h a z ≤ M.h a' z') :
    Monotone g :=
  StochSavings.policy_monotone hg hiid hh

theorem frozen_unique_stationary_of_splitting [LinearOrder Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {g : M.S × Z → M.S}
    (hpol : ∀ s, M.toStochDynProg.policy s = {g s}) (hg : Measurable g)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hh : ∀ (a a' : M.S) (z z' : Z), (a : ℝ) ≤ a' → z ≤ z' → M.h a z ≤ M.h a' z')
    {N : ℕ} {c : M.S × Z} {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x, δ ≤ ((policyKernel M.Q g hg ^ N) x).real (Iic c))
    (hup : ∀ x, δ ≤ ((policyKernel M.Q g hg ^ N) x).real (Ici c))
    {π π' : Measure (M.S × Z)} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant (policyKernel M.Q g hg) π)
    (hπ' : Kernel.Invariant (policyKernel M.Q g hg) π') : π' = π :=
  StochSavings.unique_stationary_of_splitting hpol hg hiid hh hδ hlow hup hπ hπ'

end Savings

open AiyagariEconomy in
theorem frozen_slack_saving_floor (r : Icc slackEconomy.rlo slackEconomy.rhi)
    (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S)
    (hg : ∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s})
    (a : slackEconomy.household.S) : CDFirm.tenth.kOfR (-1 / 20) / 100 ≤ g (a, 1) :=
  slack_saving_floor r g hg a

open AiyagariEconomy in
theorem frozen_slack_stationary_unique (r : Icc slackEconomy.rlo slackEconomy.rhi)
    (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S) (hg : Measurable g)
    (hpol : ∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s})
    (π π' : ProbabilityMeasure (slackEconomy.household.S × Fin 2))
    (hπ : Kernel.Invariant (policyKernel slackEconomy.Q g hg) π)
    (hπ' : Kernel.Invariant (policyKernel slackEconomy.Q g hg) π') : π' = π :=
  slack_stationary_unique r g hg hpol π π' hπ hπ'

open AiyagariEconomy in
theorem frozen_slack_equilibrium_unique :
    ∃ r : Icc slackEconomy.rlo slackEconomy.rhi,
    ∃ (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (slackEconomy.household.S × Fin 2)),
      (∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel slackEconomy.Q g hg) π ∧
      (∀ π' : ProbabilityMeasure (slackEconomy.household.S × Fin 2),
        Kernel.Invariant (policyKernel slackEconomy.Q g hg) π' → π' = π) ∧
      ∫ s, slackEconomy.household.assets s ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.firm.capDemand slackEconomy.L r ∧
      (∀ s, (g s : ℝ) < slackEconomy.kbar) ∧
      (π : Measure (slackEconomy.household.S × Fin 2))
        {s | 9 / 10 * slackEconomy.kbar < (s.1 : ℝ)} = 0 ∧
      -slackEconomy.firm.δ < (r : ℝ) ∧ (r : ℝ) < 0 :=
  slack_equilibrium_unique

end Econ.Audit
