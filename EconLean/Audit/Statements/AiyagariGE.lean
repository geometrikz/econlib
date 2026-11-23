/-
# Frozen statements: Aiyagari stationary general equilibrium

Headline statements of `Macro/HA/CDFirm.lean` and `Macro/HA/AiyagariGE.lean`.
Copied verbatim after the context-isolated adversarial review (record in
`Audit/REVIEW-aiyagari-ge.md`). Each statement is closed by the library
theorem, so this file stops compiling if a library statement is ever weakened.
-/
module

public import EconLean.Macro.HA.AiyagariGE

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ BoundedContinuousFunction MeasureTheory ProbabilityTheory

section Firm

variable (F : CDFirm)

theorem frozen_foc_capital {r : ℝ} (hr : -F.δ < r) : F.α * F.kOfR r ^ (F.α - 1) = r + F.δ :=
  F.foc_capital hr

theorem frozen_zero_profit {L r : ℝ} (hL : 0 < L) (hr : -F.δ < r) :
    (r + F.δ) * F.capDemand L r + F.wage r * L = F.output (F.capDemand L r) L :=
  F.zero_profit hL hr

theorem frozen_strictAntiOn_kOfR : StrictAntiOn F.kOfR (Ioi (-F.δ)) := F.strictAntiOn_kOfR

theorem frozen_exists_capDemand_ge {L : ℝ} (hL : 0 < L) (B : ℝ) {r₀ : ℝ} (hr₀ : -F.δ < r₀) :
    ∃ r, -F.δ < r ∧ r ≤ r₀ ∧ B ≤ F.capDemand L r :=
  F.exists_capDemand_ge hL B hr₀

end Firm

section Household

variable {Θ Z : Type*} [TopologicalSpace Θ] [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z]
  (M : ParamSavings Θ Z)

theorem frozen_le_policy (θ : Θ) (m : M.S) (hm : ∀ s : M.S × Z, (m : ℝ) ≤ M.h θ s.1 s.2)
    (hmono : ∀ z' (a b : M.S), (a : ℝ) ≤ b → M.h θ a z' ≤ M.h θ b z')
    (hgain : ∀ (s : M.S × Z) (y : M.S) (x : Z → M.S), (y : ℝ) < m →
      (∀ z', (x z' : ℝ) ≤ M.h θ y z') →
      M.u (M.h θ s.1 s.2 - y) - M.u (M.h θ s.1 s.2 - m) <
        M.β * ∑ z', M.Q s.2 z' * (M.u (M.h θ m z' - x z') - M.u (M.h θ y z' - x z')))
    {g : M.S × Z → M.S} (hg : ∀ s, (M.slice θ).toStochDynProg.policy s = {g s}) (s : M.S × Z) :
    (m : ℝ) ≤ g s :=
  M.le_policy θ m hm hmono hgain hg s

variable [MeasurableSpace Z] [BorelSpace Z]

theorem frozen_marg_isInvariant [DecidableEq Z] (g : M.S × Z → M.S) (hg : Measurable g)
    (μ : ProbabilityMeasure (M.S × Z)) (hμ : Kernel.Invariant (policyKernel M.Q g hg) μ) :
    IsInvariant M.Q (M.marg μ) :=
  M.marg_isInvariant g hg μ hμ

theorem frozen_integral_policy_eq (g : M.S × Z → M.S) (hg : Measurable g)
    (μ : ProbabilityMeasure (M.S × Z)) (hμ : Kernel.Invariant (policyKernel M.Q g hg) μ) :
    ∫ s, ((g s : M.S) : ℝ) ∂(μ : Measure (M.S × Z)) = ∫ s, M.assets s ∂(μ : Measure (M.S × Z)) :=
  M.integral_policy_eq g hg μ hμ

end Household

section GE

variable {Z : Type*} [Fintype Z] (E : AiyagariEconomy Z) [TopologicalSpace Z] [DiscreteTopology Z]
  [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]

theorem frozen_exists_stationary_equilibrium [DecidableEq Z]
    (hlo : E.kbar ≤ E.firm.capDemand E.L E.rlo)
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z), Kernel.Invariant (policyKernel E.Q g hg) μ ∧
        E.firm.capDemand E.L E.rhi ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z))) :
    ∃ r : Icc E.rlo E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.firm.capDemand E.L r ∧
      ∫ s, E.e s.2 ∂(π : Measure (E.household.S × Z)) = E.L ∧
      E.firm.α * ((∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) / E.L) ^
        (E.firm.α - 1) = r + E.firm.δ ∧
      E.firm.wage r = (1 - E.firm.α) *
        ((∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) / E.L) ^ E.firm.α ∧
      ∫ s, ((1 + (r : ℝ)) * (s.1 : ℝ) + E.firm.wage r * E.e s.2 - (g s : ℝ))
          ∂(π : Measure (E.household.S × Z)) +
        E.firm.δ * ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) =
        E.firm.output (∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) E.L :=
  E.exists_stationary_equilibrium hlo hhi

end GE

theorem frozen_sqrt_equilibrium :
    ∃ r : Icc AiyagariEconomy.sqrtEconomy.rlo AiyagariEconomy.sqrtEconomy.rhi,
    ∃ (g : AiyagariEconomy.sqrtEconomy.household.S × Fin 2 →
        AiyagariEconomy.sqrtEconomy.household.S)
      (hg : Measurable g) (π : ProbabilityMeasure (AiyagariEconomy.sqrtEconomy.household.S × Fin 2)),
      (∀ s, (AiyagariEconomy.sqrtEconomy.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel AiyagariEconomy.sqrtEconomy.Q g hg) π ∧
      ∫ s, AiyagariEconomy.sqrtEconomy.household.assets s
        ∂(π : Measure (AiyagariEconomy.sqrtEconomy.household.S × Fin 2)) =
        AiyagariEconomy.sqrtEconomy.firm.capDemand AiyagariEconomy.sqrtEconomy.L r ∧
      0 < ∫ s, AiyagariEconomy.sqrtEconomy.household.assets s
        ∂(π : Measure (AiyagariEconomy.sqrtEconomy.household.S × Fin 2)) :=
  AiyagariEconomy.sqrt_equilibrium

end Econ.Audit
