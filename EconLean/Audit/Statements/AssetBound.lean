/-
# Frozen statements: the endogenous asset bound

Headline statements of `Macro/HA/AssetBound.lean`. Copied verbatim after the
context-isolated adversarial review (record in `Audit/REVIEW-asset-bound.md`).
Each statement is closed by the library theorem, so this file stops compiling
if a library statement is ever weakened.
-/
module

public import EconLean.Macro.HA.AssetBound

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ MeasureTheory ProbabilityTheory

section Household

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] {M : StochSavings Z}
  {g : M.S × Z → M.S}

theorem frozen_policy_mono (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {s₁ s₂ : M.S × Z}
    (hQ : ∀ z', M.Q s₁.2 z' = M.Q s₂.2 z') (hh : M.h s₁.1 s₁.2 ≤ M.h s₂.1 s₂.2) :
    (g s₁ : ℝ) ≤ g s₂ :=
  StochSavings.policy_mono hg hQ hh

theorem frozen_cons_mono (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {s₁ s₂ : M.S × Z}
    (hQ : ∀ z', M.Q s₁.2 z' = M.Q s₂.2 z') (hh : M.h s₁.1 s₁.2 ≤ M.h s₂.1 s₂.2) :
    M.cons g s₁ ≤ M.cons g s₂ :=
  StochSavings.cons_mono hg hQ hh

theorem frozen_policy_lt_self (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A)
    (s : M.S × Z) (hs : A ≤ s.1) : (g s : ℝ) < s.1 :=
  StochSavings.policy_lt_self hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC s hs

theorem frozen_policy_lt_kbar (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A) (hAk : A < M.kbar)
    (s : M.S × Z) : (g s : ℝ) < M.kbar :=
  StochSavings.policy_lt_kbar hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC hAk s

theorem frozen_measure_gt_eq_zero [MeasurableSpace Z] [BorelSpace Z]
    (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A)
    (hgm : Measurable g) (μ : Measure (M.S × Z)) [IsProbabilityMeasure μ]
    (hμ : Kernel.Invariant (policyKernel M.Q g hgm) μ) : μ {s | A < (s.1 : ℝ)} = 0 :=
  StochSavings.measure_gt_eq_zero hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC hgm μ hμ

end Household

theorem frozen_sqrt_inada (K ε : ℝ) (hε : 0 < ε) :
    ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < Real.sqrt d - Real.sqrt 0 :=
  sqrt_inada K ε hε

theorem frozen_sqrt_eulerGap {β R y c : ℝ} (hβ : 0 < β) (hR : 0 < R) (hβR : β * R < 1)
    (hy : 0 ≤ y) (hc : y < (1 - (β * R) ^ 2) * c) : EulerGap Real.sqrt β R y c :=
  sqrt_eulerGap hβ hR hβR hy hc

theorem frozen_riskyHousehold_assetBound :
    ∃ g : StochSavings.riskyHousehold.S × Fin 2 → StochSavings.riskyHousehold.S,
      Continuous g ∧ (∀ s, StochSavings.riskyHousehold.toStochDynProg.policy s = {g s}) ∧
      (∀ s, (15 : ℝ) ≤ s.1 → (g s : ℝ) < s.1) ∧ (∀ s, (g s : ℝ) < 20) ∧
      ∃ (hg : Measurable g) (μ : Measure (StochSavings.riskyHousehold.S × Fin 2)),
        IsProbabilityMeasure μ ∧ Kernel.Invariant (policyKernel (fun _ _ => 1 / 2) g hg) μ ∧
        ∀ ν : Measure (StochSavings.riskyHousehold.S × Fin 2), IsProbabilityMeasure ν →
          Kernel.Invariant (policyKernel (fun _ _ => 1 / 2) g hg) ν → ν {s | (15 : ℝ) < s.1} = 0 :=
  StochSavings.riskyHousehold_assetBound

theorem frozen_risky_cap_slack :
    ∃ g : AiyagariEconomy.riskyEconomy.household.S × Fin 2 →
        AiyagariEconomy.riskyEconomy.household.S, Continuous g ∧
      (∀ s, (AiyagariEconomy.riskyEconomy.household.slice
        ⟨1 / 10, le_rfl, AiyagariEconomy.riskyEconomy.rlo_le⟩).toStochDynProg.policy s = {g s}) ∧
      (∀ s, (40 : ℝ) ≤ s.1 → (g s : ℝ) < s.1) ∧ (∀ s, (g s : ℝ) < 50) ∧
      ∃ (hg : Measurable g) (μ : Measure (AiyagariEconomy.riskyEconomy.household.S × Fin 2)),
        IsProbabilityMeasure μ ∧
        Kernel.Invariant (policyKernel AiyagariEconomy.riskyEconomy.Q g hg) μ ∧
        ∀ ν : Measure (AiyagariEconomy.riskyEconomy.household.S × Fin 2), IsProbabilityMeasure ν →
          Kernel.Invariant (policyKernel AiyagariEconomy.riskyEconomy.Q g hg) ν →
          ν {s | (40 : ℝ) < s.1} = 0 :=
  AiyagariEconomy.risky_cap_slack

end Econ.Audit
