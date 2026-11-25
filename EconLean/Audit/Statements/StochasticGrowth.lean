/-
# Frozen statements: stochastic growth (invariant distribution of capital)

Headline statements of `Macro/DP/StochasticGrowth.lean`, copied verbatim after
the context-isolated adversarial review (record in
`Audit/REVIEW-stochastic-growth.md`). Each statement is closed by the library
theorem, so this file stops compiling if a library statement is ever weakened.
-/
module

public import EconLean.Macro.DP.StochasticGrowth

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ MeasureTheory ProbabilityTheory

theorem frozen_le_pow_real_of_chain {X : Type*} [MeasurableSpace X] {κ : Kernel X X} [IsMarkovKernel κ]
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n)) {p q : ℝ} (hq : 0 ≤ q)
    (h0 : ∀ x, p ≤ (κ x).real (A 0)) (hstep : ∀ n, ∀ y ∈ A n, q ≤ (κ y).real (A (n + 1))) :
    ∀ n x, p * q ^ n ≤ ((κ ^ (n + 1)) x).real (A n) :=
  le_pow_real_of_chain hAm hq h0 hstep

namespace LogCapitalFrozen

variable (P : LogCapital)

theorem frozen_sg_stationary_unique {π π' : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    [IsProbabilityMeasure π'] (hπ : Kernel.Invariant P.K π) (hπ' : Kernel.Invariant P.K π') :
    π' = π :=
  P.stationary_unique hπ hπ'

theorem frozen_sg_exists_unique_stationary :
    ∃ π : Measure (P.S × Fin 2), IsProbabilityMeasure π ∧ Kernel.Invariant P.K π ∧
      ∀ π' : Measure (P.S × Fin 2), IsProbabilityMeasure π' → Kernel.Invariant P.K π' → π' = π :=
  P.exists_unique_stationary

theorem frozen_sg_marginal_eq {π : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant P.K π) (z : Fin 2) :
    π.real (Prod.snd ⁻¹' {z}) = P.q z :=
  P.marginal_eq hπ z

theorem frozen_sg_integral_x {π : Measure (P.S × Fin 2)} [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant P.K π) :
    ∫ s, (s.1 : ℝ) ∂π = (P.q 0 * P.μ 0 + P.q 1 * P.μ 1) / (1 - P.α) :=
  P.integral_x hπ

end LogCapitalFrozen

section BrockMirman

open LogCapital

variable {α β : ℝ} {A q : Fin 2 → ℝ} {hα0 : 0 < α} {hα1 : α < 1}
  {hA : ∀ z, 0 < A z} {hA01 : A 0 ≤ A 1} {hq : ∀ z, 0 < q z} {hqs : q 0 + q 1 = 1}

theorem frozen_brockMirman_policy (hβ0 : 0 < β) (z : Fin 2) {k : ℝ} (hk : 0 < k) :
    (brockMirman α β A q hα0 hα1 hA hA01 hq hqs).μ z +
      (brockMirman α β A q hα0 hα1 hA hA01 hq hqs).α * Real.log k =
      Real.log (α * β * A z * k ^ α) :=
  brockMirman_policy hβ0 z hk

theorem frozen_brockMirman_mean_log_capital
    {π : Measure ((brockMirman α β A q hα0 hα1 hA hA01 hq hqs).S × Fin 2)}
    [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (brockMirman α β A q hα0 hα1 hA hA01 hq hqs).K π) :
    ∫ s, (s.1 : ℝ) ∂π =
      (Real.log (α * β) + (q 0 * Real.log (A 0) + q 1 * Real.log (A 1))) / (1 - α) :=
  brockMirman_mean_log_capital hπ

end BrockMirman

end Econ.Audit
