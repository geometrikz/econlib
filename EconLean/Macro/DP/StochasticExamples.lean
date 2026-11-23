/-
# Non-vacuity witnesses for stochastic DP and finite Markov chains

* A stochastic dynamic program meeting SL Assumptions 9.4–9.5 (finite shocks):
  `X = [0, 1]`, two shock states `z ∈ {0, 1}` switching with probability `1/2`,
  any next state feasible, return `x z - y²`, `β = 1/2`.
* Doeblin's condition holds for that transition matrix (`ε = 1/2`), so the
  theorem gives a unique invariant distribution.
-/
module

public import EconLean.Macro.DP.Stochastic
public import EconLean.Macro.DP.MarkovChain

@[expose] public section

namespace Econ

namespace StochExample

open Set Matrix BoundedContinuousFunction

/-- The i.i.d. fair-coin transition matrix on two states. -/
noncomputable def Q : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

theorem isStochastic_Q : IsStochastic Q :=
  ⟨fun _ _ => by norm_num [Q], fun _ => by simp [Q]⟩

/-- A stochastic DP satisfying all assumptions. -/
noncomputable def P : StochDynProg (Icc (0 : ℝ) 1) (Fin 2) where
  Γ := fun _ => univ
  F := fun s y => (s.1 : ℝ) * ((s.2 : ℕ) : ℝ) - (y : ℝ) ^ 2
  Q := Q
  β := 1 / 2
  Q_nonneg := isStochastic_Q.1
  Q_sum := isStochastic_Q.2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => univ_nonempty
  Γ_compact := fun _ => isCompact_univ
  Γ_continuous := ⟨UpperHemicontinuous.const, LowerHemicontinuous.const⟩
  F_continuous := by
    unfold Function.uncurry
    have h : Continuous fun z : Fin 2 => ((z : ℕ) : ℝ) := continuous_of_discreteTopology
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (h.comp (continuous_snd.comp continuous_fst))).sub
      ((continuous_subtype_val.comp continuous_snd).pow 2)
  F_bounded := ⟨2, fun s y _ => by
    obtain ⟨hx0, hx1⟩ := s.1.2
    obtain ⟨hy0, hy1⟩ := y.2
    have hz0 : (0 : ℝ) ≤ ((s.2 : ℕ) : ℝ) := by positivity
    have hz1 : ((s.2 : ℕ) : ℝ) ≤ 1 := by
      have := s.2.isLt; norm_cast; omega
    rw [abs_le]; constructor <;> nlinarith⟩

/-- SL Thm 9.6 applies to the example. -/
example : ∃! v : (Icc (0 : ℝ) 1 × Fin 2) →ᵇ ℝ, ∀ s,
    IsGreatest ((fun y => P.F s y + P.β * ∑ z', P.Q s.2 z' * v (y, z')) '' P.Γ s) (v s) :=
  ⟨P.value, P.bellman_equation, fun w hw => P.value_unique w hw⟩

/-- Doeblin applies to the fair-coin chain: a unique invariant distribution. -/
example : ∃ π : Fin 2 → ℝ, IsInvariant Q π ∧ (∀ π', IsInvariant Q π' → π' = π) ∧
    ∀ μ ∈ Distributions (Fin 2), ∀ n : ℕ,
    l1Dist (μ ᵥ* (Q ^ n)) π ≤ 2 * (1 - Fintype.card (Fin 2) * (1 / 2)) ^ n :=
  doeblin isStochastic_Q (by norm_num) (fun _ _ => le_refl _)

end StochExample

end Econ
