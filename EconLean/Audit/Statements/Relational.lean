/-
# Frozen statements: relational contracts (Levin 2003, perfect monitoring)

Headline statements of `Contracts/Relational`, copied after the adversarial review recorded in
`Audit/REVIEW-relational.md`. Each is closed by the library theorem, so if a library statement
is ever weakened this file stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Contracts.Relational

@[expose] public section

namespace Econ.Audit

open Econ

theorem frozen_stationary_selfEnforcing {E : Type*} {y c : E → ℝ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hc : ∀ e, 0 ≤ c e) {e : E} (hfeas : (1 - δ) * c e ≤ δ * (y e - c e))
    {u π : ℝ} (hu : 0 ≤ u) (hπ : 0 ≤ π) (hsum : u + π = y e - c e) :
    IsSelfEnforcing y c δ (stationaryRel c δ e u π) :=
  stationary_selfEnforcing hδ0 hδ1 hc hfeas hu hπ hsum

theorem frozen_selfEnforcing_dynamic {E : Type*} {y c : E → ℝ} {δ : ℝ} {K : RelContract E}
    (hK : IsSelfEnforcing y c δ K) (hc0 : ∃ e₀, c e₀ = 0) (t : ℕ) :
    c (K.e t) ≤ δ * (K.U (t + 1) + K.P (t + 1)) :=
  selfEnforcing_dynamic hK hc0 t

theorem frozen_levin_stationary_optimal {E : Type*} [Fintype E] {y c : E → ℝ} {δ : ℝ}
    {K : RelContract E} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : ∀ e, 0 ≤ c e)
    (hc0 : ∃ e₀, c e₀ = 0) (hK : IsSelfEnforcing y c δ K) :
    ∃ e' ∈ stationaryFeasible y c δ,
      (∀ e ∈ stationaryFeasible y c δ, y e - c e ≤ y e' - c e') ∧
      IsSelfEnforcing y c δ (stationaryRel c δ e' (y e' - c e') 0) ∧
      ∀ (K' : RelContract E), IsSelfEnforcing y c δ K' →
        ∀ t, (1 - δ) * (K'.U t + K'.P t) ≤ y e' - c e' :=
  levin_stationary_optimal hδ0 hδ1 hc hc0 hK

theorem frozen_constant_effort_iff {E : Type*} {y c : E → ℝ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hc : ∀ e, 0 ≤ c e) (hc0 : ∃ e₀, c e₀ = 0) (e : E) :
    (∃ K : RelContract E, IsSelfEnforcing y c δ K ∧ ∀ t, K.e t = e) ↔
      (1 - δ) * c e ≤ δ * (y e - c e) :=
  constant_effort_iff hδ0 hδ1 hc hc0 e

end Econ.Audit
