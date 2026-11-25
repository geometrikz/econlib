/-
# Frozen statements: stochastic Brock–Mirman optimality

Headline statements of `Macro/DP/StochasticBrockMirman.lean`, copied verbatim
after the context-isolated adversarial review (record in
`Audit/REVIEW-stochastic-brock-mirman.md`). Each statement is closed by the
library theorem, so this file stops compiling if a library statement is ever
weakened.
-/
module

public import EconLean.Macro.DP.StochasticBrockMirman

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ Real Finset StochBrockMirman StochBrockMirman.Params

namespace StochBrockMirmanFrozen

variable {Z : Type*} [Fintype Z] (P : Params Z)

theorem frozen_sbm_bellman_eq {s : ℝ × Z} (hk : 0 < s.1) :
    P.F s (P.g s) + P.β * ∑ z', P.q z' * P.V (P.g s, z') = P.V s :=
  P.bellman_eq hk

theorem frozen_sbm_bellman_le {s : ℝ × Z} (hk : 0 < s.1) {k' : ℝ} (hk'0 : 0 < k') (hk'1 : k' < P.y s) :
    P.F s k' + P.β * ∑ z', P.q z' * P.V (k', z') ≤ P.V s :=
  P.bellman_le hk hk'0 hk'1

theorem frozen_stochastic_brockMirman {k₀ : ℝ} (hk₀ : 0 < k₀) (z₀ : Z) :
    P.Feasible (fun h => policyPlan P.g h (k₀, z₀)) (k₀, z₀) ∧
    Tendsto (fun n => P.J n (fun h => policyPlan P.g h (k₀, z₀)) (k₀, z₀)) atTop
      (𝓝 (P.V (k₀, z₀))) ∧
    ∀ σ : List Z → ℝ, P.Feasible σ (k₀, z₀) → ∀ ε > 0, ∀ᶠ n in atTop,
      P.J n σ (k₀, z₀) ≤ P.V (k₀, z₀) + ε :=
  P.stochastic_brockMirman hk₀ z₀

end StochBrockMirmanFrozen

end Econ.Audit
