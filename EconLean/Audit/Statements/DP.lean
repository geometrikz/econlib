/-
# Frozen statements: dynamic programming foundations (milestone M5, F8/F9)

Headline statements of `Macro/DP/*.lean`, copied verbatim after they passed the
context-isolated adversarial review (2026-11-23; record in
`Audit/REVIEW-dp.md`). Each is closed by the library theorem, so if a library
statement is ever weakened, this file stops compiling. Lightweight stand-in
for `leanprover/comparator`. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.DP.Concavity
public import EconLean.Macro.DP.BrockMirman

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ BoundedContinuousFunction Real

section Blackwell
variable {X : Type*} [TopologicalSpace X]

theorem frozen_blackwell {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : (X →ᵇ ℝ) → (X →ᵇ ℝ))
    (hmono : ∀ f g : X →ᵇ ℝ, (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    (hdisc : ∀ (f : X →ᵇ ℝ) (a : ℝ), 0 ≤ a → ∀ x, T (f + const X a) x ≤ T f x + β * a) :
    ContractingWith ⟨β, hβ0⟩ T :=
  blackwell hβ0 hβ1 T hmono hdisc

theorem frozen_blackwell_fixedPoint {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (T : (X →ᵇ ℝ) → (X →ᵇ ℝ))
    (hmono : ∀ f g : X →ᵇ ℝ, (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    (hdisc : ∀ (f : X →ᵇ ℝ) (a : ℝ), 0 ≤ a → ∀ x, T (f + const X a) x ≤ T f x + β * a) :
    ∃! v : X →ᵇ ℝ, T v = v ∧
      ∀ v₀ : X →ᵇ ℝ, ∀ n : ℕ, dist (T^[n] v₀) v ≤ dist v₀ (T v₀) * β ^ n / (1 - β) :=
  blackwell_fixedPoint hβ0 hβ1 T hmono hdisc
end Blackwell

section Sequence
variable {X : Type*}

theorem frozen_IsOptimalValue_unique {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} {x₀ : X}
    {w w' : ℝ} (hw : IsOptimalValue Γ F β x₀ w) (hw' : IsOptimalValue Γ F β x₀ w') : w = w' :=
  hw.unique hw'

theorem frozen_verification {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β) {S : Set X}
    (hS : ∀ x ∈ S, Γ x ⊆ S) {v : X → ℝ} {g : X → X}
    (hineq : ∀ x ∈ S, ∀ y ∈ Γ x, F x y + β * v y ≤ v x)
    (hg : ∀ x ∈ S, g x ∈ Γ x ∧ F x (g x) + β * v (g x) = v x)
    (hbound : ∀ x₀ ∈ S, ∀ x, IsFeasiblePlan Γ x₀ x →
      ∀ ε > 0, ∀ᶠ n in atTop, -ε ≤ β ^ n * v (x n))
    (hpol : ∀ x₀ ∈ S, ∀ ε > 0, ∀ᶠ n in atTop, β ^ n * v (planOf g x₀ n) ≤ ε)
    {x₀ : X} (hx₀ : x₀ ∈ S) :
    IsOptimalValue Γ F β x₀ (v x₀) ∧
      Tendsto (partialPayoff F β (planOf g x₀)) atTop (𝓝 (v x₀)) :=
  verification hβ hS hineq hg hbound hpol hx₀

theorem frozen_verification_of_lowerBound {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {S : Set X} (hS : ∀ x ∈ S, Γ x ⊆ S) {v : X → ℝ} {g : X → X}
    (hineq : ∀ x ∈ S, ∀ y ∈ Γ x, F x y + β * v y ≤ v x)
    (hg : ∀ x ∈ S, g x ∈ Γ x ∧ F x (g x) + β * v (g x) = v x)
    {a b : ℝ} (hb : 1 ≤ b) (hlow : ∀ x ∈ S, ∀ y ∈ Γ x, a + b * F x y ≤ v x)
    (hpol : ∀ x₀ ∈ S, ∀ ε > 0, ∀ᶠ n in atTop, β ^ n * v (planOf g x₀ n) ≤ ε)
    {x₀ : X} (hx₀ : x₀ ∈ S) :
    IsOptimalValue Γ F β x₀ (v x₀) ∧
      Tendsto (partialPayoff F β (planOf g x₀)) atTop (𝓝 (v x₀)) :=
  verification_of_lowerBound hβ0 hβ1 hS hineq hg hb hlow hpol hx₀

theorem frozen_euler_transversality {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    {F : E → E → ℝ} {Γ : E → Set E} {β : ℝ}
    (hβ : 0 ≤ β) (Fx Fy : E → E → E →ₗ[ℝ] ℝ)
    (hconc : ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' →
      F x' y' ≤ F x y + Fx x y (x' - x) + Fy x y (y' - y))
    (hΓ : ∀ x y, y ∈ Γ x → 0 ≤ y)
    (hFx : ∀ x y z, y ∈ Γ x → 0 ≤ z → 0 ≤ Fx x y z)
    {x₀ : E} {xs : ℕ → E} (hxs : IsFeasiblePlan Γ x₀ xs)
    (heuler : ∀ t, Fy (xs t) (xs (t + 1)) + β • Fx (xs (t + 1)) (xs (t + 2)) = 0)
    (htvc : Tendsto (fun t => β ^ t * Fx (xs t) (xs (t + 1)) (xs t)) atTop (𝓝 0)) :
    IsOptimalPlan Γ F β x₀ xs :=
  euler_transversality hβ Fx Fy hconc hΓ hFx hxs heuler htvc
end Sequence

section Bellman
variable {X : Type*} [TopologicalSpace X] (P : DynProg X)

theorem frozen_bellman_equation (x : X) :
    IsGreatest ((fun y => P.F x y + P.β * P.value y) '' P.Γ x) (P.value x) :=
  P.bellman_equation x

theorem frozen_value_unique (w : X →ᵇ ℝ)
    (hw : ∀ x, IsGreatest ((fun y => P.F x y + P.β * w y) '' P.Γ x) (w x)) :
    w = P.value :=
  P.value_unique w hw

theorem frozen_mem_policy_iff {x y : X} :
    y ∈ P.policy x ↔ y ∈ P.Γ x ∧ P.F x y + P.β * P.value y = P.value x :=
  P.mem_policy_iff

theorem frozen_policy_nonempty_compact_uhc :
    (∀ x, (P.policy x).Nonempty ∧ IsCompact (P.policy x)) ∧ UpperHemicontinuous P.policy :=
  P.policy_nonempty_compact_uhc

theorem frozen_principle_of_optimality (x₀ : X) :
    IsGreatest {u | ∃ x, IsFeasiblePlan P.Γ x₀ x ∧ P.payoff x = u} (P.value x₀) ∧
      ∀ x, IsFeasiblePlan P.Γ x₀ x →
        (P.payoff x = P.value x₀ ↔ ∀ t, x (t + 1) ∈ P.policy (x t)) :=
  P.principle_of_optimality x₀

theorem frozen_value_strictMono [Preorder X]
    (hF : ∀ x x' y, x < x' → y ∈ P.Γ x → P.F x y < P.F x' y)
    (hΓ : ∀ x x', x ≤ x' → P.Γ x ⊆ P.Γ x') : StrictMono P.value :=
  P.value_strictMono hF hΓ
end Bellman

section Concavity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

theorem frozen_value_strictlyConcave (hS : Convex ℝ S) (P : DynProg S)
    (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F) :
    StrictlyConcaveFn (P.value : S → ℝ) :=
  P.value_strictlyConcave hS hΓ hF

theorem frozen_exists_continuous_policy (hS : Convex ℝ S) (P : DynProg S)
    (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F) :
    ∃ g : S → S, Continuous g ∧ ∀ x, P.policy x = {g x} :=
  P.exists_continuous_policy hS hΓ hF
end Concavity

theorem frozen_hasDerivAt_value {S : Set ℝ} (hS : Convex ℝ S) (P : DynProg S)
    (hΓ : ConvexGraph P.Γ) (hF : StrictlyConcaveReturn P.Γ P.F)
    {x₀ y₀ : S} (hint : (x₀ : ℝ) ∈ interior S) (hy₀ : y₀ ∈ P.policy x₀)
    (hloc : ∀ᶠ r in 𝓝 (x₀ : ℝ), ∀ h : r ∈ S, y₀ ∈ P.Γ ⟨r, h⟩)
    {Fx : ℝ} (hFx : HasDerivAt (extendS fun x => P.F x y₀) Fx x₀) :
    HasDerivAt (extendS (P.value : S → ℝ)) Fx x₀ :=
  P.hasDerivAt_value hS hΓ hF hint hy₀ hloc hFx

theorem frozen_brockMirman_value {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {k₀ : ℝ} (hk₀ : 0 < k₀) :
    IsOptimalValue (BrockMirman.Γ α) (BrockMirman.F α) β k₀
        ((log (1 - α * β) + (α * β / (1 - α * β)) * log (α * β)) / (1 - β) +
          α / (1 - α * β) * log k₀) ∧
      IsOptimalPlan (BrockMirman.Γ α) (BrockMirman.F α) β k₀
        (planOf (fun k => α * β * k ^ α) k₀) ∧
      Tendsto (partialPayoff (BrockMirman.F α) β (planOf (fun k => α * β * k ^ α) k₀)) atTop
        (𝓝 ((log (1 - α * β) + (α * β / (1 - α * β)) * log (α * β)) / (1 - β) +
          α / (1 - α * β) * log k₀)) :=
  BrockMirman.brockMirman_value hα0 hα1 hβ0 hβ1 hk₀

theorem frozen_brockMirman_optimal_of_euler {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {k₀ : ℝ} (hk₀ : 0 < k₀) :
    IsOptimalPlan (BrockMirman.Γ α) (BrockMirman.F α) β k₀
      (planOf (fun k => α * β * k ^ α) k₀) :=
  BrockMirman.brockMirman_optimal_of_euler hα0 hα1 hβ0 hβ1 hk₀

end Econ.Audit
