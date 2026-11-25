/-
# Frozen statements: group strategy-proofness of DA, reputation, lemons with gains from trade

Headline statements of `Matching/GroupStrategyProof`, `Games/Reputation` and
`Information/LemonsGains`, copied after the adversarial review recorded in
`Audit/REVIEW-batch15.md`. Each is closed by the library theorem, so if a library statement is
ever weakened this file stops compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Matching.GroupStrategyProof
public import EconLean.Games.Reputation
public import EconLean.Information.LemonsGains

@[expose] public section

namespace Econ.Audit

open Finset Econ

theorem frozen_daMatching_groupStrategyproof {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq W] (um um' : M → W → ℝ) (uw : W → M → ℝ)
    (hum : ∀ m, Function.Injective (um m)) (huw : ∀ w, Function.Injective (uw w))
    (C : Finset M) (hC : C.Nonempty) (hsame : ∀ m, m ∉ C → um' m = um m) :
    ¬ ∀ m ∈ C, Improves um (daMatching um uw) (daMatching um' uw) m :=
  daMatching_groupStrategyproof um um' uw hum huw C hC hsame

theorem frozen_bounded_surprises {μ₀ : ℝ} {q : ℕ → ℝ} (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) (T : ℕ) :
    (((range T).filter fun t => predictA μ₀ q t ≤ π).card : ℝ) ≤ Real.log μ₀ / Real.log π :=
  bounded_surprises hμ₀ hμ₁ hq hπ0 hπ1 T

theorem frozen_reputation_bound {μ₀ : ℝ} {q : ℕ → ℝ} (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1)
    (hq : ∀ t, 0 ≤ q t ∧ q t ≤ 1) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) {u : ℕ → ℝ}
    {v m Mx δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hm : ∀ t, m ≤ u t) (hMx : ∀ t, u t ≤ Mx)
    (hmv : m ≤ v) (hbr : ∀ t, π < predictA μ₀ q t → v ≤ u t) :
    δ ^ ⌊Real.log μ₀ / Real.log π⌋₊ * v + (1 - δ ^ ⌊Real.log μ₀ / Real.log π⌋₊) * m ≤
      (1 - δ) * ∑' t, δ ^ t * u t :=
  reputation_bound hμ₀ hμ₁ hq hπ0 hπ1 hδ0 hδ1 hm hMx hmv hbr

theorem frozen_reputation_limit {μ₀ : ℝ} (hμ₀ : 0 < μ₀) (hμ₁ : μ₀ ≤ 1) {π : ℝ} (hπ0 : 0 < π)
    (hπ1 : π < 1) {v m : ℝ} (hmv : m ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ < 1, ∀ δ, δ₀ ≤ δ → δ < 1 → ∀ (q u : ℕ → ℝ) (Mx : ℝ), (∀ t, 0 ≤ q t ∧ q t ≤ 1) →
      (∀ t, m ≤ u t) → (∀ t, u t ≤ Mx) → (∀ t, π < predictA μ₀ q t → v ≤ u t) →
      v - ε ≤ (1 - δ) * ∑' t, δ ^ t * u t :=
  reputation_limit hμ₀ hμ₁ hπ0 hπ1 hmv hε

theorem frozen_lemonsEqR_price_le_mean {F : SimpleLottery} {r : ℝ → ℝ} (hr : Monotone r)
    {p : ℝ} (h : IsLemonsEqR F r p) : p ≤ F.mean :=
  lemonsEqR_price_le_mean hr h

theorem frozen_lemonsEqR_withheld {F : SimpleLottery} {r : ℝ → ℝ} (hr : Monotone r) {p : ℝ}
    (h : IsLemonsEqR F r p) {θ : ℝ} (hθ : F.mean < r θ) : p < r θ :=
  lemonsEqR_withheld hr h hθ

end Econ.Audit
