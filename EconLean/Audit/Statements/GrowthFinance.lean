/-
# Frozen statements: discounted Hosios, AK, Lucas, Romer, finite-state FTAP

Headline statements of `Macro/Labor/HosiosDiscounted.lean`,
`Macro/Growth/AK.lean`, `Macro/Growth/Lucas.lean`, `Macro/Growth/Romer.lean`
and `Finance/AssetPricing.lean`, copied verbatim after two rounds of
context-isolated adversarial review (2026-11-23; see
`Audit/REVIEW-growth-finance.md`). Each is closed by the library theorem, so if
a library statement is weakened this file stops compiling. Lightweight
stand-in for `leanprover/comparator`. Do not edit a statement here without a
new review.
-/
module

public import EconLean.Macro.Labor.HosiosDiscounted
public import EconLean.Macro.Growth.Lucas
public import EconLean.Macro.Growth.Romer
public import EconLean.Finance.AssetPricing

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Real Finset

section Hosios
open Econ.DMP

theorem frozen_hd_isSearchEqm_iff (D : Discrete) {β θ : ℝ} (hβ₀ : 0 ≤ β) :
    (∃ J E U w, D.IsSearchEqm β θ J E U w) ↔
      D.IsEquilibrium D.rate β θ ∧ D.findRate θ ≤ 1 ∧ D.fillRate θ ≤ 1 :=
  D.isSearchEqm_iff hβ₀

theorem frozen_hd_isOptimal_stationary (D : Discrete) {θp : ℝ}
    (hp : D.IsEquilibrium D.rate D.η θp) (hfp : D.findRate θp ≤ 1) (hqp : D.fillRate θp ≤ 1) {u₀ : ℝ}
    (hu : u₀ ∈ Icc (0 : ℝ) 1) : D.IsOptimal u₀ (fun _ => θp) :=
  D.isOptimal_stationary hp hfp hqp hu

theorem frozen_hd_welfare_lt (D : Discrete) {θp : ℝ} (hp : D.IsEquilibrium D.rate D.η θp)
    (hfp : D.findRate θp ≤ 1) (hqp : D.fillRate θp ≤ 1) {u₀ : ℝ} (hu : u₀ ∈ Ioc (0 : ℝ) 1) {θ : ℕ → ℝ}
    (hθ : D.Feasible θ) (hne : θ 0 ≠ θp) : D.welfare u₀ θ < D.welfare u₀ (fun _ => θp) :=
  D.welfare_lt hp hfp hqp hu hθ hne

theorem frozen_hd_hosios (D : Discrete) {β θe θp u₀ : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (he : ∃ J E U w, D.IsSearchEqm β θe J E U w)
    (hp : D.IsEquilibrium D.rate D.η θp) (hfp : D.findRate θp ≤ 1) (hqp : D.fillRate θp ≤ 1)
    (hu : u₀ ∈ Ioc (0 : ℝ) 1) :
    D.IsOptimal u₀ (fun _ => θe) ↔ β = D.η :=
  D.hosios hβ₀ hβ₁ he hp hfp hqp hu

end Hosios

section AK
open Econ.AK

theorem frozen_ak_growthRate_eq (s A δ k₀ : ℝ) (t : ℕ) (hk : kpath s A δ k₀ t ≠ 0) :
    (kpath s A δ k₀ (t + 1) - kpath s A δ k₀ t) / kpath s A δ k₀ t = s * A - δ :=
  growthRate_eq s A δ k₀ t hk

theorem frozen_ak_optimal {β R k₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hR : 0 < R) (hk : 0 < k₀)
    (P : Plan R k₀) {W : ℝ} (hW : HasSum (fun t => β ^ t * log (P.c t)) W) :
    W ≤ ∑' t, β ^ t * log (cstar β R k₀ t) :=
  optimal hβ₀ hβ₁ hR hk P hW

theorem frozen_ak_cstar_succ (β R k₀ : ℝ) (t : ℕ) :
    cstar β R k₀ (t + 1) = β * R * cstar β R k₀ t :=
  cstar_succ β R k₀ t

end AK

section Lucas
open Econ.Lucas

theorem frozen_lucas_isEquilibrium_iff (E : Economy) {h₀ : ℝ} (hh : 0 < h₀)
    (hint : 1 - E.β ≤ E.β * E.B) (u : ℕ → ℝ) :
    E.IsEquilibrium h₀ u ↔ u = fun _ => (1 - E.β) * (1 + E.B) / E.B :=
  E.isEquilibrium_iff hh hint u

theorem frozen_lucas_isEfficient_iff (E : Economy) {h₀ : ℝ} (hh : 0 < h₀)
    (hint : 1 - E.β ≤ E.β * E.B) (u : ℕ → ℝ) :
    E.IsEfficient h₀ u ↔ u = fun _ => E.uStar ((1 + E.γ) * E.β / (1 - E.β)) :=
  E.isEfficient_iff hh hint u

theorem frozen_lucas (E : Economy) {h₀ : ℝ} (hh : 0 < h₀) (hint : 1 - E.β ≤ E.β * E.B)
    {ue up : ℕ → ℝ} (he : E.IsEquilibrium h₀ ue) (hp : E.IsEfficient h₀ up) :
    (0 < E.γ → ∀ t, up t < ue t ∧ E.growth (ue t) < E.growth (up t)) ∧
    (E.γ = 0 → ue = up) :=
  E.lucas hh hint he hp

end Lucas

section Romer
open Econ.Romer

theorem frozen_romer_demand_optimal (E : Economy) {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    E.finalProfit p x ≤ E.finalProfit p (E.demand p) ∧
    (x ≠ E.demand p → E.finalProfit p x < E.finalProfit p (E.demand p)) :=
  E.demand_optimal hp hx

theorem frozen_romer_monopoly_price (E : Economy) {p : ℝ} (hp : 0 < p) :
    E.monoProfit p ≤ E.monoProfit 1 ∧ (p ≠ 1 → E.monoProfit p < E.monoProfit 1) ∧
    E.monoProfit 1 = E.a * E.L :=
  E.monopoly_price hp

theorem frozen_romer_freeEntry_iff (E : Economy) {r : ℝ} (hr : 0 < r) :
    E.η * (E.monoProfit 1 / r) = 1 ↔ r = E.rEq :=
  E.freeEntry_iff hr

theorem frozen_romer_planner_optimal (E : Economy) {N₀ : ℝ} (hN : 0 < N₀)
    (P : E.PlannerPlan N₀) {W : ℝ} (hW : HasSum (fun t => E.β ^ t * log (P.C t)) W) :
    W ≤ ∑' t, E.β ^ t * log (AK.cstar E.β E.RPlan (N₀ / E.η) t) :=
  E.planner_optimal hN P hW

theorem frozen_romer_eulerGrowth_lt_optimal (E : Economy) : E.eulerGrowth < E.β * E.RPlan :=
  E.eulerGrowth_lt_optimal

end Romer

section AssetPricing
open Econ.AssetPricing

theorem frozen_ftap {σ ι : Type*} [Fintype σ] [Fintype ι] (M : Market σ ι) :
    M.NoArbitrage ↔ ∃ m, M.IsStatePrice m :=
  M.ftap

theorem frozen_complete_iff_unique {σ ι : Type*} [Fintype σ] [Fintype ι] (M : Market σ ι)
    (hna : M.NoArbitrage) : M.Complete ↔ ∃! m, M.IsStatePrice m :=
  M.complete_iff_unique hna

end AssetPricing

end Econ.Audit
