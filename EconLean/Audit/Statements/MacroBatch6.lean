/-
# Frozen statements: NK policy, Blanchard–Kahn, networks, Baqaee–Farhi,
# Chamley–Judd, sticky information, social cost of carbon

Headline statements of `Macro/NK/Shocks.lean`, `Macro/NK/BlanchardKahn.lean`,
`Macro/ProductionNetworks.lean`, `Macro/BaqaeeFarhi.lean`, `Macro/Fiscal/ChamleyJudd.lean`,
`Macro/NK/StickyInformation.lean` and `Macro/Climate/SocialCostCarbon.lean`,
copied verbatim after context-isolated adversarial review (2026-11-23; see
`Audit/REVIEW-macro-batch6.md`). Each is closed by the library theorem, so if a
library statement is weakened this file stops compiling. Do not edit a
statement here without a new review.
-/
module

public import EconLean.Macro.NK.Shocks
public import EconLean.Macro.NK.BlanchardKahn
public import EconLean.Macro.ProductionNetworks
public import EconLean.Macro.BaqaeeFarhi
public import EconLean.Macro.Fiscal.ChamleyJudd
public import EconLean.Macro.NK.StickyInformation
public import EconLean.Macro.Climate.SocialCostCarbon

@[expose] public section

namespace Econ.Audit

open Finset Filter Topology

theorem frozen_divine_coincidence (E : Econ.NK.Model)
    (hdet : 0 < E.κ * (E.φπ - 1) + (1 - E.β) * E.φx)
    {rn x p i : ℕ → ℝ} (h : E.IsShockEquilibrium rn 0 x p i) (hr : E.FollowsRule rn x p i)
    (hb : ∃ B, ∀ t, |x t| ≤ B ∧ |p t| ≤ B) : ∀ t, x t = 0 ∧ p t = 0 :=
  E.divine_coincidence hdet h hr hb

theorem frozen_discretion_unique {β κ lam ρ u₀ : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) {x p : ℕ → ℝ}
    (hpc : ∀ t, p t = β * p (t + 1) + κ * x t + ρ ^ t * u₀)
    (htr : ∀ t, x t = -(κ / lam) * p t) (hb : ∃ B, ∀ t, |p t| ≤ B) :
    ∀ t, p t = lam * (ρ ^ t * u₀) / (κ ^ 2 + lam * (1 - β * ρ)) ∧
      x t = -κ * (ρ ^ t * u₀) / (κ ^ 2 + lam * (1 - β * ρ)) :=
  Econ.NK.discretion_unique hβ₀ hβ₁ hκ hlam hρ hpc htr hb

theorem frozen_determinateN_iff {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    Econ.NK.DeterminateN M ↔ ∀ μ, Econ.NK.IsEigenvalue M μ → 1 < ‖μ‖ :=
  Econ.NK.determinateN_iff M

theorem frozen_hulten {n : Type*} [Fintype n] [DecidableEq n] (N : Econ.ProdNetworks.Network n)
    {z z' π π' : n → ℝ} (hz : ∀ i, 0 < z i) (hz' : ∀ i, 0 < z' i)
    (hπ : N.IsPriceSystem z π) (hπ' : N.IsPriceSystem z' π') :
    N.logGDP π' - N.logGDP π = ∑ i, N.domar i * (Real.log (z' i) - Real.log (z i)) :=
  N.hulten hz hz' hπ hπ'

theorem frozen_isSales_iff {n : Type*} [Fintype n] [DecidableEq n] (N : Econ.ProdNetworks.Network n)
    (S : n → ℝ) : N.IsSales S ↔ S = N.domar :=
  N.isSales_iff S

theorem frozen_aggVar_ge_div {n : Type*} [Fintype n] [DecidableEq n] (N : Econ.ProdNetworks.Network n)
    (σ : ℝ) [Nonempty n] : σ ^ 2 / Fintype.card n ≤ N.aggVar σ :=
  N.aggVar_ge_div σ

theorem frozen_star_aggVar_ge (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 0 ≤ a) (ha0 : 0 < a)
    (ha1 : a < 1) (σ : ℝ) :
    σ ^ 2 * a ^ 2 / 4 ≤ (Econ.ProdNetworks.star m a ha ha1).aggVar σ :=
  Econ.ProdNetworks.star_aggVar_ge m hm a ha ha0 ha1 σ

theorem frozen_complements_le_hulten {n : Type*} [Fintype n] (E : Econ.BaqaeeFarhi.Economy n)
    (hθ : E.θ < 1) (x d : n → ℝ) :
    E.logY (x + d) - E.logY x ≤ ∑ i, E.domar x i * d i :=
  E.complements_le_hulten hθ x d

theorem frozen_substitutes_ge_hulten {n : Type*} [Fintype n] (E : Econ.BaqaeeFarhi.Economy n)
    (hθ : 1 < E.θ) (x d : n → ℝ) :
    ∑ i, E.domar x i * d i ≤ E.logY (x + d) - E.logY x :=
  E.substitutes_ge_hulten hθ x d

theorem frozen_hasDerivAt_logY {n : Type*} [Fintype n] (E : Econ.BaqaeeFarhi.Economy n)
    (hθ : E.θ ≠ 1) (x d : n → ℝ) :
    HasDerivAt (fun t : ℝ => E.logY (x + t • d)) (∑ i, E.domar x i * d i) 0 :=
  E.hasDerivAt_logY hθ x d

theorem frozen_chamley_judd {β : ℝ} (hβ : 0 < β) {uc Wc r τ : ℕ → ℝ}
    (h : Econ.ChamleyJudd.IsRamseyFOC β uc Wc r τ)
    {ucs Wcs rs τs : ℝ} (hucs : 0 < ucs) (hWcs : 0 < Wcs) (hrs : rs ≠ 0)
    (huc : Tendsto uc atTop (𝓝 ucs)) (hWc : Tendsto Wc atTop (𝓝 Wcs))
    (hr : Tendsto r atTop (𝓝 rs)) (hτ : Tendsto τ atTop (𝓝 τs)) :
    τs = 0 :=
  Econ.ChamleyJudd.chamley_judd hβ h hucs hWcs hrs huc hWc hr hτ

theorem frozen_ratio_unbounded {β : ℝ} {uc Wc r τ : ℕ → ℝ}
    (h : Econ.ChamleyJudd.IsRamseyFOC β uc Wc r τ)
    (huc : ∀ t, 0 < uc t) (hWc : ∀ t, 0 < Wc t)
    {τl rl : ℝ} (hτl : 0 < τl) (hτ : ∀ t, τl ≤ τ t ∧ τ t ≤ 1)
    (hrl : 0 < rl) (hr : ∀ t, rl ≤ r t) :
    ∀ M, ∃ t, M < uc t / Wc t :=
  Econ.ChamleyJudd.ratio_unbounded h huc hWc hτl hτ hrl hr

theorem frozen_sticky_output_eq {lam α : ℝ} (hl : 0 < lam) (hl1 : lam ≤ 1) (hα : 0 < α)
    (hα1 : α ≤ 1) {m m0 p : ℕ → ℝ} (hp : Econ.StickyInfo.IsEquilibrium lam α m m0 p) (t : ℕ) :
    m t - p t = Econ.StickyInfo.output lam α m m0 t :=
  Econ.StickyInfo.output_eq hl hl1 hα hα1 hp t

theorem frozen_announced_disinflation_cost {lam α : ℝ} (hl : 0 < lam) (hl1 : lam ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1)
    {m m0 : ℕ → ℝ} {T : ℕ} {D : ℝ} (hpre : ∀ t < T, m t = m0 t)
    (hD : ∀ t, |m t - m0 t| ≤ D) (t : ℕ) :
    |Econ.StickyInfo.output lam α m m0 t| ≤ (1 - lam) ^ (T + 1) * D / α :=
  Econ.StickyInfo.announced_disinflation_cost hl hl1 hα hα1 hpre hD t

theorem frozen_scc_eq (P : Econ.Climate.Params) {Ytilde S : ℕ → ℝ} (hY : ∀ j, 0 < Ytilde j) :
    P.scc Ytilde S = P.γ * ((1 - P.s) * P.outputAfter Ytilde S 0 0) * P.kernel :=
  P.scc_eq hY

theorem frozen_tsum_kernel (P : Econ.Climate.Params) :
    ∑' j : ℕ, P.β ^ j * P.remain j = P.kernel :=
  P.tsum_kernel

theorem frozen_sccCap_eq (P : Econ.Climate.Params) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (a S : ℕ → ℝ) (k0 : ℝ) :
    P.sccCap α a S k0 = P.γ * Real.exp (P.logYcap α a S k0 0 0) * P.kernel :=
  P.sccCap_eq hα hα1 a S k0

theorem frozen_bf_second_order {n : Type*} [Fintype n] (E : Econ.BaqaeeFarhi.Economy n)
    (hθ : E.θ ≠ 1) (x d : n → ℝ) :
    deriv (deriv fun t : ℝ => E.logY (x + t • d)) 0 =
      (E.θ - 1) * (∑ i, E.domar x i * d i ^ 2 - (∑ i, E.domar x i * d i) ^ 2) :=
  E.second_order hθ x d

end Econ.Audit

end
