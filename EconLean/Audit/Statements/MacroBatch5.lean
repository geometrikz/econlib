/-
# Frozen statements: precautionary saving, AD vs Radner, Lucas tree, PIH, NK

Headline statements of `Macro/Consumption/Precautionary.lean`,
`Finance/SequentialMarkets.lean`, `Finance/LucasTree.lean`,
`Macro/Consumption/PIH.lean`, `Macro/NK/ThreeEquation.lean`, and the review
fixes in `Macro/Growth/Romer.lean`, `Macro/Banking/DiamondDybvig.lean` and
`Macro/Misallocation.lean`, copied verbatim after context-isolated adversarial
review (2026-11-23; see `Audit/REVIEW-macro-batch5.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Consumption.Precautionary
public import EconLean.Macro.Consumption.PIH
public import EconLean.Finance.SequentialMarkets
public import EconLean.Finance.LucasTree
public import EconLean.Macro.NK.ThreeEquation
public import EconLean.Macro.Growth.Romer
public import EconLean.Macro.Banking.DiamondDybvig
public import EconLean.Macro.Misallocation

@[expose] public section

namespace Econ.Audit

open Set Finset Real

section Precautionary
open Econ.Precautionary

theorem frozen_prec_isOptimal_of_foc {ι : Type*} [Fintype ι] (P : Problem ι) {s : ℝ}
    (hs : P.Feasible s)
    (h : P.u' (P.w - s) = P.β * P.R * ∑ i, P.π i * P.u' (P.R * s + P.y i)) : P.IsOptimal s :=
  P.isOptimal_of_foc hs h

theorem frozen_prec_foc {ι : Type*} [Fintype ι] (P : Problem ι) {s : ℝ} (h : P.IsOptimal s) :
    P.u' (P.w - s) = P.β * P.R * ∑ i, P.π i * P.u' (P.R * s + P.y i) :=
  P.foc h

theorem frozen_precautionary {ι : Type*} [Fintype ι] (P : Problem ι)
    (hconv : ConvexOn ℝ (Ioi 0) P.u') {sc sr : ℝ}
    (hc : P.certain.IsOptimal sc) (hr : P.IsOptimal sr) : sc ≤ sr :=
  P.precautionary hconv hc hr

theorem frozen_precautionary_strict {ι : Type*} [Fintype ι] (P : Problem ι)
    (hconv : StrictConvexOn ℝ (Ioi 0) P.u') (hpos : ∀ i, 0 < P.π i)
    (hy : ∃ i j, P.y i ≠ P.y j) {sc sr : ℝ} (hc : P.certain.IsOptimal sc)
    (hr : P.IsOptimal sr) : sc < sr :=
  P.precautionary_strict hconv hpos hy hc hr

end Precautionary

section Sequential
open Econ.AssetPricing

theorem frozen_seqBudget_iff_adBudget {σ ι : Type*} [Fintype σ] [Fintype ι] {M : Market σ ι}
    {m : σ → ℝ} (hm : M.IsStatePrice m) (hc : M.Complete) (e x : Bundle σ) :
    M.SeqBudget e x ↔ adBudget m e x :=
  Market.seqBudget_iff_adBudget hm hc e x

theorem frozen_complete_iff_budget_eq {σ ι : Type*} [Fintype σ] [Fintype ι] {M : Market σ ι}
    {m : σ → ℝ} (hm : M.IsStatePrice m) :
    M.Complete ↔ ∀ e x : Bundle σ, M.SeqBudget e x ↔ adBudget m e x :=
  Market.complete_iff_budget_eq hm

theorem frozen_isRadner_of_isAD {σ ι A : Type*} [Fintype σ] [Fintype ι] [Fintype A] [Nonempty A]
    {E : Economy A σ} {M : Market σ ι} {m : σ → ℝ} (hm : M.IsStatePrice m) (hc : M.Complete)
    {x : A → Bundle σ} (hx : E.IsAD m x) : ∃ h, E.IsRadner M x h :=
  Economy.isRadner_of_isAD hm hc hx

theorem frozen_isAD_of_isRadner {σ ι A : Type*} [Fintype σ] [Fintype ι] [Fintype A]
    {E : Economy A σ} {M : Market σ ι} {m : σ → ℝ} (hm : M.IsStatePrice m) (hc : M.Complete)
    {x : A → Bundle σ} {h : A → ι → ℝ} (hx : E.IsRadner M x h) : E.IsAD m x :=
  Economy.isAD_of_isRadner hm hc hx

end Sequential

section Lucas
open Econ.LucasTree

theorem frozen_lt_existsUnique_price {Z : Type*} [Fintype Z] (T : LucasTree.Tree Z) : ∃! p, T.IsPrice p :=
  T.existsUnique_price

theorem frozen_lt_price_pos {Z : Type*} [Fintype Z] (T : LucasTree.Tree Z) {p : Z → ℝ} (hp : T.IsPrice p)
    (z : Z) : 0 < p z :=
  T.price_pos hp z

theorem frozen_lt_isPrice_log {Z : Type*} [Fintype Z] (T : LucasTree.Tree Z)
    (hlog : ∀ c, 0 < c → T.u' c = c⁻¹) : T.IsPrice fun z => T.β / (1 - T.β) * T.d z :=
  T.isPrice_log hlog

theorem frozen_lt_premium_eq {Z : Type*} [Fintype Z] (T : LucasTree.Tree Z) {p : Z → ℝ}
    (hp : T.IsPrice p) (z : Z) :
    expect (T.Q z) (T.ret p z) - T.riskFree z =
      -T.riskFree z * cov (T.Q z) (T.sdf z) (T.ret p z) :=
  T.premium_eq hp z

theorem frozen_lt_hansen_jagannathan {Z : Type*} [Fintype Z] (T : LucasTree.Tree Z) {p : Z → ℝ}
    (hp : T.IsPrice p) (z : Z) :
    (expect (T.Q z) (T.ret p z) - T.riskFree z) ^ 2 ≤
      var (T.Q z) (T.sdf z) / T.bondPrice z ^ 2 * var (T.Q z) (T.ret p z) :=
  T.hansen_jagannathan hp z

theorem frozen_hj_bound {Z : Type*} [Fintype Z] {w : Z → ℝ} (hw : ∀ z, 0 ≤ w z)
    (hw1 : ∑ z, w z = 1) {m r : Z → ℝ}
    (hm : 0 < expect w m) (he : expect w (fun z => m z * r z) = 1) :
    (expect w r - 1 / expect w m) ^ 2 ≤ var w m / expect w m ^ 2 * var w r :=
  hj_bound hw hw1 hm he

end Lucas

section PIH
open Econ.PIH

theorem frozen_pih_euler {S : Type*} [Fintype S] [DecidableEq S] {P : Problem S}
    {c a : List S → ℝ} (h₀ : List S) (hopt : P.IsOptimal c a) (hlen : h₀.length < P.N)
    (hP : 0 < P.prob h₀) :
    P.u' (c h₀) = P.β * P.R * ∑ s, P.π h₀ s * P.u' (c (s :: h₀)) :=
  Problem.euler h₀ hopt hlen hP

theorem frozen_pih_isOptimal_of_euler {S : Type*} [Fintype S] [DecidableEq S] (P : Problem S)
    (hanti : Antitone P.u') {c a : List S → ℝ} (hf : P.Feasible c a)
    (he : ∀ h : List S, h.length < P.N →
      P.u' (c h) = P.β * P.R * ∑ s, P.π h s * P.u' (c (s :: h)))
    (hterm : ∀ h : List S, h.length = P.N → c h = a h + P.y h ∧ 0 ≤ P.u' (c h)) :
    P.IsOptimal c a :=
  P.isOptimal_of_euler hanti hf he hterm

theorem frozen_hall {S : Type*} [Fintype S] [DecidableEq S] (P : Problem S) {κ γ : ℝ}
    (hγ : γ ≠ 0) (hu : ∀ c, P.u' c = κ - γ * c) (hβR : P.β * P.R = 1)
    {c a : List S → ℝ} (hopt : P.IsOptimal c a) (h₀ : List S) (hlen : h₀.length < P.N)
    (hP : 0 < P.prob h₀) : c h₀ = ∑ s, P.π h₀ s * c (s :: h₀) :=
  P.hall hγ hu hβR hopt h₀ hlen hP

end PIH

section NK
open Econ.NK

theorem frozen_bk_determinate_iff (M : Matrix (Fin 2) (Fin 2) ℝ) (hD : 0 < M.det) :
    Determinate M ↔ 1 < M.det ∧ |M.trace| < 1 + M.det :=
  determinate_iff M hD

theorem frozen_taylor_principle (E : Model) :
    E.Determinate ↔ 0 < E.κ * (E.φπ - 1) + (1 - E.β) * E.φx :=
  E.taylor_principle

theorem frozen_taylor_principle_strict (E : Model) (h : E.φx = 0) :
    E.Determinate ↔ 1 < E.φπ :=
  E.taylor_principle_strict h

end NK

section Fixes

theorem frozen_romer_household_optimal (E : Econ.Romer.Economy) {k₀ : ℝ} (hk : 0 < k₀) :
    (∀ (P : Econ.AK.Plan (1 + E.rEq) k₀) {W : ℝ},
      HasSum (fun t => E.β ^ t * log (P.c t)) W →
        W ≤ ∑' t, E.β ^ t * log (Econ.AK.cstar E.β (1 + E.rEq) k₀ t)) ∧
    ∀ t, Econ.AK.cstar E.β (1 + E.rEq) k₀ (t + 1) =
      E.eulerGrowth * Econ.AK.cstar E.β (1 + E.rEq) k₀ t :=
  E.household_optimal hk

theorem frozen_dd_suspension_unique (B : Econ.DiamondDybvig.Bank)
    (h : B.r₁ * (1 - B.lam + B.lam * B.R) < B.R) :
    B.SuspensionGoodEquilibrium ∧ ¬ B.SuspensionRunEquilibrium :=
  B.suspension_unique h

theorem frozen_tfp_eq_hk {ι : Type*} [Fintype ι] [Nonempty ι] (I : Econ.Misallocation.Industry ι)
    {s : ι → ℝ} (hpos : ∀ i, 0 < s i) :
    I.tfp s = (∑ i, (I.A i * I.tfprAvg s / I.tfpr s i) ^ (I.σ - 1)) ^ (1 / (I.σ - 1)) :=
  I.tfp_eq_hk hpos

end Fixes

end Econ.Audit
