/-
# Frozen statements: McCall search, Hsieh–Klenow, Diamond–Dybvig, DMP, Hulten

Headline statements of `Macro/Labor/McCall.lean`, `Macro/Misallocation.lean`,
`Macro/Banking/DiamondDybvig.lean`, `Macro/Labor/DMP.lean` and
`Macro/Hulten.lean`, copied verbatim after two rounds of context-isolated
adversarial review (2026-11-23; see `Audit/REVIEW-quick-macro.md`). Each is
closed by the library theorem, so if a library statement is weakened this file
stops compiling. Lightweight stand-in for `leanprover/comparator`. Do not edit a
statement here without a new review.
-/
module

public import EconLean.Macro.Labor.McCall
public import EconLean.Macro.Labor.DMP
public import EconLean.Macro.Misallocation
public import EconLean.Macro.Banking.DiamondDybvig
public import EconLean.Macro.Hulten

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Real

section McCall
open Econ.McCall
variable {ι : Type*} [Fintype ι]

theorem frozen_isReservationWage_iff_textbook (e : Env) (F : OfferDist ι) (x : ℝ) :
    IsReservationWage e F x ↔
      x - e.c = e.β / (1 - e.β) * F.expect (fun w => max (w - x) 0) :=
  isReservationWage_iff_textbook e F x

theorem frozen_existsUnique_reservationWage (e : Env) (F : OfferDist ι) :
    ∃! x, IsReservationWage e F x :=
  existsUnique_reservationWage e F

theorem frozen_bellman_reservationWage (e : Env) (F : OfferDist ι) {wbar : ℝ}
    (h : IsReservationWage e F wbar) :
    bellman e F (fun i => max (F.w i) wbar / (1 - e.β)) = fun i => max (F.w i) wbar / (1 - e.β) :=
  bellman_reservationWage e F h

theorem frozen_bellman_unique (e : Env) (F : OfferDist ι) {V W : ι → ℝ}
    (hV : bellman e F V = V) (hW : bellman e F W = W) : V = W :=
  bellman_unique e F hV hW

theorem frozen_accept_iff (e : Env) (F : OfferDist ι) {wbar : ℝ} (h : IsReservationWage e F wbar)
    {V : ι → ℝ} (hV : bellman e F V = V) (i : ι) :
    e.c + e.β * ∑ j, F.p j * V j ≤ F.w i / (1 - e.β) ↔ wbar ≤ F.w i :=
  accept_iff e F h hV i

theorem frozen_reservationWage_strictMono_c (F : OfferDist ι) {β c₁ c₂ : ℝ} (hβ₀ : 0 ≤ β)
    (hβ₁ : β < 1) (hc : c₁ < c₂) {x₁ x₂ : ℝ} (h₁ : IsReservationWage ⟨β, c₁, hβ₀, hβ₁⟩ F x₁)
    (h₂ : IsReservationWage ⟨β, c₂, hβ₀, hβ₁⟩ F x₂) : x₁ < x₂ :=
  reservationWage_strictMono_c F hβ₀ hβ₁ hc h₁ h₂

theorem frozen_reservationWage_mono_riskier (e : Env) (F : OfferDist ι) {κ : Type*} [Fintype κ]
    (G : OfferDist κ) (hFG : Riskier F G) {xF xG : ℝ} (hF : IsReservationWage e F xF)
    (hG : IsReservationWage e G xG) : xF ≤ xG :=
  reservationWage_mono_riskier e F G hFG hF hG

end McCall

section Misallocation
open Econ.Misallocation
variable {ι : Type*} [Fintype ι] (I : Industry ι)

theorem frozen_tfp_le_efficient [Nonempty ι] {s : ι → ℝ} (hs : Industry.IsAlloc s) :
    I.tfp s ≤ I.tfpEfficient :=
  I.tfp_le_efficient hs

theorem frozen_tfp_eq_efficient_iff [Nonempty ι] {s : ι → ℝ} (hs : Industry.IsAlloc s) :
    I.tfp s = I.tfpEfficient ↔ s = I.effAlloc :=
  I.tfp_eq_efficient_iff hs

theorem frozen_tfpr_equal_iff [Nonempty ι] {s : ι → ℝ} (hs : Industry.IsAlloc s) (hpos : ∀ i, 0 < s i) :
    (∀ i j, I.tfpr s i = I.tfpr s j) ↔ I.tfp s = I.tfpEfficient :=
  I.tfpr_equal_iff hs hpos

theorem frozen_tfp_lt_of_tfpr_dispersion [Nonempty ι] {s : ι → ℝ} (hs : Industry.IsAlloc s)
    (hpos : ∀ i, 0 < s i) (hdisp : ∃ i j, I.tfpr s i ≠ I.tfpr s j) :
    I.tfp s < I.tfpEfficient :=
  I.tfp_lt_of_tfpr_dispersion hs hpos hdisp

theorem frozen_tfpr_wedgeAlloc [Nonempty ι] {τ : ι → ℝ} (hτ : ∀ i, τ i < 1) (i : ι) :
    I.tfpr (I.wedgeAlloc τ) i =
      (∑ j, I.wt j * (1 - τ j) ^ I.σ) ^ (1 - I.ρ) / (1 - τ i) :=
  I.tfpr_wedgeAlloc hτ i

theorem frozen_wedgeAlloc_efficient_iff [Nonempty ι] {τ : ι → ℝ} (hτ : ∀ i, τ i < 1) :
    I.tfp (I.wedgeAlloc τ) = I.tfpEfficient ↔ ∀ i j, τ i = τ j :=
  I.wedgeAlloc_efficient_iff hτ

end Misallocation

section DiamondDybvig
open Econ.DiamondDybvig

theorem frozen_crra_optimum {lam R γ : ℝ} (hlam₀ : 0 < lam) (hlam₁ : lam < 1) (hR : 1 < R)
    (hγ : 1 < γ) :
    lam * c1star lam R γ + (1 - lam) * c2star lam R γ / R = 1 ∧
    1 < c1star lam R γ ∧ c1star lam R γ < c2star lam R γ ∧
    ∀ x₁ x₂ : ℝ, 0 < x₁ → 0 < x₂ → lam * x₁ + (1 - lam) * x₂ / R ≤ 1 →
      lam * crra γ x₁ + (1 - lam) * crra γ x₂ ≤
        lam * crra γ (c1star lam R γ) + (1 - lam) * crra γ (c2star lam R γ) :=
  crra_optimum hlam₀ hlam₁ hR hγ

theorem frozen_goodEquilibrium_iff (B : Bank) :
    B.GoodEquilibrium ↔ B.r₁ * (1 - B.lam + B.lam * B.R) ≤ B.R :=
  B.goodEquilibrium_iff

theorem frozen_runEquilibrium_iff (B : Bank) : B.RunEquilibrium ↔ 1 < B.r₁ :=
  B.runEquilibrium_iff

theorem frozen_multiple_equilibria (B : Bank) {γ : ℝ} (hγ : 1 < γ)
    (hr : B.r₁ = c1star B.lam B.R γ) : B.GoodEquilibrium ∧ B.RunEquilibrium :=
  B.multiple_equilibria hγ hr

theorem frozen_suspension_waiting_strictly_better (B : Bank)
    (h : B.r₁ * (1 - B.lam + B.lam * B.R) < B.R) {f : ℝ} (hf : B.lam ≤ f) :
    B.suspensionEarlyPay f < B.latePay B.lam :=
  B.suspension_waiting_strictly_better h hf

end DiamondDybvig

section DMP
open Econ.DMP

theorem frozen_steadyState_unemployment {s f u : ℝ} (hsf : 0 < s + f) :
    flow s f u = u ↔ u = s / (s + f) :=
  steadyState_unemployment hsf

theorem frozen_tendsto_unemployment {s f : ℝ} (h0 : 0 < s + f) (h2 : s + f < 2) (u₀ : ℝ) :
    Tendsto (fun t : ℕ => (flow s f)^[t] u₀) atTop (𝓝 (s / (s + f))) :=
  tendsto_unemployment h0 h2 u₀

theorem frozen_jc_iff_textbook (E : Economy) {r β θ : ℝ} (hθ : 0 < θ) (hr : 0 ≤ r) :
    E.jc r β θ = (1 - β) * (E.y - E.b) ↔
      E.c / E.fillRate θ = (E.y - ((1 - β) * E.b + β * (E.y + E.c * θ))) / (r + E.s) :=
  E.jc_iff_textbook hθ hr

theorem frozen_existsUnique_equilibrium (E : Economy) {r β : ℝ} (hr : 0 ≤ r) (hβ₀ : 0 ≤ β)
    (hβ₁ : β < 1) : ∃! θ, E.IsEquilibrium r β θ :=
  E.existsUnique_equilibrium hr hβ₀ hβ₁

theorem frozen_equilibrium_strictAnti_β (E : Economy) {r β₁ β₂ θ₁ θ₂ : ℝ} (hr : 0 ≤ r)
    (hβ₁ : 0 ≤ β₁) (hβ : β₁ < β₂) (h₁ : E.IsEquilibrium r β₁ θ₁) (h₂ : E.IsEquilibrium r β₂ θ₂) :
    θ₂ < θ₁ :=
  E.equilibrium_strictAnti_β hr hβ₁ hβ h₁ h₂

theorem frozen_beveridge (E : Economy) {θ θ' : ℝ} (hθ : 0 < θ) (hlt : θ < θ') :
    E.unemp θ' < E.unemp θ ∧ E.vac θ < E.vac θ' :=
  E.beveridge hθ hlt

theorem frozen_welfare_eq (E : Economy) {θ : ℝ} (hθ : 0 ≤ θ) :
    E.welfare θ = E.y * (1 - E.unemp θ) + E.b * E.unemp θ - E.c * θ * E.unemp θ :=
  E.welfare_eq hθ

theorem frozen_isEfficient_iff (E : Economy) {θ : ℝ} :
    E.IsEfficient θ ↔ E.IsEquilibrium 0 E.η θ :=
  E.isEfficient_iff

theorem frozen_hosios (E : Economy) {β θ : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (h : E.IsEquilibrium 0 β θ) : E.IsEfficient θ ↔ β = E.η :=
  E.hosios hβ₀ hβ₁ h

end DMP

section Hulten
open Econ.Hulten

theorem frozen_horizontal_ce_eq {ι : Type*} [Fintype ι] (H : Horizontal ι) {p : ι → ℝ} {w Y : ℝ}
    {l : ι → ℝ} (h : H.IsCE p w Y l) :
    (∀ i, l i = H.a i) ∧ Y = H.maxOutput ∧ w = Y :=
  H.ce_eq h

theorem frozen_horizontal_domar {ι : Type*} [Fintype ι] (H : Horizontal ι) {p : ι → ℝ} {w Y : ℝ}
    {l : ι → ℝ} (h : H.IsCE p w Y l) (i : ι) :
    p i * (H.A i * l i) / Y = H.a i :=
  H.domar h i

theorem frozen_horizontal_hulten {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Horizontal ι)
    {p : ι → ℝ} {w Y : ℝ} {l : ι → ℝ} (h : H.IsCE p w Y l)
    (i : ι) {pt : ℝ → ι → ℝ} {wt Yt : ℝ → ℝ} {lt : ℝ → ι → ℝ}
    (ht : ∀ t, (H.shock i t).IsCE (pt t) (wt t) (Yt t) (lt t)) :
    HasDerivAt (fun t => log (Yt t)) (p i * (H.A i * l i) / Y) 0 :=
  H.hulten h i ht

theorem frozen_vertical_ce_eq (V : Vertical) {p₁ w Y l₁ : ℝ} (h : V.IsCE p₁ w Y l₁) :
    l₁ = V.ω ∧ Y = V.maxOutput ∧ w = Y :=
  V.ce_eq h

theorem frozen_vertical_domar (V : Vertical) {p₁ w Y l₁ : ℝ} (h : V.IsCE p₁ w Y l₁) :
    p₁ * (V.A₁ * l₁) / w = V.ω ∧ Y / w = 1 ∧ 1 < p₁ * (V.A₁ * l₁) / w + Y / w :=
  V.domar h

theorem frozen_vertical_hulten (V : Vertical) {p₁ w Y l₁ : ℝ} (h : V.IsCE p₁ w Y l₁) :
    HasDerivAt (fun t => log ({ V with A₁ := V.A₁ * exp t, hA₁ := mul_pos V.hA₁ (exp_pos t) } :
        Vertical).maxOutput) (p₁ * (V.A₁ * l₁) / w) 0 ∧
    HasDerivAt (fun t => log ({ V with A₂ := V.A₂ * exp t, hA₂ := mul_pos V.hA₂ (exp_pos t) } :
        Vertical).maxOutput) (Y / w) 0 :=
  V.hulten h

end Hulten

end Econ.Audit
