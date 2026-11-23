/-
# Frozen statements: Aghion–Howitt, directed technical change,
# Eaton–Kortum, Melitz

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-23; see `Audit/REVIEW-macro-batch10.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Growth.AghionHowitt
public import EconLean.Macro.Growth.DirectedTechChange
public import EconLean.Macro.Trade.EatonKortum
public import EconLean.Macro.Trade.Melitz

@[expose] public section

namespace Econ.Audit

open Set MeasureTheory

theorem frozen_ah_isEquilibrium_iff (P : Econ.AghionHowitt.Params) (n : ℝ) :
    P.IsEquilibrium n ↔ n = max 0 P.nStar :=
  P.isEquilibrium_iff n

theorem frozen_ah_growth_pos (P : Econ.AghionHowitt.Params)
    (h : P.r < P.lam * P.γ * P.θ * P.L) : 0 < P.growth P.nStar :=
  P.growth_pos h

theorem frozen_ah_scale (P P' : Econ.AghionHowitt.Params) (hlam : P'.lam = P.lam)
    (hγ : P'.γ = P.γ) (hθ : P'.θ = P.θ) (hr : P'.r = P.r) (hL : P.L < P'.L) :
    P.nStar < P'.nStar :=
  P.nStar_strictMono_L P' hlam hγ hθ hr hL

theorem frozen_dtc_isFreeEntry_iff {σ η N x : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hN : 0 < N)
    (hx : 0 < x) :
    Econ.DirectedTech.IsFreeEntry σ η N x ↔ N = Econ.DirectedTech.nStar σ η x :=
  Econ.DirectedTech.isFreeEntry_iff hσ hη hN hx

theorem frozen_dtc_strong_bias_iff {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    StrictMonoOn (fun x => Econ.DirectedTech.relWage σ (Econ.DirectedTech.nStar σ η x) x)
      (Ioi 0) ↔ 2 < σ :=
  Econ.DirectedTech.strong_bias_iff hσ hη

theorem frozen_ek_trade_share {ι : Type*} [DecidableEq ι] (s : Finset ι) (Φ : ι → ℝ)
    (hΦ : ∀ k ∈ s, 0 < Φ k) {i : ι} (hi : i ∈ s) :
    ∫ u in Ioi (0 : ℝ), Φ i * Real.exp (-(Φ i * u)) * ∏ k ∈ s.erase i, Real.exp (-(Φ k * u)) =
      Φ i / ∑ k ∈ s, Φ k :=
  Econ.EatonKortum.trade_share s Φ hΦ hi

theorem frozen_ek_priceIndex_eq {θ σ Φtot : ℝ} (hθ : 0 < θ) (hσ : σ < 1 + θ) (hσ1 : σ ≠ 1)
    (hΦ : 0 < Φtot) :
    Econ.EatonKortum.priceIndex θ σ Φtot = Econ.EatonKortum.gammaConst θ σ * Φtot ^ (-1 / θ) :=
  Econ.EatonKortum.priceIndex_eq hθ hσ hσ1 hΦ

theorem frozen_melitz_selection_iff (P : Econ.Melitz.Params) :
    1 < P.Λ ↔ P.f < P.τ ^ (P.σ - 1) * P.fx :=
  P.selection_iff

theorem frozen_melitz_J_eq (P : Econ.Melitz.Params) {φ : ℝ} (hφ : P.φmin ≤ φ) :
    P.J φ = (P.σ - 1) / (P.k - P.σ + 1) * (P.φmin / φ) ^ P.k :=
  P.J_eq hφ

theorem frozen_melitz_trade_raises_cutoff (P : Econ.Melitz.Params) {δ fe n φa φs : ℝ}
    (hn : 0 < n) (hΛ : 1 ≤ P.Λ) (ha : P.φmin ≤ φa) (hs : P.φmin ≤ φs)
    (haut : P.f * P.J φa = δ * fe)
    (hopen : P.f * P.J φs + n * P.fx * P.J (P.Λ * φs) = δ * fe) : φa < φs :=
  P.trade_raises_cutoff hn hΛ ha hs haut hopen

end Econ.Audit

end
