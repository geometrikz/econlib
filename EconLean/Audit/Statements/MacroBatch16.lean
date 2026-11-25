/-
# Frozen statements: Lagos–Wright bargaining, dynamic Kiyotaki–Moore, Lucas–Stokey

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-25; see `Audit/REVIEW-macro-batch16.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.MoneySearch.LagosWrightBargaining
public import EconLean.Macro.Credit.DynamicKM
public import EconLean.Macro.PublicFinance.LucasStokey

@[expose] public section

namespace Econ.Audit

open Set

theorem frozen_lw_hasDerivAt_nashPay (E : Econ.LagosWright.Env) (θ : ℝ) {d2 : ℝ}
    (hd2 : HasDerivAt E.du d2 E.qs) :
    HasDerivAt (E.nashPay θ) (1 + θ * (1 - θ) * d2 * (E.qs - E.u E.qs)) E.qs :=
  E.hasDerivAt_nashPay θ hd2

theorem frozen_lw_holdup (E : Econ.LagosWright.Env) {θ i d2 : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hi : 0 ≤ i) (hd2 : HasDerivAt E.du d2 E.qs) (hd2neg : d2 < 0)
    (hsurplus : E.qs < E.u E.qs) :
    ¬ IsLocalMax (E.nashObj θ i) E.qs :=
  E.holdup hθ hθ1 hi hd2 hd2neg hsurplus

theorem frozen_lw_holdup_lt (E : Econ.LagosWright.Env) {θ i d2 q : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hi : 0 ≤ i) (hd2 : HasDerivAt E.du d2 E.qs) (hd2neg : d2 < 0)
    (hsurplus : E.qs < E.u E.qs) (hq : q ∈ Ioc 0 E.qs)
    (hbest : ∀ z ∈ Ioc 0 E.qs, E.nashObj θ i z ≤ E.nashObj θ i q) :
    q < E.qs :=
  E.holdup_lt hθ hθ1 hi hd2 hd2neg hsurplus hq hbest

theorem frozen_lw_kalai_friedman (E : Econ.LagosWright.Env) {θ q : ℝ} (hθ : 0 < θ)
    (hq : 0 < q) (hmax : IsLocalMax (E.kalaiObj θ 0) q) : q = E.qs :=
  E.kalai_friedman hθ hq hmax

theorem frozen_lw_kalai_friedman_attained (E : Econ.LagosWright.Env) {θ : ℝ} (hθ : 0 < θ)
    {z : ℝ} (hz : 0 < z) : E.kalaiObj θ 0 z ≤ E.kalaiObj θ 0 E.qs :=
  E.kalai_friedman_attained hθ hz

theorem frozen_lw_kalai_lt_star (E : Econ.LagosWright.Env) {θ i q : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hi : 0 < i) (hq : 0 < q) (hdu : 0 ≤ E.du q)
    (hmax : IsLocalMax (E.kalaiObj θ i) q) : q < E.qs :=
  E.kalai_lt_star hθ hθ1 hi hq hdu hmax

theorem frozen_lw_kalai_mono_theta (E : Econ.LagosWright.Env) {θ₁ θ₂ i q₁ q₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ : θ₁ < θ₂) (hθ₂ : θ₂ ≤ 1) (hi : 0 < i) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hdu₁ : 0 ≤ E.du q₁) (h₁ : IsLocalMax (E.kalaiObj θ₁ i) q₁)
    (h₂ : IsLocalMax (E.kalaiObj θ₂ i) q₂) : q₁ < q₂ :=
  E.kalai_mono_theta hθ₁ hθ hθ₂ hi hq₁ hq₂ hdu₁ h₁ h₂

theorem frozen_dkm_price_eq (P : Econ.DynamicKM.Params) {k q : ℕ → ℝ} (hk : P.HoldingsEq k)
    (hq : P.PriceEq k q) (hb : ∃ M, ∀ t, |q t| ≤ M) (t : ℕ) : q t = P.φ * k t :=
  P.price_eq hk hq hb t

theorem frozen_dkm_amplification (P : Econ.DynamicKM.Params) (hstab : P.Kbar * P.φ < P.d)
    (hlam : 0 < P.lam) {Δa : ℝ} (hΔ : 0 < Δa) {k q : ℕ → ℝ} (hk : P.HoldingsEq k)
    (hq : P.PriceEq k q) (hb : ∃ M, ∀ t, |q t| ≤ M) (h : P.ImpactEq Δa (k 0) (q 0)) :
    P.Kbar * Δa / P.d < P.Kbar * Δa / (P.d - P.Kbar * P.ψ) ∧
      P.Kbar * Δa / (P.d - P.Kbar * P.ψ) < k 0 :=
  P.amplification hstab hlam hΔ hk hq hb h

theorem frozen_dkm_φ_strictMono (P P' : Econ.DynamicKM.Params) (hψ : P'.ψ = P.ψ)
    (hR : P'.R = P.R) (hlam : P.lam < P'.lam) : P.φ < P'.φ :=
  P.φ_strictMono P' hψ hR hlam

theorem frozen_ls_tax_smoothing {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ℕ} (hγ : 1 ≤ γ)
    {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n)
    (hmax : IsLocalMaxOn (Econ.LucasStokey.welfare γ w g)
      {l | Econ.LucasStokey.implement γ w g l = Econ.LucasStokey.implement γ w g l₀} l₀) :
    ∃ τ : ℝ, ∀ n, Econ.LucasStokey.tax γ l₀ n = τ :=
  Econ.LucasStokey.tax_smoothing hγ hw hmax

theorem frozen_ls_first_best {ι : Type*} [Fintype ι] (γ : ℕ) {w g : ι → ℝ}
    (hw : ∀ n, 0 ≤ w n) :
    IsLocalMaxOn (Econ.LucasStokey.welfare γ w g)
      {l | Econ.LucasStokey.implement γ w g l = Econ.LucasStokey.implement γ w g 1} 1 ∧
      ∀ n, Econ.LucasStokey.tax γ (1 : ι → ℝ) n = 0 :=
  Econ.LucasStokey.first_best γ hw

end Econ.Audit
