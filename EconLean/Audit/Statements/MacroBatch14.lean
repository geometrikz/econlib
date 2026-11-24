/-
# Frozen statements: self-enforcing wage contracts, bank runs as a global
# game, the financial accelerator

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-24; see `Audit/REVIEW-macro-batch14.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Contracts.ThomasWorrall
public import EconLean.Macro.Banking.GoldsteinPauzner
public import EconLean.Macro.Credit.FinancialAccelerator

@[expose] public section

namespace Econ.Audit

theorem frozen_tw_kkt_clamp {a b x x' μ ν : ℝ} (hab : a ≤ b) (hx' : x' = x + μ - ν)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (ha : a ≤ x') (hb : x' ≤ b) (hμc : 0 < μ → x' = a)
    (hνc : 0 < ν → x' = b) : x' = Econ.ThomasWorrall.clamp a b x :=
  Econ.ThomasWorrall.kkt_clamp hab hx' hμ hν ha hb hμc hνc

theorem frozen_tw_eventually_constant {S : Type*} (a b : S → ℝ) (s : ℕ → S) (x₀ : ℝ)
    {A B : ℝ} (hAB : A ≤ B) (ha : ∀ σ, a σ ≤ A) (hb : ∀ σ, B ≤ b σ)
    {sA sB : S} (hsA : a sA = A) (hsB : b sB = B) {tA tB : ℕ} (htA : 1 ≤ tA) (htB : 1 ≤ tB)
    (hA : s tA = sA) (hB : s tB = sB) :
    ∀ t, max tA tB ≤ t →
      Econ.ThomasWorrall.path a b s x₀ t = Econ.ThomasWorrall.path a b s x₀ (max tA tB) :=
  Econ.ThomasWorrall.eventually_constant a b s x₀ hAB ha hb hsA hsB htA htB hA hB

theorem frozen_tw_not_eventually_constant {S : Type*} (a b : S → ℝ) (s : ℕ → S) (x₀ : ℝ)
    {A B : ℝ} (hBA : B < A) (hab : ∀ σ, a σ ≤ b σ) {sA sB : S} (hsA : a sA = A)
    (hsB : b sB = B) (hA : ∀ T, ∃ t, T ≤ t ∧ 1 ≤ t ∧ s t = sA)
    (hB : ∀ T, ∃ t, T ≤ t ∧ 1 ≤ t ∧ s t = sB) :
    ¬ ∃ T c, ∀ t, T ≤ t → Econ.ThomasWorrall.path a b s x₀ t = c :=
  Econ.ThomasWorrall.not_eventually_constant a b s x₀ hBA hab hsA hsB hA hB

theorem frozen_gp_A_eq (P : Econ.GoldsteinPauzner.Params) (θ : ℝ) :
    P.A θ = P.p θ * P.R * P.I - (1 - P.r * P.lam) - Real.log P.r :=
  P.A_eq θ

theorem frozen_gp_existsUnique_threshold (P : Econ.GoldsteinPauzner.Params) {θL θH : ℝ}
    (hL : P.A θL < 0) (hH : 0 < P.A θH) : ∃! θs, P.A θs = 0 :=
  P.existsUnique_threshold hL hH

theorem frozen_gp_threshold_mono_r (P P' : Econ.GoldsteinPauzner.Params)
    (hlam : P'.lam = P.lam) (hR : P'.R = P.R) (hp : P'.p = P.p) (hrr : P.r < P'.r)
    {θs θs' : ℝ} (h : P.A θs = 0) (h' : P'.A θs' = 0) : θs < θs' :=
  P.threshold_mono_r P' hlam hR hp hrr h h'

theorem frozen_bgg_K_strictMono_N (E : Econ.BGG.Env) (hs : StrictAntiOn E.s (Set.Ioi 0))
    {A N₁ N₂ K₁ K₂ : ℝ} (hA : 0 < A) (hN₁ : 0 < N₁) (hN : N₁ < N₂) (h₁ : E.IsEq A N₁ K₁)
    (h₂ : E.IsEq A N₂ K₂) : K₁ < K₂ :=
  E.K_strictMono_N hs hA hN₁ hN h₁ h₂

theorem frozen_bgg_K_indep_N (E : Econ.BGG.Env)
    (hconst : ∀ x y, 0 < x → 0 < y → E.s x = E.s y) {A N₁ N₂ K₁ K₂ : ℝ}
    (hA : 0 < A) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (h₁ : E.IsEq A N₁ K₁) (h₂ : E.IsEq A N₂ K₂) :
    K₁ = K₂ :=
  E.K_indep_N hconst hA hN₁ hN₂ h₁ h₂

theorem frozen_bgg_amplification (E : Econ.BGG.Env) (hs : StrictAntiOn E.s (Set.Ioi 0))
    {N₀ κ A₁ A₂ K₁ K₂ K₂' : ℝ} (hA₁ : 0 < A₁) (hA : A₁ < A₂) (hκ : 0 < κ)
    (hN : 0 < N₀ + κ * A₁) (h₁ : E.IsEq A₁ (N₀ + κ * A₁) K₁) (h₂ : E.IsEq A₂ (N₀ + κ * A₂) K₂)
    (h₂' : E.IsEq A₂ (N₀ + κ * A₁) K₂') : K₁ < K₂' ∧ K₂' < K₂ :=
  E.amplification hs hA₁ hA hκ hN h₁ h₂ h₂'

end Econ.Audit
