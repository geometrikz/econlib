/-
# Frozen statements: the Saez top rate, the inverse Euler equation,
# granular fluctuations, rare disasters

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-24; see `Audit/REVIEW-macro-batch12.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.PublicFinance.SaezTopRate
public import EconLean.Macro.PublicFinance.InverseEuler
public import EconLean.Macro.Granularity
public import EconLean.Finance.RareDisasters

@[expose] public section

namespace Econ.Audit

open Finset

theorem frozen_saez_dSW_eq_zero_iff (P : Econ.Saez.Params) {τ : ℝ} (hτ : τ < 1) :
    P.dSW τ = 0 ↔ τ = P.topRate :=
  P.dSW_eq_zero_iff hτ

theorem frozen_saez_welfare_hasDerivAt {Z V : ℝ → ℝ} {τ e g zs : ℝ}
    (hZ : HasDerivAt Z (-(e * Z τ / (1 - τ))) τ) (hV : HasDerivAt V (-(Z τ - zs)) τ) :
    HasDerivAt (fun t => t * (Z t - zs) + g * V t)
      ((1 - g) * (Z τ - zs) - e * Z τ * τ / (1 - τ)) τ :=
  Econ.Saez.Params.welfare_hasDerivAt hZ hV

theorem frozen_saez_topRate_isMaxOn (P : Econ.Saez.Params) :
    IsMaxOn P.welfare (Set.Ico 0 1) P.topRate :=
  P.topRate_isMaxOn

theorem frozen_inverse_euler {ι : Type*} (s : Finset ι) {h h' : ℝ → ℝ} {β R v₀ : ℝ}
    {π v : ι → ℝ} (hβ : β ≠ 0) (hR : R ≠ 0)
    (hd₀ : HasDerivAt h (h' v₀) v₀) (hd : ∀ i ∈ s, HasDerivAt h (h' (v i)) (v i))
    (hmin : IsLocalMin (Econ.InverseEuler.perturbCost s h β R v₀ π v) 0) :
    h' v₀ = 1 / (β * R) * ∑ i ∈ s, π i * h' (v i) :=
  Econ.InverseEuler.inverse_euler s hβ hR hd₀ hd hmin

theorem frozen_inverse_euler_utility_neutral {ι : Type*} (s : Finset ι) {β v₀ : ℝ}
    {π v : ι → ℝ} (hβ : β ≠ 0) (h1 : ∑ i ∈ s, π i = 1) (Δ : ℝ) :
    (v₀ - Δ) + β * ∑ i ∈ s, π i * (v i + Δ / β) = v₀ + β * ∑ i ∈ s, π i * v i :=
  Econ.InverseEuler.utility_neutral s hβ h1 Δ

theorem frozen_inverse_euler_wedge {ι : Type*} (s : Finset ι) {h h' : ℝ → ℝ} {β R v₀ : ℝ}
    {π v : ι → ℝ} (hπ : ∀ i ∈ s, 0 ≤ π i) (h1 : ∑ i ∈ s, π i = 1) (hβR : 0 < β * R)
    (hh'₀ : 0 < h' v₀) (hh' : ∀ i ∈ s, 0 < h' (v i))
    (hd₀ : HasDerivAt h (h' v₀) v₀) (hd : ∀ i ∈ s, HasDerivAt h (h' (v i)) (v i))
    (hmin : IsLocalMin (Econ.InverseEuler.perturbCost s h β R v₀ π v) 0) :
    1 / h' v₀ ≤ β * R * ∑ i ∈ s, π i * (1 / h' (v i)) ∧
      (∀ k ∈ s, ∀ l ∈ s, 0 < π k → 0 < π l → h' (v k) ≠ h' (v l) →
        1 / h' v₀ < β * R * ∑ i ∈ s, π i * (1 / h' (v i))) :=
  Econ.InverseEuler.inverse_euler_wedge s hπ h1 hβR hh'₀ hh' hd₀ hd hmin

theorem frozen_granular_var_agg {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]
    (P : Econ.CAPM.Prob σ) (s : ι → ℝ) (ε : ι → σ → ℝ) {v : ℝ}
    (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    P.Var (Econ.Granular.agg s ε) = v * ∑ i, s i ^ 2 :=
  Econ.Granular.var_agg P s ε hmean hcov

theorem frozen_granular_var_equal {σ : Type*} [Fintype σ] (P : Econ.CAPM.Prob σ) {N : ℕ}
    (hN : 0 < N) (ε : Fin N → σ → ℝ) {v : ℝ} (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    P.Var (Econ.Granular.agg (fun _ => 1 / (N : ℝ)) ε) = v / N :=
  Econ.Granular.var_equal P hN ε hmean hcov

theorem frozen_granular_var_zipf_ge {σ : Type*} [Fintype σ] (P : Econ.CAPM.Prob σ) {N : ℕ}
    (hN : 0 < N) (ε : Fin N → σ → ℝ) {v : ℝ} (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    v / (1 + Real.log N) ^ 2 ≤ P.Var (Econ.Granular.agg (Econ.Granular.zipf N) ε) :=
  Econ.Granular.var_zipf_ge P hN ε hmean hcov

theorem frozen_disasters_premium_pos (P : Econ.Disasters.Params) (hp : 0 < P.p) :
    P.Rf < P.ERe :=
  P.premium_pos hp

theorem frozen_disasters_riskfree_anti_p (P P' : Econ.Disasters.Params) (hb : P'.b = P.b)
    (hg : P'.g = P.g) (hγ : P'.γ = P.γ) (hβ : P'.β = P.β) (hpp : P.p < P'.p) :
    P'.Rf < P.Rf :=
  P.riskfree_anti_p P' hb hg hγ hβ hpp

end Econ.Audit
