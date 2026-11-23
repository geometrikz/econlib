/-
# Frozen statements: golden rule, technical progress, Diamond and Samuelson OLG

Headline statements of `Macro/Growth/GoldenRule.lean`,
`Macro/Growth/TechProgress.lean`, `Macro/OLG/LogHousehold.lean`,
`Macro/OLG/Diamond.lean` and `Macro/OLG/Samuelson.lean`, copied verbatim after
two rounds of context-isolated adversarial review (2026-11-23; verdicts:
faithful, or faithful with documented deviation; see
`Audit/REVIEW-growth-olg.md`). Each is closed by the library theorem, so if a
library statement is weakened this file stops compiling. Lightweight stand-in
for `leanprover/comparator`. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Growth.GoldenRule
public import EconLean.Macro.Growth.TechProgress
public import EconLean.Macro.OLG.Diamond
public import EconLean.Macro.OLG.Samuelson

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ.Solow Econ.OLG

theorem frozen_goldenRule_lt {f : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Ici 0) f) {c kg k : ℝ}
    (hkg : 0 ≤ kg) (hd : HasDerivAt f c kg) (hk : 0 ≤ k) (hne : k ≠ kg) :
    f k - c * k < f kg - c * kg :=
  goldenRule_lt hconc hkg hd hk hne

theorem frozen_consumption_le_goldenRule (E : Economy) {kg : ℝ} (hkg : 0 < kg)
    (hd : HasDerivAt E.f (E.n + E.δ) kg) {k : ℝ} (hs : E.IsSteadyState k) :
    (1 - E.s) * E.f k ≤ E.f kg - (E.n + E.δ) * kg :=
  E.consumption_le_goldenRule hkg hd hs

theorem frozen_isSteadyState_goldenRule (E : Economy) {kg : ℝ} (hkg : 0 < kg)
    (hd : HasDerivAt E.f (E.n + E.δ) kg) :
    (E.withGoldenSaving hkg hd).IsSteadyState kg :=
  E.isSteadyState_goldenRule hkg hd

theorem frozen_cobbDouglas_goldenSavingRate (E : Economy) {α : ℝ} (hα₁ : α < 1)
    (hf : E.f = fun k => k ^ α) (hα₀ : 0 < α) :
    E.goldenSavingRate ((α / (E.n + E.δ)) ^ (1 / (1 - α))) = α :=
  cobbDouglas_goldenSavingRate E hα₁ hf hα₀

theorem frozen_tech_tendsto_effective (T : TechEconomy) {kstar K₀ A₀ L₀ : ℝ}
    (hs : T.toEconomy.IsSteadyState kstar) (hK : 0 < K₀) (hA : 0 < A₀) (hL : 0 < L₀) :
    Tendsto (T.effective K₀ A₀ L₀) atTop (𝓝 kstar) :=
  T.tendsto_effective hs hK hA hL

theorem frozen_tech_tendsto_detrended_output (T : TechEconomy) {kstar K₀ A₀ L₀ : ℝ}
    (hs : T.toEconomy.IsSteadyState kstar) (hK : 0 < K₀) (hA : 0 < A₀) (hL : 0 < L₀) :
    Tendsto (fun t => T.output K₀ A₀ L₀ t / T.labor L₀ t / T.tech A₀ t) atTop
      (𝓝 (T.f kstar)) :=
  T.tendsto_detrended_output hs hK hA hL

theorem frozen_tech_balanced_growth (T : TechEconomy) {kstar K₀ A₀ L₀ : ℝ}
    (hs : T.toEconomy.IsSteadyState kstar)
    (hA : 0 < A₀) (hL : 0 < L₀) (h0 : K₀ / (A₀ * L₀) = kstar) (t : ℕ) :
    T.effective K₀ A₀ L₀ t = kstar ∧
    T.output K₀ A₀ L₀ (t + 1) / T.labor L₀ (t + 1) =
      (1 + T.g) * (T.output K₀ A₀ L₀ t / T.labor L₀ t) ∧
    T.capital K₀ A₀ L₀ (t + 1) / T.labor L₀ (t + 1) =
      (1 + T.g) * (T.capital K₀ A₀ L₀ t / T.labor L₀ t) :=
  T.balanced_growth hs hA hL h0 t

theorem frozen_saving_isOptimal_iff {β ω₁ ω₂ R a : ℝ} (hβ : 0 < β) (hR : 0 < R) (hω₁ : 0 < ω₁)
    (hω₂ : 0 ≤ ω₂) :
    IsOptimalSaving β ω₁ ω₂ R a ↔ a = (β * ω₁ - ω₂ / R) / (1 + β) :=
  saving_isOptimal_iff hβ hR hω₁ hω₂

theorem frozen_diamond_isEquilibrium_iff (D : Diamond) (k : ℕ → ℝ) (hk0 : 0 < k 0) :
    D.IsEquilibrium k ↔ ∀ t, k (t + 1) = D.next (k t) :=
  D.isEquilibrium_iff k hk0

theorem frozen_diamond_tendsto_equilibrium (D : Diamond) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : D.IsEquilibrium k) : Tendsto k atTop (𝓝 D.kstar) :=
  D.tendsto_equilibrium hk0 hk

theorem frozen_diamond_dynamicallyInefficient_iff (D : Diamond) :
    (D.rate D.kstar < 1 + D.n ↔ D.α * (1 + D.β) < D.β * (1 - D.α)) ∧
    (D.rate D.kstar < 1 + D.n ↔ D.kgold < D.kstar) :=
  D.dynamicallyInefficient_iff

theorem frozen_diamond_inefficient_iff_exists_improvement (D : Diamond) :
    D.rate D.kstar < 1 + D.n ↔
      ∃ k C : ℕ → ℝ, k 0 = D.kstar ∧ D.IsFeasible k C ∧
        (∀ t, D.kstar ^ D.α - (1 + D.n) * D.kstar ≤ C t) ∧
        ∃ t, D.kstar ^ D.α - (1 + D.n) * D.kstar < C t :=
  D.dynamicallyInefficient_iff_exists_improvement

theorem frozen_samuelson_isCompetitiveEquilibrium_iff (S : Samuelson) (R : ℕ → ℝ)
    (x : Samuelson.Allocation) :
    S.IsCompetitiveEquilibrium R x ↔ (∀ t, R t = S.autarkyRate) ∧ x = S.autarky :=
  S.isCompetitiveEquilibrium_iff R x

theorem frozen_samuelson_firstWelfareTheorem_fails (S : Samuelson) (h : S.ω₂ < S.β * S.ω₁) :
    ∃ R x, S.IsCompetitiveEquilibrium R x ∧
      ∃ y, S.IsFeasible y ∧ S.StrictlyDominates y x :=
  S.firstWelfareTheorem_fails h

theorem frozen_samuelson_isMonetaryEquilibrium_iff (S : Samuelson) {M p : ℝ} (hM : 0 < M) :
    S.IsMonetaryEquilibrium M p ↔
      S.ω₂ < S.β * S.ω₁ ∧ p = M * (1 + S.β) / (S.β * S.ω₁ - S.ω₂) :=
  S.isMonetaryEquilibrium_iff hM

theorem frozen_samuelson_monetaryEquilibrium (S : Samuelson) {M p : ℝ} (hM : 0 < M)
    (h : S.IsMonetaryEquilibrium M p) :
    S.monetaryAllocation M p = S.golden ∧ S.IsFeasible (S.monetaryAllocation M p) ∧
      S.StrictlyDominates (S.monetaryAllocation M p) S.autarky :=
  S.monetaryEquilibrium_eq_golden_and_dominates hM h

end Econ.Audit
