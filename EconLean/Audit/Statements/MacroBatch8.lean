/-
# Frozen statements: Kiyotaki–Wright, Lagos–Wright and the Friedman rule,
# Kiyotaki–Moore amplification, costly state verification

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-23; see `Audit/REVIEW-macro-batch8.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.MoneySearch.KiyotakiWright
public import EconLean.Macro.MoneySearch.LagosWright
public import EconLean.Macro.Credit.KiyotakiMoore
public import EconLean.Macro.Credit.CostlyStateVerification

@[expose] public section

namespace Econ.Audit

open Finset

theorem frozen_kw_nonmonetary (P : Econ.KiyotakiWright.Params) : P.IsEq 0 :=
  P.nonmonetary

theorem frozen_kw_monetary_iff (P : Econ.KiyotakiWright.Params) :
    P.IsEq 1 ↔ P.r * P.c ≤ P.α * P.x * (1 - P.M) * (1 - P.x) * (P.u - P.c) :=
  P.monetary_iff

theorem frozen_kw_no_money_with_double_coincidence (P : Econ.KiyotakiWright.Params)
    (hx : P.x = 1) : ¬ P.IsEq 1 :=
  P.no_money_with_double_coincidence hx

theorem frozen_kw_mixed_iff (P : Econ.KiyotakiWright.Params) :
    (∃ acc, P.IsMixedEq acc) ↔ P.r * P.c < P.α * P.x * (1 - P.M) * (1 - P.x) * (P.u - P.c) :=
  P.mixed_iff

theorem frozen_lw_isOptimal_iff (E : Econ.LagosWright.Env) (i : ℝ) {q : ℝ} (hq : 0 < q) :
    E.IsOptimal i q ↔ E.σ * (E.du q - 1) = i :=
  E.isOptimal_iff i hq

theorem frozen_lw_exists_optimal (E : Econ.LagosWright.Env) {i a : ℝ} (hi : 0 ≤ i) (ha : 0 < a)
    (hai : i < E.σ * (E.du a - 1)) : ∃ q, E.IsOptimal i q :=
  E.exists_optimal hi ha hai

theorem frozen_lw_antitone_in_i (E : Econ.LagosWright.Env) {i₁ i₂ q₁ q₂ : ℝ} (hi : i₁ < i₂)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (h₁ : E.IsOptimal i₁ q₁) (h₂ : E.IsOptimal i₂ q₂) :
    q₂ < q₁ :=
  E.antitone_in_i hi hq₁ hq₂ h₁ h₂

theorem frozen_lw_friedman_rule (E : Econ.LagosWright.Env) {i q : ℝ} (hi : 0 < i) (hq : 0 < q)
    (h : E.IsOptimal i q) :
    E.σ * (E.u q - q) < E.σ * (E.u E.qs - E.qs) ∧ E.IsOptimal 0 E.qs :=
  E.friedman_rule hi hq h

theorem frozen_km_existsUnique_eq (P : Econ.KiyotakiMoore.Params) (a : ℝ) :
    ∃! kq : ℝ × ℝ, P.IsEq a kq.1 kq.2 :=
  P.existsUnique_eq a

theorem frozen_km_amplification (P : Econ.KiyotakiMoore.Params) (hφ : 0 < P.φ)
    {a a' k k' q q' : ℝ} (ha : a < a') (h : P.IsEq a k q) (h' : P.IsEq a' k' q') :
    P.Kbar * (a' - a) / P.d < k' - k :=
  P.amplification hφ ha h h'

theorem frozen_csv_debt_isIC (S : Finset ℝ) (D : ℝ) :
    Econ.CSV.LL S (Econ.CSV.debt D) ∧ Econ.CSV.IsIC S (Econ.CSV.debt D) :=
  Econ.CSV.debt_isIC S D

theorem frozen_csv_debt_optimal {S : Finset ℝ} (hne : S.Nonempty) {p : ℝ → ℝ}
    (hp : ∀ ω ∈ S, 0 ≤ p ω) {κ : ℝ} (hκ : 0 ≤ κ) {C : Econ.CSV.Contract}
    (hLL : Econ.CSV.LL S C) (hIC : Econ.CSV.IsIC S C) :
    ∃ D, Econ.CSV.expRepay S p (Econ.CSV.debt D) = Econ.CSV.expRepay S p C ∧
      Econ.CSV.expVerif S p κ (Econ.CSV.debt D) ≤ Econ.CSV.expVerif S p κ C :=
  Econ.CSV.debt_optimal hne hp hκ hLL hIC

theorem frozen_csv_debt_optimal_pc {S : Finset ℝ} (hne : S.Nonempty) {p : ℝ → ℝ}
    (hp : ∀ ω ∈ S, 0 ≤ p ω) {κ I : ℝ} (hκ : 0 ≤ κ) {C : Econ.CSV.Contract}
    (hLL : Econ.CSV.LL S C) (hIC : Econ.CSV.IsIC S C) (hPC : Econ.CSV.LenderPC S p κ I C) :
    ∃ D, Econ.CSV.LL S (Econ.CSV.debt D) ∧ Econ.CSV.IsIC S (Econ.CSV.debt D) ∧
      Econ.CSV.LenderPC S p κ I (Econ.CSV.debt D) ∧
      Econ.CSV.entPayoff S p (Econ.CSV.debt D) = Econ.CSV.entPayoff S p C :=
  Econ.CSV.debt_optimal_pc hne hp hκ hLL hIC hPC

end Econ.Audit

end
