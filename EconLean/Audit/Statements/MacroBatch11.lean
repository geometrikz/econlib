/-
# Frozen statements: CAPM, Modigliani–Miller, THANK, the Friedman rule in a
# cash-in-advance economy

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-24; see `Audit/REVIEW-macro-batch11.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Finance.CAPM
public import EconLean.Finance.ModiglianiMiller
public import EconLean.Macro.NK.THANK
public import EconLean.Macro.Monetary.CashInAdvance

@[expose] public section

namespace Econ.Audit

open Finset

theorem frozen_capm_beta_pricing {σ : Type*} [Fintype σ] (P : Econ.CAPM.Prob σ)
    {m Rm R : σ → ℝ} {a b Rf : ℝ} (hm : Econ.CAPM.Prob.IsLinearSDF m Rm a b)
    (hRf : P.E m * Rf = 1) (hR : P.Prices m R) (hRm : P.Prices m Rm) (hvar : P.Var Rm ≠ 0) :
    P.E R - Rf = P.Cov R Rm / P.Var Rm * (P.E Rm - Rf) :=
  P.beta_pricing hm hRf hR hRm hvar

theorem frozen_capm_of_quadratic {σ : Type*} [Fintype σ] (P : Econ.CAPM.Prob σ)
    {Rm R : σ → ℝ} {β κ W c₀ Rf : ℝ} (hc₀ : c₀ < κ) (hβ : 0 < β) (hW : 0 < W) (hRf0 : 0 < Rf)
    (hRf : P.E (Econ.CAPM.Prob.quadSDF β κ W c₀ Rm) * Rf = 1)
    (hR : P.Prices (Econ.CAPM.Prob.quadSDF β κ W c₀ Rm) R)
    (hRm : P.Prices (Econ.CAPM.Prob.quadSDF β κ W c₀ Rm) Rm) (hvar : 0 < P.Var Rm) :
    P.E R - Rf = P.Cov R Rm / P.Var Rm * (P.E Rm - Rf) ∧ Rf < P.E Rm :=
  P.capm_of_quadratic hc₀ hβ hW hRf0 hRf hR hRm hvar

theorem frozen_mm_I_market {σ ι : Type*} [Fintype σ] [Fintype ι]
    (M : Econ.AssetPricing.Market σ ι) (hna : M.NoArbitrage) (hX hd he : ι → ℝ)
    (hsplit : ∀ s, M.payoff hd s + M.payoff he s = M.payoff hX s) :
    M.cost hd + M.cost he = M.cost hX :=
  Econ.MM.mm_I_market M hna hX hd he hsplit

theorem frozen_mm_II {σ : Type*} [Fintype σ] (m X π : σ → ℝ) (F : ℝ)
    (hD : Econ.MM.value m (Econ.MM.debt F X) ≠ 0) (hE : Econ.MM.value m (Econ.MM.equity F X) ≠ 0)
    (hV : Econ.MM.value m X ≠ 0) :
    (∑ s, π s * Econ.MM.equity F X s) / Econ.MM.value m (Econ.MM.equity F X) =
      (∑ s, π s * X s) / Econ.MM.value m X +
        ((∑ s, π s * X s) / Econ.MM.value m X -
          (∑ s, π s * Econ.MM.debt F X s) / Econ.MM.value m (Econ.MM.debt F X)) *
          (Econ.MM.value m (Econ.MM.debt F X) / Econ.MM.value m (Econ.MM.equity F X)) :=
  Econ.MM.mm_II m X π F hD hE hV

theorem frozen_thank_aggregate_IS (P : Econ.THANK.Params) {y cS cH r rn : ℕ → ℝ}
    (h : P.IsEq y cS cH r rn) (t : ℕ) : y t = y (t + 1) - P.δ * P.σ * (r t - rn t) :=
  P.aggregate_IS h t

theorem frozen_thank_amplification_iff (P : Econ.THANK.Params) (hlam : 0 < P.lam) :
    1 < P.δ ↔ 1 < P.χ :=
  P.amplification_iff hlam

theorem frozen_cia_existsUnique_eq (E : Econ.CIA.Env) {i : ℝ} (hi : 0 ≤ i) :
    ∃! c, E.IsEq i c :=
  E.existsUnique_eq hi

theorem frozen_cia_efficient_iff (E : Econ.CIA.Env) {c : ℝ} : E.IsEfficient c ↔ E.IsEq 0 c :=
  E.efficient_iff

theorem frozen_cia_friedman_rule_μ (E : Econ.CIA.Env) {μ β c : ℝ} (hβ : 0 < β)
    (hμ : β - 1 ≤ μ) (h : E.IsEqμ μ β c) : E.IsEfficient c ↔ μ = β - 1 :=
  E.friedman_rule_μ hβ hμ h

end Econ.Audit

end
