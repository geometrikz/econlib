/-
# Frozen statements: Lucas islands, Morris–Shin, Burdett–Mortensen,
# the BGG external finance premium

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-23; see `Audit/REVIEW-macro-batch9.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Information.LucasIslands
public import EconLean.Macro.Information.MorrisShin
public import EconLean.Macro.Labor.BurdettMortensen
public import EconLean.Macro.Credit.ExternalFinancePremium

@[expose] public section

namespace Econ.Audit

open Set Filter Topology

theorem frozen_lucas_mse_theta_lt (P : Econ.LucasIslands.Params) {θ : ℝ} (hθ : θ ≠ P.theta) :
    P.mse P.theta < P.mse θ :=
  P.mse_theta_lt hθ

theorem frozen_lucas_output_eq (P : Econ.LucasIslands.Params) {m p : ℝ} (h : P.IsEqPrice m p) :
    m - p = P.b * P.theta / (1 + P.b * P.theta) * (m - P.pbar) :=
  P.output_eq h

theorem frozen_lucas_output_zero_iff (P : Econ.LucasIslands.Params) {m p : ℝ}
    (h : P.IsEqPrice m p) : m - p = 0 ↔ m = P.pbar :=
  P.output_zero_iff h

theorem frozen_lucas_slope_anti (P P' : Econ.LucasIslands.Params) (hz : P'.Vz = P.Vz)
    (hb : P'.b = P.b) (hp : P.Vp < P'.Vp) : P'.b * P'.theta < P.b * P.theta :=
  P.slope_anti P' hz hb hp

theorem frozen_ms_isEqWeight_iff {r α β : ℝ} (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) (κ : ℝ) :
    Econ.MorrisShin.IsEqWeight r α β κ ↔ κ = Econ.MorrisShin.kappa r α β :=
  Econ.MorrisShin.isEqWeight_iff hr hα hβ κ

theorem frozen_ms_loss_eq {r α β : ℝ} (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    Econ.MorrisShin.lossOf α β (Econ.MorrisShin.kappa r α β) = Econ.MorrisShin.loss r α β :=
  Econ.MorrisShin.loss_eq hr hα hβ

theorem frozen_ms_public_info_harmful_iff {r α β : ℝ} (hr : r < 1) (hα : 0 < α) (hβ : 0 < β) :
    0 < deriv (fun a => Econ.MorrisShin.loss r a β) α ↔ α < β * (1 - r) * (2 * r - 1) :=
  Econ.MorrisShin.public_info_harmful_iff hr hα hβ

theorem frozen_ms_private_info_helps {r α β : ℝ} (hr : r < 1) (hα : 0 < α) (hβ : 0 < β)
    (hr0 : -1 < r) : deriv (fun b => Econ.MorrisShin.loss r α b) β < 0 :=
  Econ.MorrisShin.private_info_helps hr hα hβ hr0

theorem frozen_bm_isEquilibrium (P : Econ.BurdettMortensen.Params) :
    (∀ w, (P.p - w) * P.l w ≤ (P.p - P.b) * P.l P.b) ∧
      ∀ w ∈ Icc P.b P.wbar, (P.p - w) * P.l w = (P.p - P.b) * P.l P.b :=
  P.isEquilibrium

theorem frozen_bm_dispersion (P : Econ.BurdettMortensen.Params) :
    P.b < P.wbar ∧ P.wbar < P.p ∧ P.F P.b = 0 ∧ P.F P.wbar = 1 :=
  ⟨P.b_lt_wbar, P.wbar_lt_p, P.F_b, P.F_wbar⟩

theorem frozen_bm_tendsto_wbar_zero {δ p b : ℝ} (hδ : 0 < δ) :
    Tendsto (fun lam => Econ.BurdettMortensen.wbarOf δ lam p b) (𝓝[>] 0) (𝓝 b) :=
  Econ.BurdettMortensen.tendsto_wbar_zero hδ

theorem frozen_bgg_efp_eq_one_iff (S : Econ.BGG.Schedule) {L D : ℝ} (hL : 0 < L)
    (h : S.IsFace L D) : S.efp L D = 1 ↔ S.m D = 0 :=
  S.efp_eq_one_iff hL h

theorem frozen_bgg_efp_anti_netWorth {μ : ℝ} (hμ : 0 < μ) {I N N' D D' : ℝ} (hNN : N < N')
    (hN' : N' < I) (h : (Econ.BGG.uniform μ hμ.le).IsFace (I - N) D)
    (h' : (Econ.BGG.uniform μ hμ.le).IsFace (I - N') D') :
    (Econ.BGG.uniform μ hμ.le).efp (I - N') D' < (Econ.BGG.uniform μ hμ.le).efp (I - N) D :=
  Econ.BGG.uniform_efp_anti_netWorth hμ hNN hN' h h'

end Econ.Audit

end
