/-
# Frozen statements: Campbell–Shiller and long-run risk

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-25; see `Audit/REVIEW-macro-batch18.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Finance.CampbellShiller
public import EconLean.Finance.LongRunRisk

@[expose] public section

namespace Econ.Audit

theorem frozen_cs_pd_eq {k ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {pd dd r : ℕ → ℝ}
    (h : Econ.CampbellShiller.Identity k ρ pd dd r) (hpd : Econ.CampbellShiller.Bdd pd)
    (hdd : Econ.CampbellShiller.Bdd dd) (t : ℕ) :
    pd t = k / (1 - ρ) + ∑' j, ρ ^ j * dd (t + 1 + j) - ∑' j, ρ ^ j * r (t + 1 + j) :=
  Econ.CampbellShiller.pd_eq hρ0 hρ1 h hpd hdd t

theorem frozen_cs_var_decomp {Ω : Type*} [Fintype Ω] {k ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (p : Ω → ℝ) (hp : Econ.CampbellShiller.IsProb p) {pd dd r : Ω → ℕ → ℝ}
    (h : ∀ ω, Econ.CampbellShiller.Identity k ρ (pd ω) (dd ω) (r ω))
    (hpd : ∀ ω, Econ.CampbellShiller.Bdd (pd ω)) (hdd : ∀ ω, Econ.CampbellShiller.Bdd (dd ω))
    (t : ℕ) :
    Econ.CampbellShiller.cov p (fun ω => pd ω t) (fun ω => pd ω t) =
      Econ.CampbellShiller.cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * dd ω (t + 1 + j)) -
        Econ.CampbellShiller.cov p (fun ω => pd ω t) (fun ω => ∑' j, ρ ^ j * r ω (t + 1 + j)) :=
  Econ.CampbellShiller.var_decomp hρ0 hρ1 p hp h hpd hdd t

theorem frozen_lrr_euler_forces_A₁ (P : Econ.LongRunRisk.Params) (lδ μ κ₀ A₀ a V : ℝ)
    (h : ∀ x, P.logEuler lδ μ κ₀ A₀ a x + V = 0) : a = P.A₁ :=
  P.euler_forces_A₁ lδ μ κ₀ A₀ a V h

theorem frozen_lrr_sdf_innov (P : Econ.LongRunRisk.Params) (ε e : ℝ) :
    P.mInnov ε e = -P.γ * P.σ * ε - P.lamE * P.σ * e :=
  P.sdf_innov ε e

theorem frozen_lrr_lamE_pos_iff (P : Econ.LongRunRisk.Params) (hφ : 0 < P.φe) :
    0 < P.lamE ↔ 1 / P.ψ < P.γ :=
  P.lamE_pos_iff hφ

theorem frozen_lrr_wealth_premium_gt (P : Econ.LongRunRisk.Params) (hφ : 0 < P.φe)
    (hpos : 1 / P.ψ < P.γ) (hψ1 : 1 < P.ψ) :
    P.γ * P.σ ^ 2 < P.premium 1 (P.κ₁ * P.A₁ * P.φe) :=
  P.wealth_premium_gt hφ hpos hψ1

theorem frozen_lrr_byCalibration :
    17 < Econ.LongRunRisk.Params.byCalibration.lamE ∧
      Econ.LongRunRisk.Params.byCalibration.lamE < 172 / 10 ∧
      0 < Econ.LongRunRisk.Params.byCalibration.A₁ :=
  Econ.LongRunRisk.Params.byCalibration_lamE

end Econ.Audit
