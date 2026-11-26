/-
# Frozen statements: Rotemberg pricing and intermediary asset pricing

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-26; see `Audit/REVIEW-macro-batch19.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.NK.Rotemberg
public import EconLean.Finance.HeKrishnamurthy

@[expose] public section

namespace Econ.Audit

theorem frozen_rot_foc {β c : ℝ} (hβ : 0 < β) {T : ℕ} {p mc q : ℕ → ℝ} {m : ℕ}
    (hm : m + 2 ≤ T)
    (hmin : IsLocalMin (fun x => Econ.Rotemberg.loss β c T p mc (Function.update q (m + 1) x))
      (q (m + 1))) :
    (q (m + 1) - p (m + 1) - mc (m + 1)) + c * (q (m + 1) - q m) -
      β * c * (q (m + 2) - q (m + 1)) = 0 :=
  Econ.Rotemberg.foc hβ hm hmin

theorem frozen_rot_nkpc {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {T : ℕ} {p mc : ℕ → ℝ} {m : ℕ}
    (hm : m + 2 ≤ T)
    (hmin : IsLocalMin (fun x => Econ.Rotemberg.loss β c T p mc (Function.update p (m + 1) x))
      (p (m + 1))) :
    p (m + 1) - p m = β * (p (m + 2) - p (m + 1)) + 1 / c * mc (m + 1) :=
  Econ.Rotemberg.nkpc hβ hc hm hmin

theorem frozen_rot_calvo_bridge {β θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    {T : ℕ} {p mc : ℕ → ℝ} {m : ℕ} (hm : m + 2 ≤ T)
    (hmin : IsLocalMin (fun x => Econ.Rotemberg.loss β (θ / ((1 - θ) * (1 - β * θ))) T p mc
      (Function.update p (m + 1) x)) (p (m + 1))) :
    p (m + 1) - p m = β * (p (m + 2) - p (m + 1)) + (1 - θ) * (1 - β * θ) / θ * mc (m + 1) :=
  Econ.Rotemberg.calvo_bridge hβ hβ1 hθ hθ1 hm hmin

theorem frozen_rot_steady_inflation {β c : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) (T : ℕ) (πs : ℝ)
    {m : ℕ} (hm : m + 2 ≤ T) :
    IsLocalMin (fun x => Econ.Rotemberg.loss β c T (fun n => n * πs) (fun _ => c * (1 - β) * πs)
      (Function.update (fun n : ℕ => n * πs) (m + 1) x)) ((m + 1 : ℕ) * πs) :=
  Econ.Rotemberg.steady_inflation hβ hc T πs hm

theorem frozen_hk_isEq_iff (E : Econ.HeKrishnamurthy.Env) {w μ : ℝ} (hw : 0 < w) :
    E.IsEq w μ ↔ μ = E.premium w :=
  E.isEq_iff hw

theorem frozen_hk_premium_strictAnti (E : Econ.HeKrishnamurthy.Env) :
    StrictAntiOn E.premium (Set.Ioi 0) :=
  E.premium_strictAnti

theorem frozen_hk_unconstrained_redistribution (E E' : Econ.HeKrishnamurthy.Env)
    (hγ : E'.γ = E.γ) (hσ : E'.σ = E.σ) {w w' : ℝ} (hc : E.W ≤ E.m * w)
    (hc' : E'.W ≤ E'.m * w') (htot : w + E.W = w' + E'.W) :
    E.premium w = E'.premium w' :=
  E.unconstrained_redistribution E' hγ hσ hc hc' htot

theorem frozen_hk_constrained_redistribution_matters (E E' : Econ.HeKrishnamurthy.Env)
    (hγ : E'.γ = E.γ) (hσ : E'.σ = E.σ) (hm : E'.m = E.m) {w w' : ℝ} (hw : 0 < w)
    (hww : w < w') (hc : E.m * w < E.W) (hc' : E'.m * w' < E'.W)
    (htot : w + E.W = w' + E'.W) :
    E'.premium w' < E.premium w :=
  E.constrained_redistribution_matters E' hγ hσ hm hw hww hc hc' htot

end Econ.Audit
