/-
# Frozen statements: AMSS / Barro tax smoothing and Lucas–Stokey with general utility

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-25; see `Audit/REVIEW-macro-batch17.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.Fiscal.AMSS
public import EconLean.Macro.Fiscal.LucasStokeyGeneral

@[expose] public section

namespace Econ.Audit

theorem frozen_amss_euler_rf {S : Type*} [Fintype S] (E : Econ.AMSS.Env S) {C C' : ℝ → ℝ}
    (hC : ∀ x, HasDerivAt C (C' x) x) {b : ℝ} (hmin : IsLocalMin (E.costRF C) b) :
    C' (E.tax₀RF b) = E.β * E.R * ∑ s, E.π s * C' (E.taxRF b s) :=
  E.euler_rf hC hmin

theorem frozen_amss_martingale_quad {S : Type*} [Fintype S] (E : Econ.AMSS.Env S) {κ : ℝ}
    (hκ : 0 < κ) (hβR : E.β * E.R = 1) {b : ℝ}
    (hmin : IsLocalMin (E.costRF fun τ => κ * τ ^ 2 / 2) b) :
    E.tax₀RF b = ∑ s, E.π s * E.taxRF b s :=
  E.martingale_quad hκ hβR hmin

theorem frozen_amss_cm_constant {S : Type*} [Fintype S] [DecidableEq S] (E : Econ.AMSS.Env S)
    {C C' : ℝ → ℝ} (hC : ∀ x, HasDerivAt C (C' x) x) (hC' : StrictMono C')
    (hβR : E.β * E.R = 1) {bs : S → ℝ}
    (hmin : ∀ s, IsLocalMin (fun x => E.costCM C (Function.update bs s x)) (bs s)) (s : S)
    (hs : 0 < E.π s) : E.taxCM bs s = E.tax₀CM bs :=
  E.cm_constant hC hC' hβR hmin s hs

theorem frozen_amss_cm_le_rf {S : Type*} [Fintype S] (E : Econ.AMSS.Env S) {C : ℝ → ℝ}
    {bs : S → ℝ} (hmin : ∀ bs', E.costCM C bs ≤ E.costCM C bs') (b : ℝ) :
    E.costCM C bs ≤ E.costRF C b :=
  E.cm_le_rf hmin b

theorem frozen_amss_quad_optimum {S : Type*} [Fintype S] (E : Econ.AMSS.Env S) {κ : ℝ}
    (hκ : 0 < κ) (hβR : E.β * E.R = 1) (b : ℝ) :
    E.costRF (fun τ => κ * τ ^ 2 / 2)
        (E.R * (E.g₀ + E.b₀ - ∑ s, E.π s * E.g s) / (1 + E.R)) ≤
      E.costRF (fun τ => κ * τ ^ 2 / 2) b :=
  E.quad_optimum hκ hβR b

theorem frozen_lsg_history_independence (P : Econ.LucasStokeyGeneral.Prefs) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n) (hl : ∀ n, 0 < l₀ n)
    (hc : ∀ n, 0 < l₀ n - g n)
    (hmax : IsLocalMaxOn (P.welfare w g) {l | P.implement w g l = P.implement w g l₀} l₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧ (∀ n, P.Phi a b (g n) (l₀ n) = 0) ∧ ∀ n m, g n = g m →
      (∀ x y, 0 < x → 0 < x - g n → 0 < y → 0 < y - g n →
        P.Phi a b (g n) x = 0 → P.Phi a b (g n) y = 0 → x = y) →
      l₀ n = l₀ m ∧ l₀ n - g n = l₀ m - g m ∧ P.tax g l₀ n = P.tax g l₀ m :=
  P.history_independence hw hl hc hmax

theorem frozen_lsg_distortionary_witness {ι : Type*} [Fintype ι] {w g : ι → ℝ}
    (hw : ∀ n, 0 ≤ w n) {c : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) :
    IsLocalMaxOn ((Econ.LucasStokeyGeneral.Prefs.quasilinear 1).welfare w g)
      {l | (Econ.LucasStokeyGeneral.Prefs.quasilinear 1).implement w g l =
        (Econ.LucasStokeyGeneral.Prefs.quasilinear 1).implement w g (fun _ => c)}
      (fun _ => c) ∧ ∀ n, 0 < (Econ.LucasStokeyGeneral.Prefs.quasilinear 1).tax g (fun _ => c) n :=
  Econ.LucasStokeyGeneral.Prefs.distortionary_witness hw hc1 hc2

end Econ.Audit
