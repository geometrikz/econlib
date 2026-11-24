/-
# Frozen statements: global games (Morris–Shin 2003, §2)

Headline statements of `Information/GlobalGames`, copied after the adversarial review recorded
in `Audit/REVIEW-global-games.md`. Each is closed by the library theorem, so if a library
statement is ever weakened this file stops compiling. Do not edit a statement here without a new
review.
-/
module

public import EconLean.Information.GlobalGames

@[expose] public section

namespace Econ.Audit

open MeasureTheory Set Econ

theorem frozen_threshold_survives {μ : ℝ → Measure ℝ} {G : ℝ → ℝ} {ε : ℝ}
    (hb : GlobalBeliefs μ G ε) : ∀ n, Ioi (1 / 2 : ℝ) ∈ survives μ n :=
  hb.threshold_survives

theorem frozen_globalGame_invest {μ : ℝ → Measure ℝ} {G : ℝ → ℝ} {ε : ℝ}
    (hb : GlobalBeliefs μ G ε) {x : ℝ} (hx : 1 / 2 < x) :
    ∃ n, ∀ A ∈ survives μ n, x ∈ A :=
  hb.globalGame_invest hx

theorem frozen_globalGame_noInvest {μ : ℝ → Measure ℝ} {G : ℝ → ℝ} {ε : ℝ}
    (hb : GlobalBeliefs μ G ε) {x : ℝ} (hx : x < 1 / 2) :
    ∃ n, ∀ A ∈ survives μ n, x ∉ A :=
  hb.globalGame_noInvest hx

theorem frozen_globalGame_unique {μ : ℝ → Measure ℝ} {G : ℝ → ℝ} {ε : ℝ}
    (hb : GlobalBeliefs μ G ε) :
    (∀ n, Ioi (1 / 2 : ℝ) ∈ survives μ n) ∧
      ∀ A, (∀ n, A ∈ survives μ n) → Ioi (1 / 2 : ℝ) ⊆ A ∧ A ⊆ Ici (1 / 2) :=
  hb.globalGame_unique

theorem frozen_uniformNoise_spec : GlobalBeliefs uniformBelief uniformG 1 :=
  uniformNoise_spec

end Econ.Audit
