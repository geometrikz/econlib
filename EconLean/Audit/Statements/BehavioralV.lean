/-
# Frozen statements: behavioral round 5

Headline statements of `Behavioral/BeliefRule.lean`,
`Behavioral/CognitiveDiscounting.lean`, `Behavioral/DiagnosticExpectations.lean`,
`Behavioral/Overconfidence.lean`, `Behavioral/MotivatedBeliefs.lean`,
`Behavioral/NarrowBracketing.lean` and `Behavioral/MarketInequity.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-5.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.BeliefRule
public import EconLean.Behavioral.CognitiveDiscounting
public import EconLean.Behavioral.DiagnosticExpectations
public import EconLean.Behavioral.Overconfidence
public import EconLean.Behavioral.MotivatedBeliefs
public import EconLean.Behavioral.NarrowBracketing
public import EconLean.Behavioral.MarketInequity

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralV

section BeliefRule
open Econ.BeliefRule Econ.BeliefRule.Linear


theorem frozen_forecast_rational (e e' : ℝ) : rational.forecast e e' = e := by
  first
  | exact @Econ.BeliefRule.Linear.forecast_rational ..
  | (apply @Econ.BeliefRule.Linear.forecast_rational <;> assumption)

theorem frozen_forecast_cognitive (m e e' : ℝ) : (cognitive m).forecast e e' = m * e := by
  first
  | exact @Econ.BeliefRule.Linear.forecast_cognitive ..
  | (apply @Econ.BeliefRule.Linear.forecast_cognitive <;> assumption)

theorem frozen_forecast_diagnostic (θ e e' : ℝ) :
    (diagnostic θ).forecast e e' = e + θ * (e - e') := by
  first
  | exact @Econ.BeliefRule.Linear.forecast_diagnostic ..
  | (apply @Econ.BeliefRule.Linear.forecast_diagnostic <;> assumption)

theorem frozen_cognitive_one : cognitive 1 = rational := by
  first
  | exact @Econ.BeliefRule.Linear.cognitive_one ..
  | (apply @Econ.BeliefRule.Linear.cognitive_one <;> assumption)

theorem frozen_diagnostic_zero : diagnostic 0 = rational := by
  first
  | exact @Econ.BeliefRule.Linear.diagnostic_zero ..
  | (apply @Econ.BeliefRule.Linear.diagnostic_zero <;> assumption)

theorem frozen_forecast_eq_iff (B : Linear) : (∀ e e', B.forecast e e' = e) ↔ B = rational := by
  first
  | exact @Econ.BeliefRule.Linear.forecast_eq_iff ..
  | (apply @Econ.BeliefRule.Linear.forecast_eq_iff <;> assumption)

theorem frozen_continuous_forecast (e e' : ℝ) :
    Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : Linear).forecast e e' := by
  first
  | exact @Econ.BeliefRule.Linear.continuous_forecast ..
  | (apply @Econ.BeliefRule.Linear.continuous_forecast <;> assumption)

end BeliefRule

section CognitiveDiscounting
open Econ.CognitiveNK Econ.CognitiveNK.Model Econ.BeliefRule
variable (E : Econ.CognitiveNK.Model)

theorem frozen_determinate_iff : E.Determinate ↔ 0 < E.index := by
  first
  | exact @Econ.CognitiveNK.Model.determinate_iff ..
  | (apply @Econ.CognitiveNK.Model.determinate_iff <;> assumption)

theorem frozen_peg_determinate_iff (hπ : E.φπ = 0) (hx : E.φx = 0) :
    E.Determinate ↔ E.κ < E.σ * (1 - E.M) * (1 - E.β * E.Mf) := by
  first
  | exact @Econ.CognitiveNK.Model.peg_determinate_iff ..
  | (apply @Econ.CognitiveNK.Model.peg_determinate_iff <;> assumption)

theorem frozen_peg_indeterminate_rational (hπ : E.φπ = 0) (hx : E.φx = 0) (hM : E.M = 1)
    (hMf : E.Mf = 1) : ¬ E.Determinate := by
  first
  | exact @Econ.CognitiveNK.Model.peg_indeterminate_rational ..
  | (apply @Econ.CognitiveNK.Model.peg_indeterminate_rational <;> assumption)

theorem frozen_isEquilibrium_rational (hM : E.M = 1) (hMf : E.Mf = 1) (x p i : ℕ → ℝ) :
    E.IsEquilibrium x p i ↔ E.toRational.IsEquilibrium x p i := by
  first
  | exact @Econ.CognitiveNK.Model.isEquilibrium_rational ..
  | (apply @Econ.CognitiveNK.Model.isEquilibrium_rational <;> assumption)

theorem frozen_determinate_iff_rational (hM : E.M = 1) (hMf : E.Mf = 1) :
    E.Determinate ↔ E.toRational.Determinate := by
  first
  | exact @Econ.CognitiveNK.Model.determinate_iff_rational ..
  | (apply @Econ.CognitiveNK.Model.determinate_iff_rational <;> assumption)

theorem frozen_fg_response {M σ : ℝ} {T : ℕ} {x : ℕ → ℝ} (hx : IsISPath M σ (cut T) x)
    (hend : x (T + 1) = 0) : x 0 = M ^ T / σ := by
  first
  | exact @Econ.CognitiveNK.Model.fg_response ..
  | (apply @Econ.CognitiveNK.Model.fg_response <;> assumption)

theorem frozen_fg_path_exists (M σ : ℝ) (T : ℕ) :
    ∃ x, IsISPath M σ (cut T) x ∧ x (T + 1) = 0 := by
  first
  | exact @Econ.CognitiveNK.Model.fg_path_exists ..
  | (apply @Econ.CognitiveNK.Model.fg_path_exists <;> assumption)

theorem frozen_fg_vanishes {M σ : ℝ} (hM0 : 0 ≤ M) (hM1 : M < 1) :
    Filter.Tendsto (fun T : ℕ => M ^ T / σ) Filter.atTop (nhds 0) := by
  first
  | exact @Econ.CognitiveNK.Model.fg_vanishes ..
  | (apply @Econ.CognitiveNK.Model.fg_vanishes <;> assumption)

theorem frozen_fg_puzzle_rational {σ : ℝ} {T : ℕ} {x : ℕ → ℝ} (hx : IsISPath 1 σ (cut T) x)
    (hend : x (T + 1) = 0) : x 0 = 1 / σ := by
  first
  | exact @Econ.CognitiveNK.Model.fg_puzzle_rational ..
  | (apply @Econ.CognitiveNK.Model.fg_puzzle_rational <;> assumption)

theorem frozen_determinate_robust (E : Model) (h : 0 < E.κ * (E.φπ - 1) + (1 - E.β) * E.φx) :
    E.Determinate := by
  first
  | exact @Econ.CognitiveNK.Model.determinate_robust ..
  | (apply @Econ.CognitiveNK.Model.determinate_robust <;> assumption)

theorem frozen_fg_eventually_below_half {σ : ℝ} (hσ : 0 < σ) {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M < 1) :
    ∃ T : ℕ, M ^ T / σ < 1 / (2 * σ) := by
  first
  | exact @Econ.CognitiveNK.Model.fg_eventually_below_half ..
  | (apply @Econ.CognitiveNK.Model.fg_eventually_below_half <;> assumption)

end CognitiveDiscounting

section DiagnosticExpectations
open Econ.Diagnostic Econ.BeliefRule


theorem frozen_FE_eq (B : Linear) (ρ : ℝ) :
    FE B ρ = ![(1 - B.m) * ρ ^ 3, (1 - B.m) * ρ ^ 2, (1 - B.m - B.θ) * ρ, 1] := by
  first
  | exact @Econ.Diagnostic.FE_eq ..
  | (apply @Econ.Diagnostic.FE_eq <;> assumption)

theorem frozen_FR_eq (B : Linear) (ρ : ℝ) : FR B ρ = ![0, -B.θ * ρ ^ 2, (B.m + B.θ) * ρ, 0] := by
  first
  | exact @Econ.Diagnostic.FR_eq ..
  | (apply @Econ.Diagnostic.FR_eq <;> assumption)

theorem frozen_cov_FE_FR (B : Linear) (ρ v s2 : ℝ) :
    cov v s2 (FE B ρ) (FR B ρ) =
      s2 * ρ ^ 2 * ((1 - B.m - B.θ) * (B.m + B.θ) - B.θ * (1 - B.m) * ρ ^ 2) := by
  first
  | exact @Econ.Diagnostic.cov_FE_FR ..
  | (apply @Econ.Diagnostic.cov_FE_FR <;> assumption)

theorem frozen_cov_FR_FR (B : Linear) (ρ v s2 : ℝ) :
    cov v s2 (FR B ρ) (FR B ρ) = s2 * ρ ^ 2 * (B.θ ^ 2 * ρ ^ 2 + (B.m + B.θ) ^ 2) := by
  first
  | exact @Econ.Diagnostic.cov_FR_FR ..
  | (apply @Econ.Diagnostic.cov_FR_FR <;> assumption)

theorem frozen_cov_FE_FR_rational (ρ v s2 : ℝ) : cov v s2 (FE Linear.rational ρ) (FR Linear.rational ρ) = 0 := by
  first
  | exact @Econ.Diagnostic.cov_FE_FR_rational ..
  | (apply @Econ.Diagnostic.cov_FE_FR_rational <;> assumption)

theorem frozen_cov_FE_FR_diagnostic (θ ρ v s2 : ℝ) :
    cov v s2 (FE (Linear.diagnostic θ) ρ) (FR (Linear.diagnostic θ) ρ) =
      -(θ * (1 + θ) * ρ ^ 2 * s2) := by
  first
  | exact @Econ.Diagnostic.cov_FE_FR_diagnostic ..
  | (apply @Econ.Diagnostic.cov_FE_FR_diagnostic <;> assumption)

theorem frozen_cov_FE_FR_cognitive (m ρ v s2 : ℝ) :
    cov v s2 (FE (Linear.cognitive m) ρ) (FR (Linear.cognitive m) ρ) =
      (1 - m) * m * ρ ^ 2 * s2 := by
  first
  | exact @Econ.Diagnostic.cov_FE_FR_cognitive ..
  | (apply @Econ.Diagnostic.cov_FE_FR_cognitive <;> assumption)

theorem frozen_cgCoeff_neg_iff {θ ρ v s2 : ℝ} (hθ : 0 ≤ θ) (hρ : ρ ≠ 0) (hs : 0 < s2) :
    cgCoeff (Linear.diagnostic θ) ρ v s2 < 0 ↔ 0 < θ := by
  first
  | exact @Econ.Diagnostic.cgCoeff_neg_iff ..
  | (apply @Econ.Diagnostic.cgCoeff_neg_iff <;> assumption)

theorem frozen_cgCoeff_cognitive_pos {m ρ v s2 : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hρ : ρ ≠ 0)
    (hs : 0 < s2) : 0 < cgCoeff (Linear.cognitive m) ρ v s2 := by
  first
  | exact @Econ.Diagnostic.cgCoeff_cognitive_pos ..
  | (apply @Econ.Diagnostic.cgCoeff_cognitive_pos <;> assumption)

theorem frozen_fcT_diagnostic (θ ρ : ℝ) :
    fcT (Linear.diagnostic θ) ρ = ρ • x0 ρ + (θ * ρ) • εt := by
  first
  | exact @Econ.Diagnostic.fcT_diagnostic ..
  | (apply @Econ.Diagnostic.fcT_diagnostic <;> assumption)

theorem frozen_fe_orthogonal_iff (B : Linear) {ρ v s2 : ℝ} (hρ : ρ ≠ 0) (hs : 0 < s2) :
    (∀ y : Var, y 3 = 0 → cov v s2 (FE B ρ) y = 0) ↔ B = Linear.rational := by
  first
  | exact @Econ.Diagnostic.fe_orthogonal_iff ..
  | (apply @Econ.Diagnostic.fe_orthogonal_iff <;> assumption)

theorem frozen_hasSum_priceIRF {θ ρ δ : ℝ} (h : |δ * ρ| < 1) (k : ℕ) :
    HasSum (fun h : ℕ => δ ^ (h + 1) * forecastIRF (Linear.diagnostic θ) ρ k (h + 1))
      ((if k = 0 then 1 + θ else 1) * ρ ^ k * (δ * ρ / (1 - δ * ρ))) := by
  first
  | exact @Econ.Diagnostic.hasSum_priceIRF ..
  | (apply @Econ.Diagnostic.hasSum_priceIRF <;> assumption)

theorem frozen_price_overreaction {θ ρ δ : ℝ} (h : |δ * ρ| < 1) :
    priceIRF θ ρ δ 0 = (1 + θ) * priceIRF 0 ρ δ 0 := by
  first
  | exact @Econ.Diagnostic.price_overreaction ..
  | (apply @Econ.Diagnostic.price_overreaction <;> assumption)

theorem frozen_price_reversal {θ ρ δ : ℝ} (h : |δ * ρ| < 1) (k : ℕ) :
    priceIRF θ ρ δ (k + 1) = priceIRF 0 ρ δ (k + 1) := by
  first
  | exact @Econ.Diagnostic.price_reversal ..
  | (apply @Econ.Diagnostic.price_reversal <;> assumption)

theorem frozen_price_change_lt {θ ρ δ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) (hδ : 0 < δ) (h1 : δ * ρ < 1) :
    priceIRF θ ρ δ 1 - priceIRF θ ρ δ 0 < priceIRF 0 ρ δ 1 - priceIRF 0 ρ δ 0 := by
  first
  | exact @Econ.Diagnostic.price_change_lt ..
  | (apply @Econ.Diagnostic.price_change_lt <;> assumption)

end DiagnosticExpectations

section Overconfidence
open Econ.Overconfidence


theorem frozen_mse_sub_mse_bayes {τ₀ τs : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (w : ℝ) :
    mse τ₀ τs w - mse τ₀ τs (weight τ₀ τs) = (w - weight τ₀ τs) ^ 2 * (τ₀ + τs) / (τ₀ * τs) := by
  first
  | exact @Econ.Overconfidence.mse_sub_mse_bayes ..
  | (apply @Econ.Overconfidence.mse_sub_mse_bayes <;> assumption)

theorem frozen_mse_bayes {τ₀ τs : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) :
    mse τ₀ τs (weight τ₀ τs) = 1 / (τ₀ + τs) := by
  first
  | exact @Econ.Overconfidence.mse_bayes ..
  | (apply @Econ.Overconfidence.mse_bayes <;> assumption)

theorem frozen_mse_bayes_lt {τ₀ τs : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) {w : ℝ} (hw : w ≠ weight τ₀ τs) :
    mse τ₀ τs (weight τ₀ τs) < mse τ₀ τs w := by
  first
  | exact @Econ.Overconfidence.mse_bayes_lt ..
  | (apply @Econ.Overconfidence.mse_bayes_lt <;> assumption)

theorem frozen_weight_overconfident_gt {τ₀ τs k : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (hk : 1 < k) :
    weight τ₀ τs < weight τ₀ (k * τs) := by
  first
  | exact @Econ.Overconfidence.weight_overconfident_gt ..
  | (apply @Econ.Overconfidence.weight_overconfident_gt <;> assumption)

theorem frozen_mse_overconfident_gt {τ₀ τs k : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (hk : 1 < k) :
    mse τ₀ τs (weight τ₀ τs) < mse τ₀ τs (weight τ₀ (k * τs)) := by
  first
  | exact @Econ.Overconfidence.mse_overconfident_gt ..
  | (apply @Econ.Overconfidence.mse_overconfident_gt <;> assumption)

theorem frozen_overprecision {τ₀ τs k : ℝ} (h₀ : 0 < τ₀) (hs : 0 < τs) (hk : 1 < k) :
    1 / (τ₀ + k * τs) < mse τ₀ τs (weight τ₀ (k * τs)) := by
  first
  | exact @Econ.Overconfidence.overprecision ..
  | (apply @Econ.Overconfidence.overprecision <;> assumption)

end Overconfidence

section MotivatedBeliefs
open Econ.MotivatedBeliefs Set


theorem frozen_rational_not_optimal {A R : ℝ → ℝ} {q a : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hA : HasDerivAt A a q) (hR : DifferentiableAt ℝ R q) (hRmax : IsMaxOn R (Icc 0 1) q)
    (ha : a ≠ 0) : ¬ IsMaxOn (fun p => A p + R p) (Icc 0 1) q := by
  first
  | exact @Econ.MotivatedBeliefs.rational_not_optimal ..
  | (apply @Econ.MotivatedBeliefs.rational_not_optimal <;> assumption)

theorem frozen_exists_better_belief {A R : ℝ → ℝ} {q a : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hA : HasDerivAt A a q) (hR : DifferentiableAt ℝ R q) (hRmax : IsMaxOn R (Icc 0 1) q)
    (ha : a ≠ 0) : ∃ p ∈ Icc (0 : ℝ) 1, A q + R q < A p + R p := by
  first
  | exact @Econ.MotivatedBeliefs.exists_better_belief ..
  | (apply @Econ.MotivatedBeliefs.exists_better_belief <;> assumption)

theorem frozen_example_optimal (q p : ℝ) : W q p ≤ W q (q + 1 / 2) := by
  first
  | exact @Econ.MotivatedBeliefs.example_optimal ..
  | (apply @Econ.MotivatedBeliefs.example_optimal <;> assumption)

theorem frozen_example_optimism {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    q < q + 1 / 2 ∧ q + 1 / 2 ∈ Icc (0 : ℝ) 1 ∧ W q q < W q (q + 1 / 2) := by
  first
  | exact @Econ.MotivatedBeliefs.example_optimism ..
  | (apply @Econ.MotivatedBeliefs.example_optimism <;> assumption)

end MotivatedBeliefs

section NarrowBracketing
open Econ.Bracketing Set


theorem frozen_dominated {u : ℝ → ℝ} (hu : StrictMono u) : eu u 240 (-760) < eu u 250 (-750) := by
  first
  | exact @Econ.Bracketing.dominated ..
  | (apply @Econ.Bracketing.dominated <;> assumption)

theorem frozen_narrow_choices_exist : ∃ v : ℝ → ℝ, StrictMono v ∧ v 0 = 0 ∧ ConcaveOn ℝ (Ici 0) v ∧
    ConvexOn ℝ (Iic 0) v ∧ (∀ y, 0 ≤ y → v (-y) ≤ -v y) ∧ ChoosesA v ∧ ChoosesD v ∧
    eu v 240 (-760) < eu v 250 (-750) := by
  first
  | exact @Econ.Bracketing.narrow_choices_exist ..
  | (apply @Econ.Bracketing.narrow_choices_exist <;> assumption)

theorem frozen_segregate_gains {v : ℝ → ℝ} (hv : ConcaveOn ℝ (Ici 0) v) (h0 : v 0 = 0) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : v (x + y) ≤ v x + v y := by
  first
  | exact @Econ.Bracketing.segregate_gains ..
  | (apply @Econ.Bracketing.segregate_gains <;> assumption)

theorem frozen_integrate_losses {v : ℝ → ℝ} (hv : ConvexOn ℝ (Iic 0) v) (h0 : v 0 = 0) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : v (-x) + v (-y) ≤ v (-(x + y)) := by
  first
  | exact @Econ.Bracketing.integrate_losses ..
  | (apply @Econ.Bracketing.integrate_losses <;> assumption)

theorem frozen_integrate_mixed {v : ℝ → ℝ} (hv : ConcaveOn ℝ (Ici 0) v) (h0 : v 0 = 0)
    (hla : ∀ y, 0 ≤ y → v (-y) ≤ -v y) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    v x + v (-y) ≤ v (x - y) := by
  first
  | exact @Econ.Bracketing.integrate_mixed ..
  | (apply @Econ.Bracketing.integrate_mixed <;> assumption)

end NarrowBracketing

section MarketInequity
open Econ.MarketInequity Econ.SocialPreferences


theorem frozen_loser_utility (α β : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    fs α β (payoffs s) 1 = -(α / 2) := by
  first
  | exact @Econ.MarketInequity.loser_utility ..
  | (apply @Econ.MarketInequity.loser_utility <;> assumption)

theorem frozen_win_utility_gt {α β s : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1) (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    -(α / 2) < (1 - s) - α / 2 * max (2 * s - 1) 0 - β / 2 * ((1 - s) + max (1 - 2 * s) 0) := by
  first
  | exact @Econ.MarketInequity.win_utility_gt ..
  | (apply @Econ.MarketInequity.win_utility_gt <;> assumption)

theorem frozen_loser_outbids {α β s : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1) (hs0 : 0 ≤ s)
    (hs1 : s < 1) : ∃ s', s < s' ∧ s' ≤ 1 ∧ fs α β (payoffs s) 1 < fs α β (deviation s') 1 := by
  first
  | exact @Econ.MarketInequity.loser_outbids ..
  | (apply @Econ.MarketInequity.loser_outbids <;> assumption)

theorem frozen_competitive_offer {α β s : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1)
    (hNE : ∀ s', s < s' → s' ≤ 1 → fs α β (deviation s') 1 ≤ fs α β (payoffs s) 1) : s = 1 := by
  first
  | exact @Econ.MarketInequity.competitive_offer ..
  | (apply @Econ.MarketInequity.competitive_offer <;> assumption)
  | exact Econ.MarketInequity.competitive_offer hα hβ0 hβ hs0 hs1 hNE

theorem frozen_competitive_no_outbid {α β : ℝ} (hα : 0 ≤ α) {s' : ℝ} (hs' : 1 < s') :
    fs α β (deviation s') 1 < fs α β (payoffs 1) 1 := by
  first
  | exact @Econ.MarketInequity.competitive_no_outbid ..
  | (apply @Econ.MarketInequity.competitive_no_outbid <;> assumption)

end MarketInequity

end Econ.Audit.BehavioralV
