/-
# Frozen statements: the Solow growth model

Headline statements of `Macro/Growth/Solow.lean`, copied verbatim after two
rounds of context-isolated adversarial review (2026-11-23; verdicts: faithful,
or faithful with the deviations documented in the `Solow.lean` header; see
`Audit/REVIEW-solow.md`). Each is closed by the library theorem, so if a
library statement is ever weakened, this file stops compiling. Lightweight
stand-in for `leanprover/comparator`. Do not edit a statement here without a
new review.
-/
module

public import EconLean.Macro.Growth.Solow

@[expose] public section

namespace Econ.Audit

open Filter Topology Set Econ.Solow

theorem frozen_solow_of_deriv {f f' : ℝ → ℝ} (h0 : f 0 = 0)
    (hcont0 : ContinuousWithinAt f (Ici 0) 0) (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hderiv : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hpos : ∀ k, 0 < k → 0 < f' k)
    (hinada0 : Tendsto f' (𝓝[>] 0) atTop) (hinadaTop : Tendsto f' atTop (𝓝 0)) :
    NeoclassicalProduction f :=
  NeoclassicalProduction.of_deriv h0 hcont0 hconc hderiv hpos hinada0 hinadaTop

theorem frozen_solow_isSteadyState_iff (E : Economy) {k : ℝ} :
    E.IsSteadyState k ↔ 0 < k ∧ E.s * E.f k = (E.n + E.δ) * k :=
  E.isSteadyState_iff

theorem frozen_solow_existsUnique_steadyState (E : Economy) : ∃! k, E.IsSteadyState k :=
  E.existsUnique_steadyState

theorem frozen_solow_tendsto_path (E : Economy) {kstar k₀ : ℝ} (hs : E.IsSteadyState kstar)
    (hk₀ : 0 < k₀) : Tendsto (E.path k₀) atTop (𝓝 kstar) :=
  E.tendsto_path hs hk₀

theorem frozen_solow_path_strictMono_of_lt (E : Economy) {kstar k₀ : ℝ}
    (hs : E.IsSteadyState kstar) (hk₀ : 0 < k₀) (hlt : k₀ < kstar) :
    StrictMono (E.path k₀) ∧ ∀ t, E.path k₀ t < kstar :=
  E.path_strictMono_of_lt hs hk₀ hlt

theorem frozen_solow_path_strictAnti_of_gt (E : Economy) {kstar k₀ : ℝ}
    (hs : E.IsSteadyState kstar) (hgt : kstar < k₀) :
    StrictAnti (E.path k₀) ∧ ∀ t, kstar < E.path k₀ t :=
  E.path_strictAnti_of_gt hs hgt

theorem frozen_solow_fixedPoint_iff (E : Economy) {kstar k : ℝ} (hs : E.IsSteadyState kstar)
    (hk : 0 ≤ k) : E.next k = k ↔ k = 0 ∨ k = kstar :=
  E.fixedPoint_iff hs hk

theorem frozen_solow_steadyState_strictMono_s {E₁ E₂ : Economy} (hf : E₁.f = E₂.f)
    (hn : E₁.n = E₂.n) (hδ : E₁.δ = E₂.δ) (hs : E₁.s < E₂.s) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂) : k₁ < k₂ :=
  Economy.steadyState_strictMono_s hf hn hδ hs h₁ h₂

theorem frozen_solow_steadyState_strictAnti_n {E₁ E₂ : Economy} (hf : E₁.f = E₂.f)
    (hs : E₁.s = E₂.s) (hδ : E₁.δ = E₂.δ) (hn : E₁.n < E₂.n) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂) : k₂ < k₁ :=
  Economy.steadyState_strictAnti_n hf hs hδ hn h₁ h₂

theorem frozen_solow_steadyState_strictAnti_δ {E₁ E₂ : Economy} (hf : E₁.f = E₂.f)
    (hs : E₁.s = E₂.s) (hn : E₁.n = E₂.n) (hδ : E₁.δ < E₂.δ) {k₁ k₂ : ℝ}
    (h₁ : E₁.IsSteadyState k₁) (h₂ : E₂.IsSteadyState k₂) : k₂ < k₁ :=
  Economy.steadyState_strictAnti_δ hf hs hn hδ h₁ h₂

theorem frozen_solow_cobbDouglas_neoclassical {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    NeoclassicalProduction (fun k => k ^ α) :=
  cobbDouglas_neoclassical hα₀ hα₁

theorem frozen_solow_cobbDouglas_steadyState (E : Economy) {α : ℝ} (hα₁ : α < 1)
    (hf : E.f = fun k => k ^ α) :
    E.IsSteadyState ((E.s / (E.n + E.δ)) ^ (1 / (1 - α))) :=
  cobbDouglas_steadyState E hα₁ hf

end Econ.Audit
