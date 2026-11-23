/-
# Frozen statements: saddle path, primal Ramsey, nested Baqaee–Farhi,
# Ricardian equivalence, tax smoothing, Barro–Gordon, Calvo, ACR, Holmström–Tirole

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-23; see `Audit/REVIEW-macro-batch7.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.DSGE.SaddlePath
public import EconLean.Macro.Fiscal.RamseyPrimal
public import EconLean.Macro.BaqaeeFarhiNested
public import EconLean.Macro.Fiscal.Ricardian
public import EconLean.Macro.Fiscal.TaxSmoothing
public import EconLean.Macro.Monetary.BarroGordon
public import EconLean.Macro.NK.Calvo
public import EconLean.Macro.Trade.ACR
public import EconLean.Finance.HolmstromTirole

@[expose] public section

namespace Econ.Audit

open Matrix Finset Filter Topology

theorem frozen_saddle {M : Matrix (Fin 2) (Fin 2) ℝ} {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace)
    (hp : μ₁ * μ₂ = M.det)
    (h₁ : |μ₁| < 1) (h₂ : 1 < |μ₂|) {v : Fin 2 → ℝ} (hv : M *ᵥ v = μ₁ • v) (hv0 : v 0 ≠ 0)
    (k₀ : ℝ) :
    ∃! z, Econ.Saddle.IsSolution M k₀ z :=
  Econ.Saddle.saddle hs hp h₁ h₂ hv hv0 k₀

theorem frozen_no_solution_of_explosive {M : Matrix (Fin 2) (Fin 2) ℝ} {μ₁ μ₂ : ℝ}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : 1 < |μ₁|) (h₂ : 1 < |μ₂|) {k₀ : ℝ} (hk : k₀ ≠ 0) (z : ℕ → Fin 2 → ℝ) :
    ¬ Econ.Saddle.IsSolution M k₀ z :=
  Econ.Saddle.no_solution_of_explosive hs hp h₁ h₂ hk z

theorem frozen_indeterminate {M : Matrix (Fin 2) (Fin 2) ℝ} {μ₁ μ₂ : ℝ}
    (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : |μ₁| < 1) (h₂ : |μ₂| < 1) (hne : μ₁ ≠ μ₂) {k₀ : ℝ} {z : ℕ → Fin 2 → ℝ}
    (hz : Econ.Saddle.IsSolution M k₀ z) : ∃ z', Econ.Saddle.IsSolution M k₀ z' ∧ z' ≠ z :=
  Econ.Saddle.indeterminate hs hp h₁ h₂ hne hz

theorem frozen_planner_euler (P : Econ.RamseyPrimal.Problem) {c k : ℕ → ℝ} (h : P.IsOptimal c k)
    (s : ℕ) (hc₀ : 0 < c s) (hc₁ : 0 < c (s + 1)) (hk : 0 < k (s + 1)) {Wc₀ Wc₁ Fk : ℝ}
    (hW₀ : HasDerivAt P.W Wc₀ (c s)) (hW₁ : HasDerivAt P.W Wc₁ (c (s + 1)))
    (hF : HasDerivAt P.F Fk (k (s + 1))) :
    Wc₀ = P.β * Wc₁ * Fk :=
  Econ.RamseyPrimal.Problem.planner_euler h s hc₀ hc₁ hk hW₀ hW₁ hF

theorem frozen_chamley_judd_primal (P : Econ.RamseyPrimal.Problem) {c k : ℕ → ℝ}
    (h : P.IsOptimal c k) (hc : ∀ t, 0 < c t)
    (hk : ∀ t, 0 < k (t + 1)) {uc Wc Fk τ : ℕ → ℝ}
    (hW : ∀ t, HasDerivAt P.W (Wc t) (c t)) (hF : ∀ t, HasDerivAt P.F (Fk t) (k t))
    (hhh : ∀ t, uc t = P.β * uc (t + 1) * (1 + (1 - τ (t + 1)) * (Fk (t + 1) - 1)))
    {ucs Wcs rs τs : ℝ} (hucs : 0 < ucs) (hWcs : 0 < Wcs) (hrs : rs ≠ 0)
    (huc : Tendsto uc atTop (𝓝 ucs)) (hWc : Tendsto Wc atTop (𝓝 Wcs))
    (hr : Tendsto (fun t => Fk t - 1) atTop (𝓝 rs)) (hτ : Tendsto τ atTop (𝓝 τs)) :
    τs = 0 :=
  Econ.RamseyPrimal.Problem.chamley_judd_primal h hc hk hW hF hhh hucs hWcs hrs huc hWc hr hτ

theorem frozen_bf_nested_second_order {G n : Type*} [Fintype G] [Fintype n]
    (N : Econ.BaqaeeFarhi.Nested G n) (h₀ : N.top.θ ≠ 1) (hθ : ∀ g, (N.grp g).θ ≠ 1)
    (x d : G → n → ℝ) :
    deriv (deriv fun t => N.logY (Econ.BaqaeeFarhi.Nested.line x d t)) 0 =
      (N.top.θ - 1) * (∑ g, N.Λ x g * N.m x d g ^ 2 - (∑ g, N.Λ x g * N.m x d g) ^ 2) +
      ∑ g, N.Λ x g * (((N.grp g).θ - 1) *
        (∑ i, (N.grp g).domar (x g) i * d g i ^ 2 - N.m x d g ^ 2)) :=
  N.second_order h₀ hθ x d

theorem frozen_ricardian {R : ℝ} {T : ℕ} {y g τ τ' : ℕ → ℝ} (U : (ℕ → ℝ) → ℝ)
    (h : Econ.Ricardian.GovBudget R T g τ) (h' : Econ.Ricardian.GovBudget R T g τ')
    {c : ℕ → ℝ}
    (hc : c ∈ Econ.Ricardian.budget R T y τ ∧ ∀ c' ∈ Econ.Ricardian.budget R T y τ, U c' ≤ U c) :
    c ∈ Econ.Ricardian.budget R T y τ' ∧ ∀ c' ∈ Econ.Ricardian.budget R T y τ', U c' ≤ U c :=
  Econ.Ricardian.ricardian U h h' hc

theorem frozen_smooth_optimal {β : ℝ} {T : ℕ} (hβ : 0 < β) (hT : 0 < T) {B : ℝ} {τ : ℕ → ℝ}
    (hτ : Econ.TaxSmoothing.Feasible β T B τ) :
    Econ.TaxSmoothing.cost β T (Econ.TaxSmoothing.smooth β T B) ≤ Econ.TaxSmoothing.cost β T τ :=
  Econ.TaxSmoothing.smooth_optimal hβ hT hτ

theorem frozen_discretion_eq {lam k : ℝ} (hlam : 0 < lam) (π : ℝ) :
    Econ.BarroGordon.IsDiscretionEq lam k π ↔ π = lam * k :=
  Econ.BarroGordon.discretion_eq hlam π

theorem frozen_nkpc {β θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    {p mc : ℕ → ℝ} {C : ℝ}
    (hC : ∀ t, |p t + mc t| ≤ C) (h : Econ.Calvo.PriceDynamics β θ p mc) (t : ℕ) :
    p (t + 1) - p t = β * (p (t + 2) - p (t + 1)) +
      (1 - θ) * (1 - β * θ) / θ * mc (t + 1) :=
  Econ.Calvo.nkpc hβ hβ1 hθ hθ1 hC h t

theorem frozen_acr_realWage {ι : Type*} [Fintype ι] (W : Econ.ACR.World ι) (j : ι) :
    W.w j / W.P j = W.A j * W.lamjj j ^ (-W.ε)⁻¹ :=
  W.realWage_eq j

theorem frozen_ht_feasible_iff (M : Econ.HolmstromTirole.Model) (A : ℝ) (hR : M.B / M.Δp ≤ M.R) :
    (∃ Rb Rl, M.Feasible A Rb Rl) ↔ M.threshold ≤ A :=
  M.feasible_iff A hR

end Econ.Audit

end
