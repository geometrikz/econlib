/-
# Frozen statements: two-type optimal income tax, Ramsey commodity taxes,
# the intertemporal Keynesian cross, Zipf granularity

Headline statements copied verbatim after context-isolated adversarial review
(2026-11-24; see `Audit/REVIEW-macro-batch13.md`). Each is closed by the
library theorem, so if a library statement is weakened this file stops
compiling. Do not edit a statement here without a new review.
-/
module

public import EconLean.Macro.PublicFinance.TwoTypeMirrlees
public import EconLean.Macro.PublicFinance.RamseyCommodityTax
public import EconLean.Macro.IKC
public import EconLean.Macro.Granularity

@[expose] public section

namespace Econ.Audit

open Finset Matrix

theorem frozen_mirrlees_welfare_le (P : Econ.Mirrlees2.Params) (v : ℝ → ℝ) {cL yL cH yH : ℝ}
    (hF : P.Feasible cL yL cH yH) (hIC : P.ICH v cL yL cH yH) :
    P.welfare v cL yL cH yH ≤ P.W v yL yH :=
  P.welfare_le v hF hIC

theorem frozen_mirrlees_optimum_no_distortion_top (P : Econ.Mirrlees2.Params) (v : ℝ → ℝ)
    {v' : ℝ → ℝ} (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH) (hyH : 0 < yH)
    (hs : P.Φ v yL < P.Φ v yH) : Econ.Mirrlees2.Params.wedge v' P.θH yH = 0 :=
  P.optimum_no_distortion_top v hv hopt hyH hs

theorem frozen_mirrlees_optimum_bottom_tax_pos (P : Econ.Mirrlees2.Params) (v : ℝ → ℝ)
    {v' : ℝ → ℝ} (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hmono : StrictMonoOn v' (Set.Ioi 0)) (hnn : ∀ x, 0 < x → 0 ≤ v' x)
    {cL yL cH yH : ℝ} (hopt : P.IsOptimum v cL yL cH yH) (hyL : 0 < yL)
    (hs : P.Φ v yL < P.Φ v yH) : 0 < Econ.Mirrlees2.Params.wedge v' P.θL yL :=
  P.optimum_bottom_tax_pos v hv hmono hnn hopt hyL hs

theorem frozen_ramsey_rule {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {CS x : ι → ℝ → ℝ} {x' p t₀ : ι → ℝ}
    (hCS : ∀ i, HasStrictDerivAt (CS i) (-x i (p i + t₀ i)) (p i + t₀ i))
    (hx : ∀ i, HasStrictDerivAt (x i) (x' i) (p i + t₀ i))
    (hx0 : ∀ i, x i (p i + t₀ i) ≠ 0)
    (hmax : IsLocalMaxOn (Econ.RamseyTax.welfare CS p)
      {t | Econ.RamseyTax.revenue x p t = Econ.RamseyTax.revenue x p t₀} t₀) :
    ∃ θ : ℝ, ∀ k, t₀ k * x' k = θ * x k (p k + t₀ k) :=
  Econ.RamseyTax.ramsey_rule hCS hx hx0 hmax

theorem frozen_inverse_elasticity_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {CS x : ι → ℝ → ℝ} {x' p t₀ : ι → ℝ}
    (hCS : ∀ i, HasStrictDerivAt (CS i) (-x i (p i + t₀ i)) (p i + t₀ i))
    (hx : ∀ i, HasStrictDerivAt (x i) (x' i) (p i + t₀ i))
    (hq : ∀ i, 0 < p i + t₀ i) (hxpos : ∀ i, 0 < x i (p i + t₀ i))
    (hε : ∀ i, 0 < Econ.RamseyTax.elasticity (p i + t₀ i) (x i (p i + t₀ i)) (x' i))
    (hrev : 0 < Econ.RamseyTax.revenue x p t₀)
    (hmax : IsLocalMaxOn (Econ.RamseyTax.welfare CS p)
      {t | Econ.RamseyTax.revenue x p t = Econ.RamseyTax.revenue x p t₀} t₀) :
    ∃ c : ℝ, 0 < c ∧ (∀ k, t₀ k / (p k + t₀ k) =
        c / Econ.RamseyTax.elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k)) ∧
      (∀ k l, Econ.RamseyTax.elasticity (p l + t₀ l) (x l (p l + t₀ l)) (x' l) <
          Econ.RamseyTax.elasticity (p k + t₀ k) (x k (p k + t₀ k)) (x' k) →
        t₀ k / (p k + t₀ k) < t₀ l / (p l + t₀ l)) :=
  Econ.RamseyTax.inverse_elasticity_pos hCS hx hq hxpos hε hrev hmax

theorem frozen_ikc_existsUnique {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : IsUnit (1 - M).det) (dG dT : ι → ℝ) : ∃! dY, Econ.IKC.IsEq M dG dT dY :=
  Econ.IKC.existsUnique_eq M hM dG dT

theorem frozen_ikc_balanced_budget_isEq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (dG : ι → ℝ) : Econ.IKC.IsEq M dG dG dG :=
  Econ.IKC.balanced_budget_isEq M dG

theorem frozen_ikc_pv_budget {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hq : q ᵥ* M = q) {dG dT dY : ι → ℝ} (h : Econ.IKC.IsEq M dG dT dY) : q ⬝ᵥ dG = q ⬝ᵥ dT :=
  Econ.IKC.pv_budget M q hq h

theorem frozen_ikc_not_isUnit_of_pv {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    {q : ι → ℝ} (hq0 : q ≠ 0) (hq : q ᵥ* M = q) : ¬ IsUnit (1 - M).det :=
  Econ.IKC.not_isUnit_of_pv M hq0 hq

theorem frozen_granular_var_zipf_le {σ : Type*} [Fintype σ] (P : Econ.CAPM.Prob σ) {N : ℕ}
    (hN : 0 < N) (ε : Fin N → σ → ℝ) {v : ℝ} (hmean : ∀ i, P.E (ε i) = 0)
    (hcov : ∀ i j, P.E (fun ω => ε i ω * ε j ω) = if i = j then v else 0) :
    P.Var (Econ.Granular.agg (Econ.Granular.zipf N) ε) ≤ 2 * v / Real.log (N + 1) ^ 2 :=
  Econ.Granular.var_zipf_le P hN ε hmean hcov

end Econ.Audit
