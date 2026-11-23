/-
# Firm heterogeneity and selection into exporting (Melitz)

Melitz (2003), "The Impact of Trade on Intra-Industry Reallocations and
Aggregate Industry Productivity", Econometrica; Melitz–Redding (2014),
Handbook of International Economics, §2 (Pareto case);
Chaney (2008), AER.

**Setting.** Firms pay `f_e > 0` to draw productivity `φ` from a Pareto
distribution with shape `k` and scale `φ_min > 0`
(density `k φ_min^k φ^{−k−1}` on `[φ_min, ∞)`), with CES demand elasticity
`σ > 1` and `k > σ − 1`. Producing for the home market costs `f > 0` per
period; exporting to each of `n` partners costs `f_x > 0` plus iceberg cost
`τ > 1`. Firms die at rate `δ > 0`. With zero-profit cutoffs `φ*` (domestic)
and `φ_x*` (export), profits are `f((φ/φ*)^{σ−1} − 1)` and
`f_x((φ/φ_x*)^{σ−1} − 1)`, and the cutoffs satisfy
`φ_x* = Λ φ*` with `Λ = τ (f_x/f)^{1/(σ−1)}`. Free entry requires the
expected value of entry to equal `f_e`:
`f J(φ*) + n f_x J(φ_x*) = δ f_e` with
`J(φ) = ∫_φ^∞ ((x/φ)^{σ−1} − 1) dG(x)`.

**Results.**
* `selection_iff`: exporters are a strict subset of producers
  (`φ_x* > φ*`) iff `τ^{σ−1} f_x > f`.
* `J_eq`: for Pareto draws and `φ ≥ φ_min`,
  `J(φ) = (σ − 1)/(k − σ + 1) · (φ_min/φ)^k`.
* `surv_eq_integral`, `exporter_share`: the fraction of producers that export is `Λ^{−k}`.
* `trade_raises_cutoff`: opening to trade (`n > 0`) strictly raises the
  domestic survival cutoff relative to autarky: the least productive firms
  exit and market shares reallocate toward more productive firms, raising
  aggregate productivity.

**Deviations.** Steady state only; the profit expressions in terms of the
cutoffs (which follow from CES demand and the zero-profit conditions) are
taken as given; symmetric countries.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section

namespace Econ
namespace Melitz

open Real MeasureTheory Set

/-- Parameters. -/
structure Params where
  σ : ℝ
  k : ℝ
  φmin : ℝ
  f : ℝ
  fx : ℝ
  τ : ℝ
  hσ : 1 < σ
  hk : σ - 1 < k
  hφmin : 0 < φmin
  hf : 0 < f
  hfx : 0 < fx
  hτ : 1 < τ

namespace Params

variable (P : Params)

/-- Pareto density on `[φ_min, ∞)` (the formula is only used above `φ_min`;
all results about `J` assume the cutoff is at least `φ_min`). -/
def pdf (x : ℝ) : ℝ := P.k * P.φmin ^ P.k * x ^ (-P.k - 1)

/-- Expected (normalized) excess profit of entry above cutoff `φ`. -/
def J (φ : ℝ) : ℝ := ∫ x in Ioi φ, ((x / φ) ^ (P.σ - 1) - 1) * P.pdf x

/-- Ratio of the export cutoff to the domestic cutoff. -/
def Λ : ℝ := P.τ * (P.fx / P.f) ^ (1 / (P.σ - 1))

theorem k_pos : 0 < P.k := by linarith [P.hσ, P.hk]

/-- **Selection into exporting.** -/
theorem selection_iff : 1 < P.Λ ↔ P.f < P.τ ^ (P.σ - 1) * P.fx := by
  have hs : 0 < P.σ - 1 := by linarith [P.hσ]
  have hτ : 0 < P.τ := by linarith [P.hτ]
  have hr : 0 < P.fx / P.f := div_pos P.hfx P.hf
  -- `Λ^{σ−1} = τ^{σ−1} f_x/f`
  have hΛ : P.Λ ^ (P.σ - 1) = P.τ ^ (P.σ - 1) * P.fx / P.f := by
    rw [Λ, mul_rpow hτ.le (rpow_nonneg hr.le _), ← rpow_mul hr.le, one_div_mul_cancel hs.ne',
      rpow_one, mul_div_assoc]
  have hΛpos : 0 < P.Λ := mul_pos hτ (rpow_pos_of_pos hr _)
  constructor
  · intro h
    have := one_lt_rpow h hs
    rw [hΛ, lt_div_iff₀ P.hf, one_mul] at this
    exact this
  · intro h
    have h1 : 1 < P.Λ ^ (P.σ - 1) := by rw [hΛ, lt_div_iff₀ P.hf, one_mul]; exact h
    by_contra hle; push Not at hle
    have := rpow_le_one hΛpos.le hle hs.le
    linarith

/-- **The Pareto entry integral.** -/
theorem J_eq {φ : ℝ} (hφ : P.φmin ≤ φ) :
    P.J φ = (P.σ - 1) / (P.k - P.σ + 1) * (P.φmin / φ) ^ P.k := by
  have hφ0 : 0 < φ := P.hφmin.trans_le hφ
  have hk := P.k_pos
  have a1 : P.σ - 1 - P.k - 1 < -1 := by linarith [P.hk]
  have a2 : -P.k - 1 < -1 := by linarith
  have hcongr : EqOn (fun x => ((x / φ) ^ (P.σ - 1) - 1) * P.pdf x)
      (fun x => P.k * P.φmin ^ P.k * φ ^ (-(P.σ - 1)) * x ^ (P.σ - 1 - P.k - 1) -
        P.k * P.φmin ^ P.k * x ^ (-P.k - 1)) (Ioi φ) := by
    intro x hx
    have hx0 : 0 < x := hφ0.trans hx
    simp only [pdf]
    rw [div_rpow hx0.le hφ0.le, rpow_neg hφ0.le,
      show P.σ - 1 - P.k - 1 = (P.σ - 1) + (-P.k - 1) by ring, rpow_add hx0]
    field_simp
  rw [J, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_sub ((integrableOn_Ioi_rpow_of_lt a1 hφ0).const_mul _)
      ((integrableOn_Ioi_rpow_of_lt a2 hφ0).const_mul _),
    integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt a1 hφ0,
    integral_Ioi_rpow_of_lt a2 hφ0]
  have e1 : P.σ - 1 - P.k - 1 + 1 = (P.σ - 1) + -P.k := by ring
  have e2 : -P.k - 1 + 1 = -P.k := by ring
  rw [e1, e2, rpow_add hφ0, div_rpow P.hφmin.le hφ0.le, rpow_neg hφ0.le, rpow_neg hφ0.le]
  have hk1 : P.k - P.σ + 1 ≠ 0 := by linarith [P.hk]
  have h3 : P.σ - 1 + -P.k ≠ 0 := by linarith [P.hk]
  have hp : 0 < φ ^ (P.σ - 1) := rpow_pos_of_pos hφ0 _
  have hq : 0 < φ ^ P.k := rpow_pos_of_pos hφ0 _
  field_simp
  ring

/-- Pareto survival function `1 − G(φ)` for `φ ≥ φ_min`. -/
def surv (φ : ℝ) : ℝ := (P.φmin / φ) ^ P.k

theorem surv_eq_integral {φ : ℝ} (hφ : P.φmin ≤ φ) : ∫ x in Ioi φ, P.pdf x = P.surv φ := by
  have hφ0 : 0 < φ := P.hφmin.trans_le hφ
  have hk := P.k_pos
  have a2 : -P.k - 1 < -1 := by linarith
  simp only [pdf]
  rw [integral_const_mul, integral_Ioi_rpow_of_lt a2 hφ0, surv, div_rpow P.hφmin.le hφ0.le,
    show -P.k - 1 + 1 = -P.k by ring, rpow_neg hφ0.le]
  field_simp

/-- **Share of exporters** among producers: `(1 − G(Λφ*))/(1 − G(φ*)) = Λ^{−k}`. -/
theorem exporter_share {φ : ℝ} (hφ : 0 < φ) (hΛ : 0 < P.Λ) :
    P.surv (P.Λ * φ) / P.surv φ = P.Λ ^ (-P.k) := by
  simp only [surv]
  rw [div_mul_eq_div_div_swap, div_rpow (div_pos P.hφmin hφ).le hΛ.le, rpow_neg hΛ.le]
  have : 0 < (P.φmin / φ) ^ P.k := rpow_pos_of_pos (div_pos P.hφmin hφ) _
  field_simp

/-- **Trade raises the survival cutoff.** Let `φa` be the autarky cutoff
(`f J(φa) = δ f_e`) and `φs` the cutoff with `n > 0` export markets
(`f J(φs) + n f_x J(Λ φs) = δ f_e`), with exporting selective (`Λ ≥ 1`) and
both cutoffs above `φ_min`. Then `φa < φs`. -/
theorem trade_raises_cutoff {δ fe n φa φs : ℝ} (hn : 0 < n)
    (hΛ : 1 ≤ P.Λ) (ha : P.φmin ≤ φa) (hs : P.φmin ≤ φs)
    (haut : P.f * P.J φa = δ * fe) (hopen : P.f * P.J φs + n * P.fx * P.J (P.Λ * φs) = δ * fe) :
    φa < φs := by
  have hφs0 : 0 < φs := P.hφmin.trans_le hs
  have hφa0 : 0 < φa := P.hφmin.trans_le ha
  have hsx : P.φmin ≤ P.Λ * φs := hs.trans (le_mul_of_one_le_left hφs0.le hΛ)
  have hC : 0 < (P.σ - 1) / (P.k - P.σ + 1) := div_pos (by linarith [P.hσ]) (by linarith [P.hk])
  rw [P.J_eq ha] at haut
  rw [P.J_eq hs, P.J_eq hsx] at hopen
  have hx : 0 < n * P.fx * ((P.σ - 1) / (P.k - P.σ + 1) * (P.φmin / (P.Λ * φs)) ^ P.k) := by
    have := rpow_pos_of_pos (div_pos P.hφmin (mul_pos (by linarith : (0:ℝ) < P.Λ) hφs0)) P.k
    have := P.hfx
    positivity
  -- hence `(φmin/φs)^k < (φmin/φa)^k`
  have hlt : (P.φmin / φs) ^ P.k < (P.φmin / φa) ^ P.k := by
    have := P.hf
    have h1 : P.f * ((P.σ - 1) / (P.k - P.σ + 1) * (P.φmin / φs) ^ P.k) <
        P.f * ((P.σ - 1) / (P.k - P.σ + 1) * (P.φmin / φa) ^ P.k) := by linarith
    have h2 := lt_of_mul_lt_mul_left h1 P.hf.le
    exact lt_of_mul_lt_mul_left h2 hC.le
  have hlt' : P.φmin / φs < P.φmin / φa :=
    (rpow_lt_rpow_iff (div_pos P.hφmin hφs0).le (div_pos P.hφmin hφa0).le P.k_pos).1 hlt
  exact (div_lt_div_iff_of_pos_left P.hφmin hφs0 hφa0).1 hlt'

end Params
end Melitz
end Econ

end
