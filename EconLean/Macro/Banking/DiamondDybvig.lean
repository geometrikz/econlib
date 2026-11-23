/-
# Bank runs (Diamond–Dybvig)

Diamond and Dybvig (1983), "Bank Runs, Deposit Insurance, and Liquidity",
JPE (Nobel 2022); Freixas–Rochet ch. 7; Allen–Gale ch. 3.

**The economics.** Three dates `0, 1, 2`. A unit mass of ex-ante identical
depositors each has one unit of goods at date 0. At date 1 each learns her
type: a fraction `λ ∈ (0, 1)` is *impatient* (values only date-1 consumption),
the rest are *patient* (value date-2 consumption, but can store goods from
date 1). The technology returns `R > 1` at date 2 per unit invested, or `1` if
liquidated at date 1.

**Liquidity insurance.** Ex ante, the planner maximizes
`λ u(c₁) + (1 − λ) u(c₂)` subject to `λ c₁ + (1 − λ) c₂ / R ≤ 1`.
`optimal_of_foc` proves the first-order condition `u'(c₁) = R u'(c₂)` plus a
binding budget characterizes the optimum for any concave increasing `u`. For
CRRA utility with relative risk aversion `γ > 1` the optimum is
`c₁* = 1/(λ + (1 − λ) R^{1/γ − 1})`, `c₂* = R^{1/γ} c₁*`, with
`1 < c₁* < c₂* < R` (`crra_optimum`): the bank offers more than the
liquidation value at date 1. This is the insurance a bank provides.

**Runs.** A bank offers the demand-deposit contract paying `r₁` per unit to
anyone withdrawing at date 1 (while it has assets), and splits what is left
among those who wait. If a fraction `f ≥ λ` withdraws at date 1 the bank
survives iff `f r₁ < 1`; waiting then pays `R (1 − f r₁)/(1 − f)`. We call `f`
an equilibrium in the symmetric patient strategies "all wait" (`f = λ`) or
"all run" (`f = 1`) when that strategy is a best response for each patient
depositor, who takes `f` as given:
* `goodEquilibrium_iff`: "all wait" is an equilibrium iff
  `r₁ (1 − λ + λR) ≤ R`. The optimal contract satisfies it.
* `runEquilibrium_iff`: "all run" is an equilibrium iff `r₁ ≥ 1`. So the
  optimal contract (`r₁ = c₁* > 1`) has **both** equilibria
  (`multiple_equilibria`): a run is a self-fulfilling prophecy.
* `suspension_waiting_strictly_better`: with **suspension of convertibility**
  (the bank pays at most the fraction `λ` at date 1), waiting is strictly
  better for a patient depositor whatever others do, so the run equilibrium
  disappears.

**Deviations from the paper.** Payments at date 1 are pro rata when the bank
fails (no sequential-service queue); equilibria are in symmetric pure
strategies of patient depositors; deposit insurance financed by taxation is
not formalized (suspension is the simpler mechanism with the same effect when
`λ` is known).
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

noncomputable section

namespace Econ
namespace DiamondDybvig

open Set Real

/-! ## Optimal risk sharing -/

/-- **Tangent-line inequality** for a concave function on `(0, ∞)` that is
differentiable at `c`. -/
theorem le_tangent {u : ℝ → ℝ} (hconc : ConcaveOn ℝ (Ioi 0) u) {c d x : ℝ} (hc : 0 < c)
    (hd : HasDerivAt u d c) (hx : 0 < x) : u x ≤ u c + d * (x - c) := by
  rcases lt_trichotomy x c with hlt | rfl | hgt
  · have := hconc.le_slope_of_hasDerivAt (mem_Ioi.2 hx) (mem_Ioi.2 hc) hlt hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hlt)] at this
    linarith
  · simp
  · have := hconc.slope_le_of_hasDerivAt (mem_Ioi.2 hc) (mem_Ioi.2 hx) hgt hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hgt)] at this
    linarith

/-- **The first-order condition characterizes optimal risk sharing.** If `u`
is concave and increasing (`u'(c₁) ≥ 0`), and `(c₁, c₂)` exhausts the budget
`λ c₁ + (1 − λ) c₂ / R = 1` with `u'(c₁) = R u'(c₂)`, then it maximizes
expected utility `λ u(c₁) + (1 − λ) u(c₂)` over all affordable positive
consumption plans. -/
theorem optimal_of_foc {u : ℝ → ℝ} (hconc : ConcaveOn ℝ (Ioi 0) u) {lam R c₁ c₂ d₁ d₂ : ℝ}
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1) (hR : 0 < R) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hd₁ : HasDerivAt u d₁ c₁) (hd₂ : HasDerivAt u d₂ c₂) (hfoc : d₁ = R * d₂) (hd₁0 : 0 ≤ d₁)
    (hbud : lam * c₁ + (1 - lam) * c₂ / R = 1) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hbx : lam * x₁ + (1 - lam) * x₂ / R ≤ 1) :
    lam * u x₁ + (1 - lam) * u x₂ ≤ lam * u c₁ + (1 - lam) * u c₂ := by
  have t₁ := le_tangent hconc hc₁ hd₁ hx₁
  have t₂ := le_tangent hconc hc₂ hd₂ hx₂
  have hd₂' : d₂ = d₁ / R := by rw [hfoc]; field_simp
  -- the gain is at most `d₁ (budget(x) − 1) ≤ 0`
  have key : lam * (d₁ * (x₁ - c₁)) + (1 - lam) * (d₂ * (x₂ - c₂)) =
      d₁ * ((lam * x₁ + (1 - lam) * x₂ / R) - (lam * c₁ + (1 - lam) * c₂ / R)) := by
    rw [hd₂']; field_simp; ring
  have : d₁ * ((lam * x₁ + (1 - lam) * x₂ / R) - (lam * c₁ + (1 - lam) * c₂ / R)) ≤ 0 := by
    rw [hbud]; exact mul_nonpos_of_nonneg_of_nonpos hd₁0 (by linarith)
  have h1 : 0 < 1 - lam := by linarith
  nlinarith [mul_le_mul_of_nonneg_left t₁ hlam₀.le, mul_le_mul_of_nonneg_left t₂ h1.le]

/-- CRRA utility `u(c) = c^{1−γ}/(1−γ)` (for `γ ≠ 1`). -/
def crra (γ c : ℝ) : ℝ := c ^ (1 - γ) / (1 - γ)

theorem hasDerivAt_crra {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (crra γ) (c ^ (-γ)) c := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  show HasDerivAt (fun x => x ^ (1 - γ) / (1 - γ)) _ c
  convert h using 1
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- CRRA utility is concave on `(0, ∞)` for `γ > 0`. -/
theorem concaveOn_crra {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≠ 1) : ConcaveOn ℝ (Ioi 0) (crra γ) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), deriv (crra γ) x = x ^ (-γ) :=
    fun x hx => (hasDerivAt_crra hγ1 hx).deriv
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx => (hasDerivAt_crra hγ1 hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun x hx => (hasDerivAt_crra hγ1 hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [hderiv a ha, hderiv b hb]
    exact rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- The CRRA optimum `c₁* = 1/(λ + (1 − λ) R^{1/γ − 1})`. -/
def c1star (lam R γ : ℝ) : ℝ := 1 / (lam + (1 - lam) * R ^ (1 / γ - 1))

/-- `c₂* = R^{1/γ} c₁*`. -/
def c2star (lam R γ : ℝ) : ℝ := R ^ (1 / γ) * c1star lam R γ

/-- **Optimal liquidity insurance with CRRA utility.** For `γ > 1`, `R > 1`:
`(c₁*, c₂*)` is the optimal risk-sharing allocation, and `1 < c₁* < c₂*`:
impatient depositors get more than the liquidation value `1`, patient ones
still get more than impatient ones. -/
theorem crra_optimum {lam R γ : ℝ} (hlam₀ : 0 < lam) (hlam₁ : lam < 1) (hR : 1 < R)
    (hγ : 1 < γ) :
    lam * c1star lam R γ + (1 - lam) * c2star lam R γ / R = 1 ∧
    1 < c1star lam R γ ∧ c1star lam R γ < c2star lam R γ ∧
    ∀ x₁ x₂ : ℝ, 0 < x₁ → 0 < x₂ → lam * x₁ + (1 - lam) * x₂ / R ≤ 1 →
      lam * crra γ x₁ + (1 - lam) * crra γ x₂ ≤
        lam * crra γ (c1star lam R γ) + (1 - lam) * crra γ (c2star lam R γ) := by
  have hR0 : 0 < R := by linarith
  have hγ0 : 0 < γ := by linarith
  have h1 : 0 < 1 - lam := by linarith
  set e := R ^ (1 / γ - 1)
  have he0 : 0 < e := rpow_pos_of_pos hR0 _
  have he1 : e < 1 := rpow_lt_one_of_one_lt_of_neg hR (by
    rw [sub_neg, div_lt_one hγ0]; exact hγ)
  have hden : 0 < lam + (1 - lam) * e := by positivity
  have hden1 : lam + (1 - lam) * e < 1 := by nlinarith
  have hc1 : 0 < c1star lam R γ := div_pos one_pos hden
  have hRg : 1 < R ^ (1 / γ) := one_lt_rpow hR (by positivity)
  have hc2 : 0 < c2star lam R γ := mul_pos (by linarith) hc1
  -- `R^{1/γ} / R = R^{1/γ − 1} = e`
  have hRe : R ^ (1 / γ) / R = e := by rw [← rpow_sub_one hR0.ne']
  have hbud : lam * c1star lam R γ + (1 - lam) * c2star lam R γ / R = 1 := by
    simp only [c2star]
    rw [show (1 - lam) * (R ^ (1 / γ) * c1star lam R γ) / R = (1 - lam) * c1star lam R γ * e by
      rw [← hRe]; ring]
    have hc : c1star lam R γ * (lam + (1 - lam) * e) = 1 := by
      simp only [c1star]; exact one_div_mul_cancel hden.ne'
    linear_combination hc
  refine ⟨hbud, ?_, ?_, ?_⟩
  · simp only [c1star]; rw [lt_div_iff₀ hden]; linarith
  · simp only [c2star]; nlinarith
  · intro x₁ x₂ hx₁ hx₂ hbx
    have hγ1 : γ ≠ 1 := by linarith
    refine optimal_of_foc (concaveOn_crra hγ0 hγ1) hlam₀ hlam₁ hR0 hc1 hc2
      (hasDerivAt_crra hγ1 hc1) (hasDerivAt_crra hγ1 hc2) ?_
      (rpow_nonneg hc1.le _) hbud hx₁ hx₂ hbx
    -- FOC: `c₁^{−γ} = R (R^{1/γ} c₁)^{−γ}`
    simp only [c2star]
    rw [mul_rpow (rpow_nonneg hR0.le _) hc1.le, ← rpow_mul hR0.le,
      show 1 / γ * -γ = -1 by field_simp, rpow_neg_one]
    field_simp

/-! ## The demand-deposit game -/

/-- The banking environment. -/
structure Bank where
  /-- Fraction of impatient depositors. -/
  lam : ℝ
  /-- Long-run gross return. -/
  R : ℝ
  /-- Date-1 payment promised per deposit. -/
  r₁ : ℝ
  hlam₀ : 0 < lam
  hlam₁ : lam < 1
  hR : 1 < R
  hr₁ : 0 < r₁

namespace Bank

variable (B : Bank)

/-- Per-capita payment to those who wait, when a fraction `f < 1` withdraws at
date 1 and the bank survives (`f r₁ < 1`). -/
def latePay (f : ℝ) : ℝ := B.R * (1 - f * B.r₁) / (1 - f)

/-- Waiting is a best response for a patient depositor when the fraction `f`
withdraws: the bank is not insolvent at date 1 (`f r₁ ≤ 1`; otherwise waiters
get nothing while early withdrawers get, under sequential service, the expected
payment `min(r₁, 1/f) > 0`) and, if anyone waits, waiting pays at least `r₁`. -/
def WaitIsBest (f : ℝ) : Prop := f * B.r₁ ≤ 1 ∧ (f < 1 → B.r₁ ≤ B.latePay f)

/-- Withdrawing is a best response when the fraction `f` withdraws: either the
bank is strictly insolvent at date 1 (`f r₁ > 1`: waiters get `0`, while an
early withdrawer gets the sequential-service expected payment `min(r₁, 1/f) > 0`),
or some depositors wait (`f < 1`) and waiting pays at most `r₁`.

Boundary convention: at `f = 1` with `f r₁ = 1` the bank exactly breaks even.
The waiting payoff there is the limit of `R (1 − f r₁)/(1 − f)` as `f → 1`,
which is `R > 1 = r₁`, so running is **not** a best response. (We do not use
Lean's junk value `latePay 1 = 0/0 = 0`.) -/
-- `WaitIsBest` and `RunIsBest` are not complements: both hold when a depositor
-- is exactly indifferent (`latePay f = r₁`). Only `f ∈ [λ, 1]` is economically
-- meaningful; the equilibrium notions below use `f = λ` and `f = 1`.
def RunIsBest (f : ℝ) : Prop := 1 < f * B.r₁ ∨ (f < 1 ∧ B.latePay f ≤ B.r₁)

/-- "All patient depositors wait" (`f = λ`) is an equilibrium. -/
def GoodEquilibrium : Prop := B.WaitIsBest B.lam

/-- "All depositors run" (`f = 1`) is an equilibrium. -/
def RunEquilibrium : Prop := B.RunIsBest 1

/-- **The good equilibrium exists iff `r₁ (1 − λ + λR) ≤ R`.** -/
theorem goodEquilibrium_iff : B.GoodEquilibrium ↔ B.r₁ * (1 - B.lam + B.lam * B.R) ≤ B.R := by
  have h1 : 0 < 1 - B.lam := by linarith [B.hlam₁]
  have := B.hlam₀; have := B.hR; have := B.hr₁
  unfold GoodEquilibrium WaitIsBest latePay
  constructor
  · rintro ⟨-, h⟩
    have := h B.hlam₁
    rw [le_div_iff₀ h1] at this
    nlinarith
  · intro h
    refine ⟨?_, fun _ => ?_⟩
    · -- `λ r₁ ≤ λR/(1 − λ + λR) < 1`
      nlinarith
    · rw [le_div_iff₀ h1]; nlinarith

/-- **The run equilibrium exists iff `r₁ > 1`:** if the bank promises more than
the liquidation value, a run exhausts its assets and running is optimal. With
`r₁ = 1` (no liquidity insurance) there is no run, as in Diamond–Dybvig (1983). -/
theorem runEquilibrium_iff : B.RunEquilibrium ↔ 1 < B.r₁ := by
  unfold RunEquilibrium RunIsBest
  constructor
  · rintro (h | ⟨h, -⟩)
    · linarith
    · exact absurd h (lt_irrefl 1)
  · intro h; left; linarith

/-- **Multiple equilibria.** If the bank offers the optimal CRRA contract
(`r₁ = c₁*`, `γ > 1`), both the good equilibrium and the run equilibrium
exist. -/
theorem multiple_equilibria {γ : ℝ} (hγ : 1 < γ) (hr : B.r₁ = c1star B.lam B.R γ) :
    B.GoodEquilibrium ∧ B.RunEquilibrium := by
  obtain ⟨hbud, h1, h12, -⟩ := crra_optimum B.hlam₀ B.hlam₁ B.hR hγ
  have hR0 : 0 < B.R := by linarith [B.hR]
  have h1l : 0 < 1 - B.lam := by linarith [B.hlam₁]
  refine ⟨(B.goodEquilibrium_iff).2 ?_, (B.runEquilibrium_iff).2 (hr ▸ h1)⟩
  -- from the budget: `c₂* = R (1 − λ c₁*)/(1 − λ) ≥ c₁*`
  rw [hr]
  set c1 := c1star B.lam B.R γ
  set c2 := c2star B.lam B.R γ
  have hc2 : c2 = B.R * (1 - B.lam * c1) / (1 - B.lam) := by
    rw [eq_div_iff h1l.ne']
    field_simp at hbud
    linarith
  rw [hc2, lt_div_iff₀ h1l] at h12
  nlinarith

/-! ## Suspension of convertibility -/

/-- With **suspension of convertibility** the bank serves at most the fraction
`λ` at date 1. If a fraction `f ≥ λ` tries to withdraw, each is served with
probability `λ / f` (getting `r₁`), and everybody not served at date 1 shares
the date-2 return `R (1 − λ r₁)`, i.e. gets `latePay λ`. -/
def suspensionEarlyPay (f : ℝ) : ℝ := B.lam / f * B.r₁ + (1 - B.lam / f) * B.latePay B.lam

/-- **Suspension of convertibility eliminates runs.** If the contract satisfies
`r₁ (1 − λ + λR) < R` (strictly: e.g. the CRRA optimum), then under suspension
a patient depositor strictly prefers waiting, whatever fraction `f ≥ λ`
of depositors tries to withdraw: running is never a best response. -/
theorem suspension_waiting_strictly_better (h : B.r₁ * (1 - B.lam + B.lam * B.R) < B.R)
    {f : ℝ} (hf : B.lam ≤ f) :
    B.suspensionEarlyPay f < B.latePay B.lam := by
  have h1 : 0 < 1 - B.lam := by linarith [B.hlam₁]
  have := B.hlam₀; have := B.hR; have := B.hr₁
  have hf0 : 0 < f := by linarith
  have hlt : B.r₁ < B.latePay B.lam := by
    unfold latePay
    rw [lt_div_iff₀ h1]; nlinarith
  unfold suspensionEarlyPay
  have hq : 0 < B.lam / f := div_pos B.hlam₀ hf0
  nlinarith

end Bank

/-- **Non-vacuity.** `λ = 1/2`, `R = 2`, `γ = 2`: the optimal contract pays
`c₁* = 2/(1 + √2) ≈ 1.17 > 1` and has both a good and a run equilibrium. -/
example : (1 : ℝ) < c1star (1 / 2) 2 2 := (crra_optimum (by norm_num) (by norm_num) (by norm_num)
  (by norm_num)).2.1

end DiamondDybvig
end Econ

end
