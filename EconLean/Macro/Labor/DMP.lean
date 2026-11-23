/-
# Steady-state unemployment, the DMP model, and the Hosios condition

Pissarides, *Equilibrium Unemployment Theory* (2000), ch. 1 and §8.1;
Mortensen–Pissarides (1994); Hosios (1990); Ljungqvist–Sargent ch. 28.

**Flows.** Workers lose jobs at rate `s` and find them at rate `f`. The
unemployment rate moves by `u' = u + s (1 − u) − f u`; its steady state is
`u* = s / (s + f)` (`steadyState_unemployment`), and it is globally stable
when `0 < s + f < 2` (`tendsto_unemployment`).

**Matching.** Unemployed `u` and vacancies `v` meet according to a
Cobb–Douglas matching function `m(u, v) = A u^η v^{1−η}`. With labour-market
tightness `θ = v/u`, the job-finding rate is `f(θ) = A θ^{1−η}` and the
vacancy-filling rate `q(θ) = A θ^{−η}`; `η ∈ (0,1)` is the elasticity of
matches with respect to unemployment. Steady-state unemployment at tightness
`θ` is `u(θ) = s / (s + f(θ))` and vacancies are `v(θ) = θ u(θ)`. As `θ` rises,
`u` falls and `v` rises (`beveridge`): the **Beveridge curve**, the locus of
steady-state `(u, v)` pairs, slopes down.

**Equilibrium** (continuous time, Pissarides ch. 1). Free entry of vacancies
(cost `c` per period) and Nash bargaining with worker power `β ∈ [0, 1)` give
the job-creation condition

    c (r + s) θ^η / A + β c θ = (1 − β)(y − b),

where `y` is match output, `b` the value of unemployment, `r` the interest
rate. `existsUnique_equilibrium`: a unique `θ* > 0` solves it (when `y > b`);
`equilibrium_strictAnti_β`: more worker bargaining power means fewer
vacancies.

**Efficiency: the Hosios condition.** A planner who maximizes steady-state
net output `W(θ) = y (1 − u) + b u − c θ u` (the `r → 0` welfare criterion of
Pissarides §8.1) chooses the `θ` that solves the job-creation condition with
`r = 0` and `β = η` (`isEfficient_iff`). Hence (`hosios`): **the equilibrium is
efficient iff the worker's bargaining power equals the elasticity of the
matching function with respect to unemployment, `β = η`.**

**Deviations from the textbook.** Cobb–Douglas matching (the standard
empirical case; Hosios's general condition is `β = −θ q'(θ)/q(θ)`, which is
`η` here); efficiency is evaluated with the steady-state (`r → 0`) welfare
criterion, as in Pissarides §8.1, so `hosios` compares it with the `r = 0`
equilibrium. The flow dynamics are in discrete time. The Hosios condition with
discounting (`r > 0`) and a present-value planner is proved in
`Macro/Labor/HosiosDiscounted.lean`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace DMP

open Set Filter Topology Real

/-! ## Unemployment flows -/

/-- Unemployment next period, given separation rate `s` and finding rate `f`. -/
def flow (s f u : ℝ) : ℝ := u + s * (1 - u) - f * u

/-- **Steady-state unemployment `u* = s/(s + f)`** is the unique fixed point of
the flow equation (inflows `s (1 − u)` = outflows `f u`). -/
theorem steadyState_unemployment {s f u : ℝ} (hsf : 0 < s + f) :
    flow s f u = u ↔ u = s / (s + f) := by
  unfold flow
  rw [eq_div_iff hsf.ne']
  constructor <;> intro h <;> linarith

/-- **Convergence to steady-state unemployment** when `0 < s + f < 2`:
`u_t − u* = (1 − s − f)^t (u₀ − u*)`. -/
theorem tendsto_unemployment {s f : ℝ} (h0 : 0 < s + f) (h2 : s + f < 2) (u₀ : ℝ) :
    Tendsto (fun t : ℕ => (flow s f)^[t] u₀) atTop (𝓝 (s / (s + f))) := by
  set ustar := s / (s + f)
  have hgap : ∀ t : ℕ, (flow s f)^[t] u₀ = ustar + (1 - s - f) ^ t * (u₀ - ustar) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      simp only [flow, ustar]
      field_simp
      ring
  have hr : |1 - s - f| < 1 := by rw [abs_lt]; constructor <;> linarith
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).mul_const (u₀ - ustar)
  rw [zero_mul] at this
  simpa [hgap] using (tendsto_const_nhds (x := ustar)).add this

/-! ## The DMP economy -/

/-- Parameters of the DMP model with Cobb–Douglas matching. -/
structure Economy where
  /-- Matching efficiency. -/
  A : ℝ
  /-- Elasticity of matches with respect to unemployment. -/
  η : ℝ
  /-- Separation rate. -/
  s : ℝ
  /-- Vacancy cost. -/
  c : ℝ
  /-- Match output. -/
  y : ℝ
  /-- Value of non-work (unemployment benefit / home production). -/
  b : ℝ
  hA : 0 < A
  hη₀ : 0 < η
  hη₁ : η < 1
  hs : 0 < s
  hc : 0 < c
  hyb : b < y

namespace Economy

variable (E : Economy)

/-- Job-finding rate `f(θ) = A θ^{1−η}`. -/
def findRate (θ : ℝ) : ℝ := E.A * θ ^ (1 - E.η)

/-- Vacancy-filling rate `q(θ) = A θ^{−η}`. -/
def fillRate (θ : ℝ) : ℝ := E.A * θ ^ (-E.η)

/-- Steady-state unemployment at tightness `θ`. -/
def unemp (θ : ℝ) : ℝ := E.s / (E.s + E.findRate θ)

/-- Steady-state vacancies at tightness `θ`: `v = θ u(θ)`. -/
def vac (θ : ℝ) : ℝ := θ * E.unemp θ

/-- `f(θ) = θ q(θ)`: matches per unemployed = tightness × matches per vacancy. -/
theorem findRate_eq {θ : ℝ} (hθ : 0 < θ) : E.findRate θ = θ * E.fillRate θ := by
  simp only [findRate, fillRate, rpow_sub hθ, rpow_neg hθ.le, rpow_one]
  field_simp

/-- Left side of the job-creation condition with interest rate `r` and
bargaining power `β`: `c (r + s) θ^η / A + β c θ`. Equivalently
`(c / q(θ)) (r + s + β f(θ))`. -/
def jc (r β θ : ℝ) : ℝ := E.c * (r + E.s) * θ ^ E.η / E.A + β * E.c * θ

/-- The job-creation condition in its textbook form: the expected vacancy
cost `c/q(θ)` equals the value of a filled job `(y − w)/(r + s)` with the Nash
wage `w = (1 − β) b + β (y + c θ)`. -/
theorem jc_iff_textbook {r β θ : ℝ} (hθ : 0 < θ) (hr : 0 ≤ r) :
    E.jc r β θ = (1 - β) * (E.y - E.b) ↔
      E.c / E.fillRate θ = (E.y - ((1 - β) * E.b + β * (E.y + E.c * θ))) / (r + E.s) := by
  have hrs : 0 < r + E.s := by linarith [E.hs]
  have hθη : 0 < θ ^ E.η := rpow_pos_of_pos hθ _
  have hA := E.hA
  have hq' : E.fillRate θ = E.A / θ ^ E.η := by
    simp only [fillRate]; rw [rpow_neg hθ.le, div_eq_mul_inv]
  rw [hq', div_div_eq_mul_div, eq_div_iff hrs.ne', jc]
  constructor
  · intro h
    have e : E.c * θ ^ E.η / E.A * (r + E.s) = E.c * (r + E.s) * θ ^ E.η / E.A := by ring
    rw [e]; linarith
  · intro h
    have e : E.c * θ ^ E.η / E.A * (r + E.s) = E.c * (r + E.s) * θ ^ E.η / E.A := by ring
    rw [e] at h; linarith

theorem jc_strictMonoOn {r β : ℝ} (hr : 0 ≤ r) (hβ : 0 ≤ β) : StrictMonoOn (E.jc r β) (Ici 0) := by
  intro a ha b hb hab
  have hrs : 0 < r + E.s := by linarith [E.hs]
  have h1 : a ^ E.η < b ^ E.η := rpow_lt_rpow ha hab E.hη₀
  have h2 : E.c * (r + E.s) * a ^ E.η / E.A < E.c * (r + E.s) * b ^ E.η / E.A :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h1 (mul_pos E.hc hrs)) E.hA
  have h3 : β * E.c * a ≤ β * E.c * b := mul_le_mul_of_nonneg_left hab.le (mul_nonneg hβ E.hc.le)
  simp only [jc]; linarith

theorem continuous_jc (r β : ℝ) : Continuous (E.jc r β) := by
  unfold jc
  have := Real.continuous_rpow_const E.hη₀.le
  fun_prop

/-- `θ` is a **DMP equilibrium** with interest rate `r` and bargaining power
`β`: positive and satisfying the job-creation condition. -/
def IsEquilibrium (r β θ : ℝ) : Prop := 0 < θ ∧ E.jc r β θ = (1 - β) * (E.y - E.b)

/-- **Existence and uniqueness of equilibrium tightness.** -/
theorem existsUnique_equilibrium {r β : ℝ} (hr : 0 ≤ r) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) :
    ∃! θ, E.IsEquilibrium r β θ := by
  have hrs : 0 < r + E.s := by linarith [E.hs]
  set K := (1 - β) * (E.y - E.b)
  have hK : 0 < K := mul_pos (by linarith) (by linarith [E.hyb])
  -- an upper point where `jc ≥ K`
  set θ₁ := (K * E.A / (E.c * (r + E.s))) ^ (1 / E.η)
  have hx : 0 < K * E.A / (E.c * (r + E.s)) := div_pos (mul_pos hK E.hA) (mul_pos E.hc hrs)
  have hθ₁ : 0 < θ₁ := rpow_pos_of_pos hx _
  have hθ₁η : θ₁ ^ E.η = K * E.A / (E.c * (r + E.s)) := by
    rw [← rpow_mul hx.le, one_div_mul_cancel E.hη₀.ne', rpow_one]
  have hup : K ≤ E.jc r β θ₁ := by
    simp only [jc, hθ₁η]
    have : E.c * (r + E.s) * (K * E.A / (E.c * (r + E.s))) / E.A = K := by
      have := E.hA; have := E.hc; field_simp
    rw [this]
    have : 0 ≤ β * E.c * θ₁ := by have := E.hc; positivity
    linarith
  have h0 : E.jc r β 0 = 0 := by simp [jc, zero_rpow E.hη₀.ne']
  obtain ⟨θ, hθmem, hθ⟩ := intermediate_value_Icc hθ₁.le (E.continuous_jc r β).continuousOn
    ⟨by rw [h0]; exact hK.le, hup⟩
  have hθ0 : 0 < θ := by
    rcases hθmem.1.eq_or_lt with h | h
    · rw [← h, h0] at hθ; linarith
    · exact h
  refine ⟨θ, ⟨hθ0, hθ⟩, fun θ' ⟨hθ'0, hθ'⟩ => ?_⟩
  exact (E.jc_strictMonoOn hr hβ₀).injOn (mem_Ici.2 hθ'0.le) (mem_Ici.2 hθ0.le) (hθ'.trans hθ.symm)

/-- **More worker bargaining power, lower tightness** (and so higher
unemployment along the Beveridge curve). -/
theorem equilibrium_strictAnti_β {r β₁ β₂ θ₁ θ₂ : ℝ} (hr : 0 ≤ r) (hβ₁ : 0 ≤ β₁)
    (hβ : β₁ < β₂) (h₁ : E.IsEquilibrium r β₁ θ₁) (h₂ : E.IsEquilibrium r β₂ θ₂) : θ₂ < θ₁ := by
  by_contra hle
  push Not at hle
  have hmono := (E.jc_strictMonoOn hr hβ₁).monotoneOn (mem_Ici.2 h₁.1.le) (mem_Ici.2 h₂.1.le) hle
  have : E.jc r β₁ θ₂ ≤ E.jc r β₂ θ₂ := by
    simp only [jc]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ.le E.hc.le) h₂.1.le
    linarith
  have := h₁.2; have := h₂.2
  have hyb := E.hyb
  nlinarith

/-- Higher tightness means lower steady-state unemployment. -/
theorem unemp_strictAntiOn : StrictAntiOn E.unemp (Ioi 0) := by
  intro a ha b hb hab
  have hfa : 0 < E.findRate a := mul_pos E.hA (rpow_pos_of_pos ha _)
  have hfab : E.findRate a < E.findRate b :=
    mul_lt_mul_of_pos_left (rpow_lt_rpow ha.le hab (by linarith [E.hη₁])) E.hA
  exact div_lt_div_of_pos_left E.hs (by linarith [E.hs]) (by linarith)

/-- Vacancies rise with tightness: `v(θ) = s / (s/θ + A θ^{−η})`, and both
terms of the denominator fall in `θ`. -/
theorem vac_strictMonoOn : StrictMonoOn E.vac (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have key : ∀ x : ℝ, 0 < x → E.vac x = E.s / (E.s / x + E.A * x ^ (-E.η)) := by
    intro x hx
    have hfx : E.findRate x = x * (E.A * x ^ (-E.η)) := by
      have := E.findRate_eq hx; simpa [fillRate] using this
    have hq : 0 < E.A * x ^ (-E.η) := mul_pos E.hA (rpow_pos_of_pos hx _)
    simp only [vac, unemp, hfx]
    have : 0 < E.s / x + E.A * x ^ (-E.η) := by positivity [E.hs]
    field_simp
  rw [key a ha', key b hb']
  have h1 : E.s / b < E.s / a := div_lt_div_of_pos_left E.hs ha' hab
  have h2 : b ^ (-E.η) < a ^ (-E.η) := rpow_lt_rpow_of_neg ha' hab (by linarith [E.hη₀])
  have hqb : 0 < E.A * b ^ (-E.η) := mul_pos E.hA (rpow_pos_of_pos hb' _)
  have hsb : 0 < E.s / b := div_pos E.hs hb'
  apply div_lt_div_of_pos_left E.hs (by linarith)
  nlinarith [E.hA]

/-- **The Beveridge curve slopes down.** Along the steady-state locus, any two
tightness levels `θ < θ'` give strictly more vacancies and strictly less
unemployment at `θ'`: in `(u, v)` space, vacancies and unemployment move in
opposite directions. -/
theorem beveridge {θ θ' : ℝ} (hθ : 0 < θ) (hlt : θ < θ') :
    E.unemp θ' < E.unemp θ ∧ E.vac θ < E.vac θ' :=
  ⟨E.unemp_strictAntiOn hθ (lt_trans hθ hlt) hlt,
    E.vac_strictMonoOn hθ (lt_trans hθ hlt) hlt⟩

/-! ## Efficiency and the Hosios condition -/

/-- Steady-state net output per member of the labour force:
`W(θ) = y (1 − u) + b u − c θ u` with `u = s/(s + f(θ))`, i.e.
`W(θ) = b + ((y − b) f(θ) − c s θ)/(s + f(θ))`. -/
def welfare (θ : ℝ) : ℝ := E.b + ((E.y - E.b) * E.findRate θ - E.c * E.s * θ) / (E.s + E.findRate θ)

theorem welfare_eq {θ : ℝ} (hθ : 0 ≤ θ) :
    E.welfare θ = E.y * (1 - E.unemp θ) + E.b * E.unemp θ - E.c * θ * E.unemp θ := by
  have hf : 0 ≤ E.findRate θ := mul_nonneg E.hA.le (rpow_nonneg hθ _)
  have hsf : 0 < E.s + E.findRate θ := by linarith [E.hs]
  simp only [welfare, unemp]
  field_simp
  ring

/-- `θ` is **efficient**: positive and maximizes steady-state net output over
all positive tightness levels. -/
def IsEfficient (θ : ℝ) : Prop := 0 < θ ∧ ∀ θ', 0 < θ' → E.welfare θ' ≤ E.welfare θ

/-- The derivative of welfare: `W'(θ) = s f(θ) / (θ (s + f(θ))²) · P(θ)` with
`P(θ) = (1 − η)(y − b) − jc(0, η, θ)`. -/
theorem hasDerivAt_welfare {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt E.welfare
      (E.s * E.findRate θ / (θ * (E.s + E.findRate θ) ^ 2) *
        ((1 - E.η) * (E.y - E.b) - E.jc 0 E.η θ)) θ := by
  have hA := E.hA
  have hf : 0 < E.findRate θ := mul_pos E.hA (rpow_pos_of_pos hθ _)
  have hsf : 0 < E.s + E.findRate θ := by linarith [E.hs]
  -- derivative of `f(θ) = A θ^{1−η}` is `A (1 − η) θ^{−η}`
  have hdf : HasDerivAt E.findRate (E.A * ((1 - E.η) * θ ^ (1 - E.η - 1))) θ :=
    (Real.hasDerivAt_rpow_const (Or.inl hθ.ne')).const_mul E.A
  have hN : HasDerivAt (fun x => (E.y - E.b) * E.findRate x - E.c * E.s * x)
      ((E.y - E.b) * (E.A * ((1 - E.η) * θ ^ (1 - E.η - 1))) - E.c * E.s * 1) θ :=
    (hdf.const_mul _).sub ((hasDerivAt_id θ).const_mul _)
  have hD : HasDerivAt (fun x => E.s + E.findRate x) (E.A * ((1 - E.η) * θ ^ (1 - E.η - 1))) θ :=
    hdf.const_add _
  have hW := (hN.div hD hsf.ne').const_add E.b
  refine hW.congr_deriv ?_
  -- algebra: express everything through `θ^η`
  have hθη : 0 < θ ^ E.η := rpow_pos_of_pos hθ _
  have e1 : θ ^ (1 - E.η - 1) = 1 / θ ^ E.η := by
    rw [show 1 - E.η - 1 = -E.η by ring, rpow_neg hθ.le, one_div]
  have e2 : E.findRate θ = E.A * θ / θ ^ E.η := by
    simp only [findRate]; rw [rpow_sub hθ, rpow_one]; ring
  simp only [jc, e1, e2]
  field_simp
  ring

/-- `P(θ) > 0` below and `< 0` above the root: `jc` is strictly increasing. -/
theorem welfare_lt_of_ne {θe θ : ℝ} (he : E.IsEquilibrium 0 E.η θe) (hθ : 0 < θ) (hne : θ ≠ θe) :
    E.welfare θ < E.welfare θe := by
  have hθe := he.1
  set P : ℝ → ℝ := fun x => (1 - E.η) * (E.y - E.b) - E.jc 0 E.η x
  have hmono := E.jc_strictMonoOn le_rfl E.hη₀.le
  have hPe : P θe = 0 := by simp only [P]; rw [he.2]; ring
  have hderiv : ∀ x, 0 < x → HasDerivAt E.welfare
      (E.s * E.findRate x / (x * (E.s + E.findRate x) ^ 2) * P x) x :=
    fun x hx => E.hasDerivAt_welfare hx
  have hfac : ∀ x, 0 < x → 0 < E.s * E.findRate x / (x * (E.s + E.findRate x) ^ 2) := by
    intro x hx
    have hf : 0 < E.findRate x := mul_pos E.hA (rpow_pos_of_pos hx _)
    have := E.hs
    positivity
  have hcont : ∀ a b, 0 < a → ContinuousOn E.welfare (Icc a b) := fun a b ha x hx =>
    (hderiv x (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- on `(θ, θe)`, `P > 0`, so `W` is strictly increasing
    refine strictMonoOn_of_deriv_pos (convex_Icc θ θe) (hcont θ θe hθ) (fun x hx => ?_)
      (left_mem_Icc.2 hlt.le) (right_mem_Icc.2 hlt.le) hlt
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hθ.trans hx.1
    rw [(hderiv x hx0).deriv]
    refine mul_pos (hfac x hx0) ?_
    have := hmono (mem_Ici.2 hx0.le) (mem_Ici.2 hθe.le) hx.2
    simp only [P] at hPe ⊢; linarith
  · refine strictAntiOn_of_deriv_neg (convex_Icc θe θ) (hcont θe θ hθe) (fun x hx => ?_)
      (left_mem_Icc.2 hgt.le) (right_mem_Icc.2 hgt.le) hgt
    rw [interior_Icc] at hx
    have hx0 : 0 < x := hθe.trans hx.1
    rw [(hderiv x hx0).deriv]
    refine mul_neg_of_pos_of_neg (hfac x hx0) ?_
    have := hmono (mem_Ici.2 hθe.le) (mem_Ici.2 hx0.le) hx.1
    simp only [P] at hPe ⊢; linarith

/-- **The efficient tightness solves the job-creation condition with `r = 0`
and `β = η`**, and such a `θ` exists, is unique and is efficient. -/
theorem isEfficient_iff {θ : ℝ} : E.IsEfficient θ ↔ E.IsEquilibrium 0 E.η θ := by
  obtain ⟨θe, he, -⟩ := E.existsUnique_equilibrium le_rfl E.hη₀.le E.hη₁
  constructor
  · rintro ⟨hθ, hmax⟩
    by_contra hne
    have hne' : θ ≠ θe := fun h => hne (h ▸ he)
    have := E.welfare_lt_of_ne he hθ hne'
    have := hmax θe he.1
    linarith
  · intro h
    refine ⟨h.1, fun θ' hθ' => ?_⟩
    rcases eq_or_ne θ' θ with rfl | hne
    · exact le_rfl
    · exact (E.welfare_lt_of_ne h hθ' hne).le

/-- **The Hosios condition.** With the steady-state welfare criterion, the
(`r = 0`) DMP equilibrium with worker bargaining power `β ∈ [0, 1)` is
efficient iff `β = η`, the elasticity of the matching function with respect
to unemployment. If `β < η` there are too many vacancies; if `β > η`, too
few. This is the `r = 0` case only; the general Hosios theorem with
discounting (`r > 0`, dynamic planner) is `DMP.Discrete.hosios` in
`Macro/Labor/HosiosDiscounted.lean`. -/
theorem hosios {β θ : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (h : E.IsEquilibrium 0 β θ) :
    E.IsEfficient θ ↔ β = E.η := by
  rw [isEfficient_iff]
  constructor
  · intro he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := E.equilibrium_strictAnti_β le_rfl hβ₀ hlt h he; linarith
    · have := E.equilibrium_strictAnti_β le_rfl E.hη₀.le hgt he h; linarith
  · rintro rfl; exact h

end Economy

/-- **Non-vacuity.** A calibrated economy (`A = 1`, `η = 1/2`, `s = 1/10`,
`r = 1/100`, `c = 1`, `y = 1`, `b = 2/5`) satisfies all assumptions and has a
unique equilibrium for `β = 1/2`. -/
example : ∃! θ, (⟨1, 1 / 2, 1 / 10, 1, 1, 2 / 5, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩ : Economy).IsEquilibrium (1 / 100) (1 / 2) θ :=
  Economy.existsUnique_equilibrium _ (by norm_num) (by norm_num) (by norm_num)

end DMP
end Econ

end
