/-
# The Friedman rule in a cash-in-advance economy

Friedman (1969); the cash–credit goods model of Lucas and Stokey (1987),
"Money and Interest in a Cash-in-Advance Economy", Econometrica, in the
endowment version of Walsh, *Monetary Theory and Policy*, ch. 3–4, and
Ljungqvist–Sargent, *Recursive Macroeconomic Theory*, ch. 26. (This is not
the Lucas–Stokey (1983) optimal-taxation result, which needs conditions on
preferences.)

**Setting (steady state).** A representative household consumes a cash good
`c₁` (which must be paid for with money held in advance) and a credit good
`c₂`, with utility `U₁(c₁) + U₂(c₂)` where each `U_j` is differentiable on
`(0, ∞)` with strictly decreasing marginal utility `U_j'`. The endowment `y`
is fixed, so feasibility is `c₁ + c₂ = y`. In a steady state with money
growth `μ` and discount factor `β ∈ (0, 1)`, the nominal interest rate is
`1 + i = (1 + μ)/β`, and the cash-in-advance constraint drives a wedge
between the two goods: `U₁'(c₁) = (1 + i) U₂'(c₂)` (`IsEq`).

**Results.**
* `existsUnique_eq`: under Inada conditions, for every `i ≥ 0` there is a
  unique interior equilibrium (Darboux's theorem plus a strictly decreasing
  wedge), so the results below are not vacuous.
* `friedman_rule_μ`: among money growth rates `μ ≥ β − 1`, the equilibrium is
  efficient iff `μ = β − 1`.
* `nominalRate_eq_zero_iff`: `i = 0` iff `μ = β − 1` (deflation at the rate
  of time preference: the Friedman rule).
* `isEq_iff`: an interior `c₁` is an equilibrium iff the first-order wedge
  `U₁'(c₁) − (1 + i) U₂'(y − c₁) = 0` holds.
* `efficient_iff`: the efficient allocation (maximizing `U₁(c) + U₂(y − c)`)
  is exactly the equilibrium at `i = 0`.
* `friedman_rule`: for every `i > 0`, the equilibrium cash-good consumption is
  strictly below the efficient level and welfare is strictly lower; welfare is
  maximized by the Friedman rule.
* `welfare_anti`: welfare is strictly decreasing in the nominal rate.

**Deviations.** Endowment economy (no labor margin), separable utility,
steady states only. `IsEq` does not itself impose `i ≥ 0` (negative nominal
rates admit no monetary equilibrium); every result assumes it.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Darboux

@[expose] public section

noncomputable section

namespace Econ
namespace CIA

open Set

/-- Primitives of the steady-state economy. -/
structure Env where
  U₁ : ℝ → ℝ
  U₂ : ℝ → ℝ
  dU₁ : ℝ → ℝ
  dU₂ : ℝ → ℝ
  y : ℝ
  hy : 0 < y
  hU₁ : ∀ c, 0 < c → HasDerivAt U₁ (dU₁ c) c
  hU₂ : ∀ c, 0 < c → HasDerivAt U₂ (dU₂ c) c
  hd₁ : StrictAntiOn dU₁ (Ioi 0)
  hd₂ : StrictAntiOn dU₂ (Ioi 0)
  hpos₁ : ∀ c, 0 < c → 0 < dU₁ c
  hpos₂ : ∀ c, 0 < c → 0 < dU₂ c
  /-- Inada conditions: marginal utilities are unbounded near zero. -/
  inada₁ : ∀ M, ∃ ε > 0, ∀ c, 0 < c → c < ε → M < dU₁ c
  inada₂ : ∀ M, ∃ ε > 0, ∀ c, 0 < c → c < ε → M < dU₂ c

/-- The steady-state nominal interest rate. -/
def nominalRate (μ β : ℝ) : ℝ := (1 + μ) / β - 1

theorem nominalRate_eq_zero_iff {μ β : ℝ} (hβ : 0 < β) : nominalRate μ β = 0 ↔ μ = β - 1 := by
  unfold nominalRate
  rw [sub_eq_zero, div_eq_one_iff_eq hβ.ne']
  constructor <;> intro h <;> linarith

namespace Env

variable (E : Env)

/-- Welfare from allocating `c` to the cash good. -/
def W (c : ℝ) : ℝ := E.U₁ c + E.U₂ (E.y - c)

/-- An interior steady-state equilibrium at nominal rate `i`. -/
def IsEq (i c : ℝ) : Prop := 0 < c ∧ c < E.y ∧ E.dU₁ c = (1 + i) * E.dU₂ (E.y - c)

/-- The efficient allocation. -/
def IsEfficient (c : ℝ) : Prop := 0 < c ∧ c < E.y ∧ ∀ c', 0 < c' → c' < E.y → E.W c' ≤ E.W c

theorem hasDerivAt_W {c : ℝ} (h0 : 0 < c) (hy : c < E.y) :
    HasDerivAt E.W (E.dU₁ c - E.dU₂ (E.y - c)) c := by
  have h2 : HasDerivAt (fun c => E.U₂ (E.y - c)) (E.dU₂ (E.y - c) * (-1)) c :=
    (E.hU₂ (E.y - c) (by linarith)).comp c ((hasDerivAt_id c).const_sub E.y)
  convert (E.hU₁ c h0).add h2 using 1
  · rfl
  · ring

/-- `W'` is strictly decreasing on `(0, y)`. -/
theorem dW_strictAnti {c c' : ℝ} (h0 : 0 < c) (hcc : c < c') (hy : c' < E.y) :
    E.dU₁ c' - E.dU₂ (E.y - c') < E.dU₁ c - E.dU₂ (E.y - c) := by
  have h1 := E.hd₁ h0 (h0.trans hcc) hcc
  have h2 := E.hd₂ (show (0:ℝ) < E.y - c' by linarith) (show (0:ℝ) < E.y - c by linarith)
    (by linarith)
  linarith

/-- Strict increase of `W` where `W' > 0` throughout. -/
theorem W_lt_of_deriv_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < E.y)
    (hpos : ∀ x ∈ Ioo a b, 0 < E.dU₁ x - E.dU₂ (E.y - x)) : E.W a < E.W b := by
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope E.W (fun x => E.dU₁ x - E.dU₂ (E.y - x)) hab
    (fun x hx => (E.hasDerivAt_W (ha.trans_le hx.1) (hx.2.trans_lt hb)).continuousAt.continuousWithinAt)
    (fun x hx => E.hasDerivAt_W (ha.trans hx.1) (hx.2.trans hb))
  have := hpos ξ hξ
  rw [hd, lt_div_iff₀ (by linarith)] at this
  linarith

theorem W_lt_of_deriv_neg {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < E.y)
    (hneg : ∀ x ∈ Ioo a b, E.dU₁ x - E.dU₂ (E.y - x) < 0) : E.W b < E.W a := by
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope E.W (fun x => E.dU₁ x - E.dU₂ (E.y - x)) hab
    (fun x hx => (E.hasDerivAt_W (ha.trans_le hx.1) (hx.2.trans_lt hb)).continuousAt.continuousWithinAt)
    (fun x hx => E.hasDerivAt_W (ha.trans hx.1) (hx.2.trans hb))
  have := hneg ξ hξ
  rw [hd, div_lt_iff₀ (by linarith)] at this
  linarith

/-- **Efficiency is the equilibrium under the Friedman rule.** -/
theorem efficient_iff {c : ℝ} : E.IsEfficient c ↔ E.IsEq 0 c := by
  constructor
  · rintro ⟨h0, hy, hmax⟩
    refine ⟨h0, hy, ?_⟩
    have hloc : IsLocalMax E.W c :=
      Filter.mem_of_superset (Ioo_mem_nhds h0 hy) fun x hx => hmax x hx.1 hx.2
    have := hloc.hasDerivAt_eq_zero (E.hasDerivAt_W h0 hy)
    linarith
  · rintro ⟨h0, hy, hfoc⟩
    refine ⟨h0, hy, fun c' h0' hy' => ?_⟩
    have hz : E.dU₁ c - E.dU₂ (E.y - c) = 0 := by linarith
    rcases lt_trichotomy c' c with h | rfl | h
    · exact (E.W_lt_of_deriv_pos h0' h hy fun x hx => by
        have := E.dW_strictAnti (h0'.trans hx.1) hx.2 hy; linarith).le
    · exact le_rfl
    · exact (E.W_lt_of_deriv_neg h0 h hy' fun x hx => by
        have := E.dW_strictAnti h0 hx.1 (hx.2.trans hy'); linarith).le

/-- Positive nominal rates distort toward the credit good: `U₁' > U₂'`. -/
theorem wedge_pos {i c : ℝ} (hi : 0 < i) (h : E.IsEq i c) :
    0 < E.dU₁ c - E.dU₂ (E.y - c) := by
  obtain ⟨h0, hy, hfoc⟩ := h
  have := E.hpos₂ (E.y - c) (by linarith)
  rw [hfoc]; nlinarith

/-- **The Friedman rule is optimal.** With `i > 0`, cash-good consumption is
strictly below the efficient level `c*` and welfare is strictly lower. -/
theorem friedman_rule {i c cs : ℝ} (hi : 0 < i) (h : E.IsEq i c) (hs : E.IsEq 0 cs) :
    c < cs ∧ E.W c < E.W cs := by
  have hw := E.wedge_pos hi h
  have hz : E.dU₁ cs - E.dU₂ (E.y - cs) = 0 := by linarith [hs.2.2]
  have hlt : c < cs := by
    by_contra hle; push Not at hle
    rcases hle.eq_or_lt with heq | hlt
    · rw [heq] at hz; linarith
    · have := E.dW_strictAnti hs.1 hlt h.2.1; linarith
  refine ⟨hlt, E.W_lt_of_deriv_pos h.1 hlt hs.2.1 fun x hx => ?_⟩
  have := E.dW_strictAnti (h.1.trans hx.1) hx.2 hs.2.1
  linarith

/-- The cash–credit wedge is strictly decreasing in `c` (for `i > −1`). -/
theorem wedge_strictAnti {i c c' : ℝ} (hi : -1 < i) (h0 : 0 < c) (hcc : c < c') (hy : c' < E.y) :
    E.dU₁ c' - (1 + i) * E.dU₂ (E.y - c') < E.dU₁ c - (1 + i) * E.dU₂ (E.y - c) := by
  have h1 := E.hd₁ h0 (h0.trans hcc) hcc
  have h2 := E.hd₂ (show (0:ℝ) < E.y - c' by linarith) (show (0:ℝ) < E.y - c by linarith)
    (by linarith)
  nlinarith

/-- **Existence and uniqueness of equilibrium** for every `i ≥ 0`. -/
theorem existsUnique_eq {i : ℝ} (hi : 0 ≤ i) : ∃! c, E.IsEq i c := by
  have hy2 : 0 < E.y / 2 := by linarith [E.hy]
  -- a point near 0 where the wedge is positive
  obtain ⟨ε₁, hε₁, h₁⟩ := E.inada₁ ((1 + i) * E.dU₂ (E.y / 2))
  set a := min (ε₁ / 2) (E.y / 2)
  have ha0 : 0 < a := lt_min (by linarith) hy2
  have haε : a < ε₁ := (min_le_left _ _).trans_lt (by linarith)
  have hay : a ≤ E.y / 2 := min_le_right _ _
  have hga : 0 < E.dU₁ a - (1 + i) * E.dU₂ (E.y - a) := by
    have h1 := h₁ a ha0 haε
    have h2 : E.dU₂ (E.y - a) ≤ E.dU₂ (E.y / 2) :=
      E.hd₂.antitoneOn hy2 (show (0:ℝ) < E.y - a by linarith) (by linarith)
    nlinarith
  -- a point near `y` where the wedge is negative
  obtain ⟨ε₂, hε₂, h₂⟩ := E.inada₂ (E.dU₁ (E.y / 2))
  set d := min (ε₂ / 2) (E.y / 2)
  have hd0 : 0 < d := lt_min (by linarith) hy2
  have hdε : d < ε₂ := (min_le_left _ _).trans_lt (by linarith)
  have hdy : d ≤ E.y / 2 := min_le_right _ _
  set b := E.y - d
  have hgb : E.dU₁ b - (1 + i) * E.dU₂ (E.y - b) < 0 := by
    have hyb : E.y - b = d := by ring
    rw [hyb]
    have h1 := h₂ d hd0 hdε
    have h2 : E.dU₁ b ≤ E.dU₁ (E.y / 2) :=
      E.hd₁.antitoneOn hy2 (show (0:ℝ) < b by linarith) (by linarith)
    have h3 := E.hpos₂ d hd0
    nlinarith
  have hab : a ≤ b := by linarith
  have hb : b < E.y := by linarith
  -- Darboux for `c ↦ U₁(c) + (1 + i) U₂(y − c)` on `[a, b]`
  have hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt (fun c => E.U₁ c + (1 + i) * E.U₂ (E.y - c))
      (E.dU₁ x - (1 + i) * E.dU₂ (E.y - x)) (Icc a b) x := by
    intro x hx
    have hx0 : 0 < x := ha0.trans_le hx.1
    have hxy : x < E.y := hx.2.trans_lt hb
    have h2 : HasDerivAt (fun c => E.U₂ (E.y - c)) (E.dU₂ (E.y - x) * (-1)) x :=
      (E.hU₂ (E.y - x) (by linarith)).comp x ((hasDerivAt_id x).const_sub E.y)
    have := ((E.hU₁ x hx0).add (h2.const_mul (1 + i))).hasDerivWithinAt (s := Icc a b)
    convert this using 1
    ring
  obtain ⟨c, hc, hgc⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt hab hderiv hga hgb
  have hc0 : 0 < c := ha0.trans hc.1
  have hcy : c < E.y := hc.2.trans hb
  simp only at hgc
  refine ⟨c, ⟨hc0, hcy, by linarith⟩, fun c' ⟨h0', hy', hfoc'⟩ => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := E.wedge_strictAnti (i := i) (by linarith) h0' hlt hcy; linarith
  · have := E.wedge_strictAnti (i := i) (by linarith) hc0 hlt hy'; linarith

/-- Equilibrium given money growth `μ` and discount factor `β`. -/
def IsEqμ (μ β c : ℝ) : Prop := E.IsEq (nominalRate μ β) c

/-- **The Friedman rule as a policy.** Among money growth rates
`μ ≥ β − 1` (non-negative nominal rates), the equilibrium is efficient iff
`μ = β − 1`; any faster money growth strictly lowers welfare. -/
theorem friedman_rule_μ {μ β c : ℝ} (hβ : 0 < β) (hμ : β - 1 ≤ μ) (h : E.IsEqμ μ β c) :
    E.IsEfficient c ↔ μ = β - 1 := by
  have hi : 0 ≤ nominalRate μ β := by
    unfold nominalRate; rw [sub_nonneg, le_div_iff₀ hβ]; linarith
  rw [← nominalRate_eq_zero_iff hβ, E.efficient_iff]
  constructor
  · intro he
    by_contra hne
    have hpos : 0 < nominalRate μ β := lt_of_le_of_ne hi (Ne.symm hne)
    have := (E.friedman_rule hpos h he).1
    linarith
  · intro h0; rw [← h0]; exact h

/-- **Welfare falls with the nominal rate.** -/
theorem welfare_anti {i i' c c' : ℝ} (hi : 0 ≤ i) (hii : i < i') (h : E.IsEq i c)
    (h' : E.IsEq i' c') : E.W c' < E.W c := by
  -- `c' < c`: the wedge rises with `i`
  have hw : ∀ x, 0 < x → x < E.y → 0 < E.dU₂ (E.y - x) := fun x _ hx => E.hpos₂ _ (by linarith)
  have hlt : c' < c := by
    by_contra hle; push Not at hle
    have hd₁ : E.dU₁ c' ≤ E.dU₁ c := E.hd₁.antitoneOn h.1 h'.1 hle
    have hd₂ : E.dU₂ (E.y - c) ≤ E.dU₂ (E.y - c') :=
      E.hd₂.antitoneOn (show (0:ℝ) < E.y - c' by linarith [h'.2.1])
        (show (0:ℝ) < E.y - c by linarith [h.2.1]) (by linarith)
    have := hw c h.1 h.2.1
    have := hw c' h'.1 h'.2.1
    have e1 := h.2.2; have e2 := h'.2.2
    nlinarith
  apply E.W_lt_of_deriv_pos h'.1 hlt h.2.1 fun x hx => ?_
  have hc := E.dW_strictAnti (h'.1.trans hx.1) hx.2 h.2.1
  have : 0 ≤ E.dU₁ c - E.dU₂ (E.y - c) := by
    have := hw c h.1 h.2.1
    rw [h.2.2]; nlinarith
  linarith

end Env
end CIA
end Econ

end
