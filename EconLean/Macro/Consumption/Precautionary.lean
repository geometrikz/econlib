/-
# Precautionary saving and prudence

Leland (1968), Sandmo (1970), Kimball (1990); Ljungqvist–Sargent ch. 17;
Gollier, *The Economics of Risk and Time*, ch. 16.

**The problem.** A consumer with wealth `w` today chooses saving `s`, consumes
`w − s` today and `R s + y` tomorrow, where income `y` takes value `y_i` with
probability `π_i`. Lifetime utility is `V(s) = u(w − s) + β Σ_i π_i u(R s + y_i)`.
Consumption must be positive in every state (`Feasible`). The **certainty
equivalent problem** (`certain`) replaces `y` by its mean `ȳ = Σ π_i y_i`.

**Prudence** (Kimball) is convexity of marginal utility `u'` (equivalently
`u''' ≥ 0` when `u` is three times differentiable). CRRA and CARA utilities
are prudent; quadratic utility has `u'''= 0`.

**Results.**
* `foc`: an optimal saving level satisfies the Euler equation
  `u'(w − s) = β R Σ π_i u'(R s + y_i)`.
* `isOptimal_of_foc`: conversely, a feasible `s` satisfying the Euler equation is
  optimal (by concavity of `u`, from `u'` decreasing).
* `precautionary`: with prudence, optimal saving under income risk is at least
  optimal saving under certainty with the same mean income.
* `precautionary_strict`: with strictly convex `u'`, full-support
  probabilities and non-degenerate income, it is strictly higher.

**Deviations.** Two periods; finitely many income states; `u` defined and
differentiable on `(0, ∞)` with `u'` strictly decreasing. Existence of both
optima is assumed in `precautionary`; only risk versus its certain mean is
compared (not general mean-preserving spreads or Kimball's comparative
prudence); the example shows the certainty problem
with log utility has one.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

noncomputable section

namespace Econ
namespace Precautionary

open Set Finset

/-- The two-period saving problem with income risk. -/
structure Problem (ι : Type*) [Fintype ι] where
  /-- Utility and marginal utility. -/
  u : ℝ → ℝ
  u' : ℝ → ℝ
  /-- Discount factor, gross return, initial wealth. -/
  β : ℝ
  R : ℝ
  w : ℝ
  /-- Income distribution. -/
  π : ι → ℝ
  y : ι → ℝ
  hβ : 0 < β
  hR : 0 < R
  hπ : ∀ i, 0 ≤ π i
  sum_π : ∑ i, π i = 1
  deriv : ∀ c, 0 < c → HasDerivAt u (u' c) c
  anti : StrictAntiOn u' (Ioi 0)

namespace Problem

variable {ι : Type*} [Fintype ι] (P : Problem ι)

/-- Lifetime utility of saving `s`. -/
def V (s : ℝ) : ℝ := P.u (P.w - s) + P.β * ∑ i, P.π i * P.u (P.R * s + P.y i)

/-- Saving `s` is feasible if consumption is positive today and in every state. -/
def Feasible (s : ℝ) : Prop := 0 < P.w - s ∧ ∀ i, 0 < P.R * s + P.y i

/-- `s` is optimal. -/
def IsOptimal (s : ℝ) : Prop := P.Feasible s ∧ ∀ s', P.Feasible s' → P.V s' ≤ P.V s

/-- Mean income. -/
def ybar : ℝ := ∑ i, P.π i * P.y i

/-- The certainty-equivalent problem: income `ȳ` for sure. -/
def certain : Problem Unit where
  u := P.u
  u' := P.u'
  β := P.β
  R := P.R
  w := P.w
  π _ := 1
  y _ := P.ybar
  hβ := P.hβ
  hR := P.hR
  hπ _ := zero_le_one
  sum_π := by simp
  deriv := P.deriv
  anti := P.anti

/-- Marginal value of saving: `β R Σ π_i u'(R s + y_i) − u'(w − s)`. -/
def marg (s : ℝ) : ℝ := P.β * P.R * ∑ i, P.π i * P.u' (P.R * s + P.y i) - P.u' (P.w - s)

theorem hasDerivAt_V {s : ℝ} (hs : P.Feasible s) : HasDerivAt P.V (P.marg s) s := by
  have h0 : HasDerivAt (fun s => P.u (P.w - s)) (P.u' (P.w - s) * (-1)) s := by
    exact (P.deriv _ hs.1).comp s ((hasDerivAt_id s).const_sub P.w)
  have h1 : HasDerivAt (fun s => ∑ i, P.π i * P.u (P.R * s + P.y i))
      (∑ i, P.π i * (P.u' (P.R * s + P.y i) * P.R)) s := by
    apply HasDerivAt.fun_sum
    intro i _
    have := (P.deriv _ (hs.2 i)).comp s (((hasDerivAt_id s).const_mul P.R).add_const (P.y i))
    simpa using this.const_mul (P.π i)
  have := h0.add (h1.const_mul P.β)
  convert this using 1
  · funext; simp [V]
  · simp only [marg, mul_sum]
    rw [sub_eq_add_neg, mul_neg_one, add_comm]
    congr 1
    exact sum_congr rfl fun i _ => by ring

theorem isOpen_feasible : IsOpen {s | P.Feasible s} := by
  have : {s | P.Feasible s} = {s | 0 < P.w - s} ∩ ⋂ i, {s | 0 < P.R * s + P.y i} := by
    ext s; simp [Feasible]
  rw [this]
  refine (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_iInter_of_finite fun i => ?_)
  exact isOpen_lt continuous_const (by fun_prop)

/-- **The Euler equation is necessary.** -/
theorem foc {s : ℝ} (h : P.IsOptimal s) :
    P.u' (P.w - s) = P.β * P.R * ∑ i, P.π i * P.u' (P.R * s + P.y i) := by
  have hmax : IsLocalMax P.V s :=
    Filter.mem_of_superset (P.isOpen_feasible.mem_nhds h.1) fun s' hs' => h.2 s' hs'
  have := hmax.hasDerivAt_eq_zero (P.hasDerivAt_V h.1)
  unfold marg at this; linarith

/-- Tangent-line bound for `u` from `u'` decreasing (mean value theorem). -/
theorem u_le_tangent {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    P.u x ≤ P.u c + P.u' c * (x - c) := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope P.u P.u' hlt
      (fun z hz => (P.deriv z (hx.trans_le hz.1)).continuousAt.continuousWithinAt)
      (fun z hz => P.deriv z (hx.trans hz.1))
    have hξc : P.u' c < P.u' ξ := P.anti (hx.trans hξ.1) hc hξ.2
    rw [eq_div_iff (by linarith)] at hd
    nlinarith
  · rw [heq]; simp
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope P.u P.u' hgt
      (fun z hz => (P.deriv z (hc.trans_le hz.1)).continuousAt.continuousWithinAt)
      (fun z hz => P.deriv z (hc.trans hz.1))
    have hξc : P.u' ξ < P.u' c := P.anti hc (hc.trans hξ.1) hξ.1
    rw [eq_div_iff (by linarith)] at hd
    nlinarith

/-- **The Euler equation is sufficient.** -/
theorem isOptimal_of_foc {s : ℝ} (hs : P.Feasible s)
    (h : P.u' (P.w - s) = P.β * P.R * ∑ i, P.π i * P.u' (P.R * s + P.y i)) : P.IsOptimal s := by
  refine ⟨hs, fun s' hs' => ?_⟩
  have h0 := P.u_le_tangent hs.1 hs'.1
  have h1 : ∑ i, P.π i * P.u (P.R * s' + P.y i) ≤
      ∑ i, P.π i * (P.u (P.R * s + P.y i) + P.u' (P.R * s + P.y i) * (P.R * s' - P.R * s)) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by
      have := P.u_le_tangent (hs.2 i) (hs'.2 i)
      linarith [show P.R * s' + P.y i - (P.R * s + P.y i) = P.R * s' - P.R * s by ring])
      (P.hπ i)
  have e : ∑ i, P.π i * (P.u (P.R * s + P.y i) + P.u' (P.R * s + P.y i) * (P.R * s' - P.R * s)) =
      ∑ i, P.π i * P.u (P.R * s + P.y i) +
        (∑ i, P.π i * P.u' (P.R * s + P.y i)) * (P.R * (s' - s)) := by
    rw [sum_mul, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [e] at h1
  have hb := mul_le_mul_of_nonneg_left h1 P.hβ.le
  unfold V
  have : P.β * ((∑ i, P.π i * P.u' (P.R * s + P.y i)) * (P.R * (s' - s))) =
      P.u' (P.w - s) * (s' - s) := by rw [h]; ring
  nlinarith

/-- The marginal value of saving is strictly decreasing on the feasible set. -/
theorem marg_strictAnti {s t : ℝ} (hs : P.Feasible s) (ht : P.Feasible t) (hst : s < t) :
    P.marg t < P.marg s := by
  have h1 : P.u' (P.w - s) < P.u' (P.w - t) := P.anti ht.1 hs.1 (by linarith)
  have h2 : ∑ i, P.π i * P.u' (P.R * t + P.y i) ≤ ∑ i, P.π i * P.u' (P.R * s + P.y i) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (P.anti.antitoneOn (hs.2 i) (ht.2 i) (by nlinarith [P.hR])) (P.hπ i)
  have := mul_le_mul_of_nonneg_left h2 (mul_pos P.hβ P.hR).le
  unfold marg; linarith

/-- Jensen: under prudence, expected marginal utility exceeds marginal utility
at expected consumption. -/
theorem marg_certain_le (hconv : ConvexOn ℝ (Ioi 0) P.u') {s : ℝ} (hs : P.Feasible s) :
    P.certain.marg s ≤ P.marg s := by
  have hj := hconv.map_sum_le (t := univ) (w := P.π) (p := fun i => P.R * s + P.y i)
    (fun i _ => P.hπ i) P.sum_π (fun i _ => hs.2 i)
  simp only [smul_eq_mul] at hj
  have e : ∑ i, P.π i * (P.R * s + P.y i) = P.R * s + P.ybar := by
    simp only [ybar, mul_add, sum_add_distrib, ← sum_mul, P.sum_π, one_mul]
  rw [e] at hj
  have := mul_le_mul_of_nonneg_left hj (mul_pos P.hβ P.hR).le
  simp only [marg, certain, one_mul, Fintype.sum_unique]
  linarith

/-- **Precautionary saving.** If marginal utility is convex (prudence), optimal
saving under income risk is at least optimal saving when income is replaced by
its mean. -/
theorem precautionary (hconv : ConvexOn ℝ (Ioi 0) P.u') {sc sr : ℝ}
    (hc : P.certain.IsOptimal sc) (hr : P.IsOptimal sr) : sc ≤ sr := by
  by_cases hfeas : P.Feasible sc
  · by_contra hlt
    push Not at hlt
    have h1 := P.marg_strictAnti hr.1 hfeas hlt
    have h2 := P.marg_certain_le hconv hfeas
    have h3 : P.certain.marg sc = 0 := by have := P.certain.foc hc; unfold marg; linarith
    have h4 : P.marg sr = 0 := by have := P.foc hr; unfold marg; linarith
    linarith
  · -- some state has non-positive consumption at `sc`, but positive at `sr`
    have hw : 0 < P.w - sc := hc.1.1
    obtain ⟨i, hi⟩ : ∃ i, P.R * sc + P.y i ≤ 0 := by
      by_contra h; push Not at h; exact hfeas ⟨hw, h⟩
    have := hr.1.2 i
    have hR := P.hR
    nlinarith

/-- **Strict precautionary saving** with strictly convex marginal utility,
full-support probabilities and non-degenerate income. -/
theorem precautionary_strict (hconv : StrictConvexOn ℝ (Ioi 0) P.u') (hpos : ∀ i, 0 < P.π i)
    (hy : ∃ i j, P.y i ≠ P.y j) {sc sr : ℝ} (hc : P.certain.IsOptimal sc)
    (hr : P.IsOptimal sr) : sc < sr := by
  by_cases hfeas : P.Feasible sc
  · by_contra hle
    push Not at hle
    obtain ⟨i, j, hij⟩ := hy
    have hj := hconv.map_sum_lt (t := univ) (w := P.π) (p := fun i => P.R * sc + P.y i)
      (fun i _ => hpos i) P.sum_π (fun i _ => hfeas.2 i)
      ⟨i, mem_univ _, j, mem_univ _, by simpa using hij⟩
    simp only [smul_eq_mul] at hj
    have e : ∑ i, P.π i * (P.R * sc + P.y i) = P.R * sc + P.ybar := by
      simp only [ybar, mul_add, sum_add_distrib, ← sum_mul, P.sum_π, one_mul]
    rw [e] at hj
    have hlt : P.certain.marg sc < P.marg sc := by
      have := mul_lt_mul_of_pos_left hj (mul_pos P.hβ P.hR)
      simp only [marg, certain, one_mul, Fintype.sum_unique]
      linarith
    have h3 : P.certain.marg sc = 0 := by have := P.certain.foc hc; unfold marg; linarith
    have h4 : P.marg sr = 0 := by have := P.foc hr; unfold marg; linarith
    rcases hle.lt_or_eq with h | h
    · have h1 := P.marg_strictAnti hr.1 hfeas h
      linarith
    · subst h; linarith
  · have hw : 0 < P.w - sc := hc.1.1
    obtain ⟨i, hi⟩ : ∃ i, P.R * sc + P.y i ≤ 0 := by
      by_contra h; push Not at h; exact hfeas ⟨hw, h⟩
    have := hr.1.2 i
    have hR := P.hR
    nlinarith

end Problem

/-- Example economy: log utility (prudent, since `u' = 1/c` is strictly convex),
`β = R = 1`, wealth `2`, income `1/2` or `3/2` with equal probability. -/
def example₁ : Problem Bool where
  u := Real.log
  u' c := c⁻¹
  β := 1
  R := 1
  w := 2
  π _ := 1 / 2
  y b := if b then 3 / 2 else 1 / 2
  hβ := one_pos
  hR := one_pos
  hπ _ := by norm_num
  sum_π := by norm_num
  deriv c hc := Real.hasDerivAt_log hc.ne'
  anti _ ha _ _ hab := inv_strictAnti₀ ha hab

/-- **Non-vacuity.** In `example₁` the certainty problem (income `1`) has
optimal saving `1/2`, the risky problem has optimal saving `(√11 − 1)/4 ≈ 0.58`,
and the hypotheses of `precautionary_strict` hold. -/
example : example₁.certain.IsOptimal (1 / 2) ∧ example₁.IsOptimal ((√11 - 1) / 4) ∧
    StrictConvexOn ℝ (Ioi 0) example₁.u' ∧ (∀ i, 0 < example₁.π i) ∧
    ∃ i j, example₁.y i ≠ example₁.y j := by
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h3 : 3 < √11 := by nlinarith [Real.sqrt_nonneg 11]
  have h4 : √11 < 4 := by nlinarith [Real.sqrt_nonneg 11]
  refine ⟨?_, ?_, ?_, fun _ => by norm_num [example₁], true, false, by norm_num [example₁]⟩
  · apply Problem.isOptimal_of_foc
    · refine ⟨by norm_num [Problem.certain, example₁], fun _ => ?_⟩
      norm_num [Problem.certain, Problem.ybar, example₁]
    · norm_num [Problem.certain, Problem.ybar, example₁]
  · apply Problem.isOptimal_of_foc
    · refine ⟨by norm_num [example₁]; linarith, fun b => ?_⟩
      cases b <;> norm_num [example₁] <;> linarith
    · norm_num [example₁]
      rw [show (2:ℝ) - (√11 - 1) / 4 = (9 - √11) / 4 by ring,
        show (√11 - 1) / 4 + 3 / 2 = (√11 + 5) / 4 by ring,
        show (√11 - 1) / 4 + 1 / 2 = (√11 + 1) / 4 by ring, inv_div, inv_div, inv_div]
      have a1 : (9 - √11 : ℝ) ≠ 0 := by linarith
      have a2 : (√11 + 5 : ℝ) ≠ 0 := by linarith
      have a3 : (√11 + 1 : ℝ) ≠ 0 := by linarith
      field_simp
      linear_combination (4 : ℝ) * h11
  · have := strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)
    simpa [example₁] using this

end Precautionary
end Econ

end
