/-
# The inverse Euler equation and the savings wedge

Rogerson (1985), "Repeated Moral Hazard", Econometrica;
Golosov, Kocherlakota and Tsyvinski (2003), "Optimal Indirect and Capital
Taxation", REStud; Kocherlakota, *The New Dynamic Public Finance* (2010),
ch. 2.

**Setting.** In a constrained-efficient (Mirrleesian) allocation, an agent
consumes `c₀` today and `c_s` tomorrow in state `s` (probability `π_s`),
with utility `u` and discount factor `β`; the planner can save at gross
return `R`. Work in utility units: `h = u⁻¹` is the resource cost of
delivering utility, with `h'(v) = 1/u'(h(v))`. Lowering today's utility by
`Δ` and raising utility in **every** state tomorrow by `Δ/β` leaves lifetime
utility and every incentive constraint unchanged (all continuation
utilities shift equally). Its resource cost is
`Φ(Δ) = h(v₀ − Δ) + (1/R) Σ_s π_s h(v_s + Δ/β)` (`perturbCost`).

**Results.**
* `inverse_euler`: if the allocation is optimal (`Δ = 0` locally minimizes
  `Φ`), then `h'(v₀) = (1/(βR)) Σ π_s h'(v_s)`, i.e. the **inverse Euler
  equation** `1/u'(c₀) = (1/(βR)) E[1/u'(c₁)]`.
* `one_le_mean_mul_mean_inv`, `one_lt_mean_mul_mean_inv`: for positive `x`,
  `(Σ π x)(Σ π/x) ≥ 1`, strictly if `x` is not constant on the support
  (harmonic mean ≤ arithmetic mean).
* `savings_wedge`: under the inverse Euler equation,
  `u'(c₀) ≤ βR E[u'(c₁)]`, strictly when future consumption is risky: at the
  optimum the agent would like to save more than the planner allows, so
  constrained efficiency requires a **positive wedge on savings** (an
  implicit capital tax).

* `utility_neutral`, `incentive_neutral`: with `Σ π = 1` the perturbation
  leaves expected lifetime utility unchanged, and it leaves every utility
  difference across states (hence every incentive constraint) unchanged.
* `inverse_euler_wedge`: composing the two, an optimum has a positive savings
  wedge in terms of `u' = 1/h'`.

**Deviations.** Two periods suffice for the perturbation argument. The
incentive constraints themselves are not modelled; `incentive_neutral` shows
that any constraint depending only on utility differences is preserved.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

noncomputable section

namespace Econ
namespace InverseEuler

open Finset

variable {ι : Type*} (s : Finset ι)

/-- Resource cost of the utility perturbation `Δ`. -/
def perturbCost (h : ℝ → ℝ) (β R v₀ : ℝ) (π v : ι → ℝ) (Δ : ℝ) : ℝ :=
  h (v₀ - Δ) + (1 / R) * ∑ i ∈ s, π i * h (v i + Δ / β)

/-- **The perturbation keeps promised utility.** With probabilities summing to
one, expected lifetime utility `v₀ − Δ + β Σ π (v_i + Δ/β)` does not depend
on `Δ`. -/
theorem utility_neutral {β v₀ : ℝ} {π v : ι → ℝ} (hβ : β ≠ 0) (h1 : ∑ i ∈ s, π i = 1) (Δ : ℝ) :
    (v₀ - Δ) + β * ∑ i ∈ s, π i * (v i + Δ / β) = v₀ + β * ∑ i ∈ s, π i * v i := by
  have : ∑ i ∈ s, π i * (v i + Δ / β) = ∑ i ∈ s, π i * v i + Δ / β := by
    rw [show ∑ i ∈ s, π i * (v i + Δ / β) = ∑ i ∈ s, π i * v i + (∑ i ∈ s, π i) * (Δ / β) by
      rw [sum_mul, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring, h1, one_mul]
  rw [this]
  field_simp
  ring

/-- **The perturbation keeps every incentive constraint.** Utility
differences across tomorrow's states are unchanged by the uniform shift. -/
theorem incentive_neutral (β Δ : ℝ) (v : ι → ℝ) (i j : ι) :
    (v i + Δ / β) - (v j + Δ / β) = v i - v j := by ring

/-- **The inverse Euler equation.** -/
theorem inverse_euler {h h' : ℝ → ℝ} {β R v₀ : ℝ} {π v : ι → ℝ} (hβ : β ≠ 0) (hR : R ≠ 0)
    (hd₀ : HasDerivAt h (h' v₀) v₀) (hd : ∀ i ∈ s, HasDerivAt h (h' (v i)) (v i))
    (hmin : IsLocalMin (perturbCost s h β R v₀ π v) 0) :
    h' v₀ = 1 / (β * R) * ∑ i ∈ s, π i * h' (v i) := by
  have hD : HasDerivAt (perturbCost s h β R v₀ π v)
      (h' v₀ * (-1) + 1 / R * ∑ i ∈ s, π i * (h' (v i) * (1 / β))) 0 := by
    have h1 : HasDerivAt (fun Δ => h (v₀ - Δ)) (h' v₀ * (-1)) 0 := by
      have := (hasDerivAt_id (0:ℝ)).const_sub v₀
      simp only [id] at this ⊢
      exact (show HasDerivAt h (h' v₀) (v₀ - 0) by simpa using hd₀).comp 0 this
    have h2 : HasDerivAt (fun Δ => ∑ i ∈ s, π i * h (v i + Δ / β))
        (∑ i ∈ s, π i * (h' (v i) * (1 / β))) 0 := by
      apply HasDerivAt.fun_sum
      intro i hi
      have hin : HasDerivAt (fun Δ : ℝ => v i + Δ / β) (1 / β) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).div_const β).const_add (v i)
      have := (show HasDerivAt h (h' (v i)) (v i + 0 / β) by simpa using hd i hi).comp 0 hin
      exact this.const_mul (π i)
    exact h1.add (h2.const_mul (1 / R))
  have h0 := hmin.hasDerivAt_eq_zero hD
  have : ∑ i ∈ s, π i * (h' (v i) * (1 / β)) = (1 / β) * ∑ i ∈ s, π i * h' (v i) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [this] at h0
  field_simp at h0 ⊢
  linarith

/-- `(Σ π x)(Σ π/x) − (Σ π)² = ½ ΣΣ π_i π_j (x_i − x_j)²/(x_i x_j)`. -/
theorem mean_mul_mean_inv_sub (π x : ι → ℝ) (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, π i * x i) * (∑ j ∈ s, π j / x j) - (∑ i ∈ s, π i) ^ 2 =
      (1 / 2) * ∑ i ∈ s, ∑ j ∈ s, π i * π j * (x i - x j) ^ 2 / (x i * x j) := by
  have hsym : ∑ i ∈ s, ∑ j ∈ s, π i * π j * (x i / x j) =
      ∑ i ∈ s, ∑ j ∈ s, π i * π j * (x j / x i) := by
    rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have e1 : (∑ i ∈ s, π i * x i) * (∑ j ∈ s, π j / x j) =
      ∑ i ∈ s, ∑ j ∈ s, π i * π j * (x i / x j) := by
    rw [sum_mul]; exact sum_congr rfl fun i _ => by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  have e2 : (∑ i ∈ s, π i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, π i * π j := by
    rw [sq, sum_mul]; exact sum_congr rfl fun i _ => by rw [mul_sum]
  have e3 : ∀ i ∈ s, ∀ j ∈ s, π i * π j * (x i - x j) ^ 2 / (x i * x j) =
      π i * π j * (x i / x j) + π i * π j * (x j / x i) - 2 * (π i * π j) := by
    intro i hi j hj
    have := hx i hi; have := hx j hj
    field_simp; ring
  rw [e1, e2]
  rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => e3 i hi j hj]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [← hsym]
  ring

/-- **Harmonic mean ≤ arithmetic mean.** -/
theorem one_le_mean_mul_mean_inv (π x : ι → ℝ) (hπ : ∀ i ∈ s, 0 ≤ π i) (h1 : ∑ i ∈ s, π i = 1)
    (hx : ∀ i ∈ s, 0 < x i) : 1 ≤ (∑ i ∈ s, π i * x i) * (∑ j ∈ s, π j / x j) := by
  have := mean_mul_mean_inv_sub s π x hx
  rw [h1, one_pow] at this
  have hnn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, π i * π j * (x i - x j) ^ 2 / (x i * x j) :=
    sum_nonneg fun i hi => sum_nonneg fun j hj =>
      div_nonneg (mul_nonneg (mul_nonneg (hπ i hi) (hπ j hj)) (sq_nonneg _))
        (mul_pos (hx i hi) (hx j hj)).le
  linarith

/-- Strict version when `x` takes two different values on the support. -/
theorem one_lt_mean_mul_mean_inv (π x : ι → ℝ) (hπ : ∀ i ∈ s, 0 ≤ π i)
    (h1 : ∑ i ∈ s, π i = 1) (hx : ∀ i ∈ s, 0 < x i) {k l : ι} (hk : k ∈ s) (hl : l ∈ s)
    (hπk : 0 < π k) (hπl : 0 < π l) (hkl : x k ≠ x l) :
    1 < (∑ i ∈ s, π i * x i) * (∑ j ∈ s, π j / x j) := by
  have := mean_mul_mean_inv_sub s π x hx
  rw [h1, one_pow] at this
  have hterm : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ π i * π j * (x i - x j) ^ 2 / (x i * x j) :=
    fun i hi j hj => div_nonneg (mul_nonneg (mul_nonneg (hπ i hi) (hπ j hj)) (sq_nonneg _))
        (mul_pos (hx i hi) (hx j hj)).le
  have hpos : 0 < ∑ i ∈ s, ∑ j ∈ s, π i * π j * (x i - x j) ^ 2 / (x i * x j) := by
    apply lt_of_lt_of_le _ (single_le_sum (f := fun i => ∑ j ∈ s, π i * π j * (x i - x j) ^ 2 /
      (x i * x j)) (fun i hi => sum_nonneg fun j hj => hterm i hi j hj) hk)
    apply lt_of_lt_of_le _ (single_le_sum (fun j hj => hterm k hk j hj) hl)
    have : 0 < (x k - x l) ^ 2 := by have := sub_ne_zero.2 hkl; positivity
    exact div_pos (mul_pos (mul_pos hπk hπl) this) (mul_pos (hx k hk) (hx l hl))
  linarith

/-- **The savings wedge.** If marginal utilities `μ₀ = u'(c₀)` and
`μ_i = u'(c_i)` satisfy the inverse Euler equation
`1/μ₀ = (1/(βR)) Σ π_i/μ_i`, then `μ₀ ≤ βR Σ π_i μ_i`, strictly when `μ` is
not constant on the support. -/
theorem savings_wedge (π μ : ι → ℝ) {μ₀ β R : ℝ} (hπ : ∀ i ∈ s, 0 ≤ π i)
    (h1 : ∑ i ∈ s, π i = 1) (hμ : ∀ i ∈ s, 0 < μ i) (hμ₀ : 0 < μ₀) (hβR : 0 < β * R)
    (hIE : 1 / μ₀ = 1 / (β * R) * ∑ i ∈ s, π i / μ i) :
    μ₀ ≤ β * R * ∑ i ∈ s, π i * μ i ∧
      (∀ k ∈ s, ∀ l ∈ s, 0 < π k → 0 < π l → μ k ≠ μ l → μ₀ < β * R * ∑ i ∈ s, π i * μ i) := by
  have hH : 0 < ∑ i ∈ s, π i / μ i := by
    have : 0 < 1 / (β * R) * ∑ i ∈ s, π i / μ i := by rw [← hIE]; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have hμ₀eq : μ₀ = β * R / ∑ i ∈ s, π i / μ i := by
    rw [eq_div_iff hH.ne']
    field_simp at hIE
    rw [eq_div_iff hβR.ne'] at hIE
    linarith
  have key : ∀ c, 1 ≤ c → c = (∑ i ∈ s, π i * μ i) * (∑ j ∈ s, π j / μ j) →
      μ₀ ≤ β * R * ∑ i ∈ s, π i * μ i := by
    intro c hc hceq
    rw [hμ₀eq, div_le_iff₀ hH]
    nlinarith
  refine ⟨key _ (one_le_mean_mul_mean_inv s π μ hπ h1 hμ) rfl, fun k hk l hl hπk hπl hkl => ?_⟩
  have hlt := one_lt_mean_mul_mean_inv s π μ hπ h1 hμ hk hl hπk hπl hkl
  rw [hμ₀eq, div_lt_iff₀ hH]
  nlinarith

/-- **Inverse Euler implies a savings wedge.** At an optimum of the
perturbation, with `u'(c) = 1/h'(v)` positive, probabilities summing to one
and `βR > 0`: `u'(c₀) ≤ βR E[u'(c₁)]`, strictly when two positive-probability
states have different marginal utility. -/
theorem inverse_euler_wedge {h h' : ℝ → ℝ} {β R v₀ : ℝ} {π v : ι → ℝ}
    (hπ : ∀ i ∈ s, 0 ≤ π i) (h1 : ∑ i ∈ s, π i = 1) (hβR : 0 < β * R)
    (hh'₀ : 0 < h' v₀) (hh' : ∀ i ∈ s, 0 < h' (v i))
    (hd₀ : HasDerivAt h (h' v₀) v₀) (hd : ∀ i ∈ s, HasDerivAt h (h' (v i)) (v i))
    (hmin : IsLocalMin (perturbCost s h β R v₀ π v) 0) :
    1 / h' v₀ ≤ β * R * ∑ i ∈ s, π i * (1 / h' (v i)) ∧
      (∀ k ∈ s, ∀ l ∈ s, 0 < π k → 0 < π l → h' (v k) ≠ h' (v l) →
        1 / h' v₀ < β * R * ∑ i ∈ s, π i * (1 / h' (v i))) := by
  have hβ : β ≠ 0 := by rintro rfl; simp at hβR
  have hR : R ≠ 0 := by rintro rfl; simp at hβR
  have hIE := inverse_euler s hβ hR hd₀ hd hmin
  have hIE' : 1 / (1 / h' v₀) = 1 / (β * R) * ∑ i ∈ s, π i / (1 / h' (v i)) := by
    rw [one_div_one_div, hIE]
    congr 1
    exact sum_congr rfl fun i _ => by rw [div_div_eq_mul_div, div_one]
  have hw := savings_wedge s π (fun i => 1 / h' (v i)) hπ h1
    (fun i hi => one_div_pos.2 (hh' i hi)) (one_div_pos.2 hh'₀) hβR hIE'
  refine ⟨hw.1, fun k hk l hl hπk hπl hkl => hw.2 k hk l hl hπk hπl ?_⟩
  intro h; apply hkl
  simpa using h

end InverseEuler
end Econ

end
