/-
# Beyond Hulten: nonlinear aggregation of sectoral shocks (Baqaee–Farhi)

Baqaee and Farhi (2019), "The Macroeconomic Impact of Microeconomic Shocks:
Beyond Hulten's Theorem", Econometrica, §3 (the one-layer CES economy).

**The economy.** Sectors `i ∈ n` produce with labour only, `yᵢ = zᵢ lᵢ`. Final
output is a CES aggregate of sector goods with elasticity of substitution
`θ > 0`, `θ ≠ 1`, and labour is supplied inelastically. Normalising the
initial point, equilibrium log real GDP as a function of log productivities
`x = log z` is
`log Y(x) = (1/(θ−1)) log Σᵢ bᵢ e^{(θ−1)xᵢ}` (`logY`), with `bᵢ > 0`,
and sector `i`'s sales share (Domar weight) is
`λᵢ(x) = bᵢ e^{(θ−1)xᵢ} / Σⱼ bⱼ e^{(θ−1)xⱼ}` (`domar`).

**Results.**
* `hasDerivAt_logY`: along any direction `d`, `d log Y/dt = Σ λᵢ dᵢ`:
  **Hulten's theorem** holds to first order at every point.
* `hasDerivAt_domar`: `dλᵢ/dt = (θ − 1) λᵢ (dᵢ − Σⱼ λⱼ dⱼ)`; `second_order`:
  `d² log Y/dt² = (θ − 1) Var_λ(d)` (Baqaee–Farhi's second-order term).
* `logY_add_sub`: exact response `log Y(x+d) − log Y(x) = (1/(θ−1)) log Σ λᵢ e^{(θ−1)dᵢ}`.
* `complements_le_hulten` (`θ < 1`): the exact response is **at most** the
  Hulten approximation `Σ λᵢ dᵢ` for every shock `d` — negative shocks hurt
  more and positive shocks help less than Hulten predicts.
  `substitutes_ge_hulten` (`θ > 1`): the reverse.
* `complements_asymmetry`: with complements, a productivity shock `+s` to
  sector `i` raises GDP by less than the shock `−s` lowers it.

**Deviations.** The closed form for equilibrium log GDP and the Domar weights
is taken as the definition of the economy (it follows from CES cost
minimisation; the derivation is standard and not formalised). Only the
one-layer (no intermediate inputs) CES economy is treated. At `θ = 1` the
formula is a junk value (`0⁻¹ = 0` in Lean); the Cobb–Douglas case is the
limit and is covered by `Macro/ProductionNetworks.lean`; every theorem here assumes `θ ≠ 1`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

namespace Econ
namespace BaqaeeFarhi

open Finset Real

/-- A one-layer CES economy. -/
structure Economy (n : Type*) [Fintype n] where
  /-- Elasticity of substitution across sector goods. -/
  θ : ℝ
  /-- Share parameters. -/
  b : n → ℝ
  hb : ∀ i, 0 < b i
  [ne : Nonempty n]

namespace Economy

variable {n : Type*} [Fintype n] (E : Economy n)

/-- `Σᵢ bᵢ e^{(θ−1)xᵢ}`. -/
def S (x : n → ℝ) : ℝ := ∑ i, E.b i * exp ((E.θ - 1) * x i)

theorem S_pos (x : n → ℝ) : 0 < E.S x := by
  have := E.ne
  exact sum_pos (fun i _ => mul_pos (E.hb i) (exp_pos _)) univ_nonempty

/-- Equilibrium log real GDP as a function of log productivities. -/
def logY (x : n → ℝ) : ℝ := (E.θ - 1)⁻¹ * log (E.S x)

/-- Domar weight (sales share) of sector `i`. -/
def domar (x : n → ℝ) (i : n) : ℝ := E.b i * exp ((E.θ - 1) * x i) / E.S x

theorem domar_pos (x : n → ℝ) (i : n) : 0 < E.domar x i :=
  div_pos (mul_pos (E.hb i) (exp_pos _)) (E.S_pos x)

theorem sum_domar (x : n → ℝ) : ∑ i, E.domar x i = 1 := by
  simp only [domar, ← Finset.sum_div]
  exact div_self (E.S_pos x).ne'

theorem hasDerivAt_num_aux (x d : n → ℝ) (i : n) :
    HasDerivAt (fun t : ℝ => exp ((E.θ - 1) * (x i + t * d i)))
      (exp ((E.θ - 1) * x i) * ((E.θ - 1) * d i)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (E.θ - 1) * (x i + t * d i)) ((E.θ - 1) * d i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d i)).const_add (x i)
      |>.const_mul (E.θ - 1)
  have h2 := (Real.hasDerivAt_exp _).comp 0 h1
  rw [zero_mul, add_zero] at h2
  exact h2

/-- Derivative of `S` along a line. -/
theorem hasDerivAt_S (x d : n → ℝ) :
    HasDerivAt (fun t : ℝ => E.S (x + t • d))
      (∑ i, E.b i * (exp ((E.θ - 1) * x i) * ((E.θ - 1) * d i))) 0 := by
  unfold S
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.const_mul _ ?_
  exact E.hasDerivAt_num_aux x d i

/-- **Hulten's theorem holds locally.** Along any direction of productivity
change `d`, the derivative of log GDP is `Σ λᵢ dᵢ`. -/
theorem hasDerivAt_logY (hθ : E.θ ≠ 1) (x d : n → ℝ) :
    HasDerivAt (fun t : ℝ => E.logY (x + t • d)) (∑ i, E.domar x i * d i) 0 := by
  have hθ' : E.θ - 1 ≠ 0 := sub_ne_zero.2 hθ
  have hS := E.hasDerivAt_S x d
  have hS0 : E.S (x + (0 : ℝ) • d) = E.S x := by simp
  have hne : E.S (x + (0 : ℝ) • d) ≠ 0 := by rw [hS0]; exact (E.S_pos x).ne'
  have hlog := (hS.log hne).const_mul (E.θ - 1)⁻¹
  convert hlog using 1
  · rfl
  rw [hS0]
  simp only [domar, Finset.sum_div, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  field_simp

/-- **Domar weights move with relative productivity** (Baqaee–Farhi): along a
direction `d`, `dλᵢ/dt = (θ − 1) λᵢ (dᵢ − Σⱼ λⱼ dⱼ)`. -/
theorem hasDerivAt_domar (x d : n → ℝ) (i : n) :
    HasDerivAt (fun t : ℝ => E.domar (x + t • d) i)
      ((E.θ - 1) * E.domar x i * (d i - ∑ j, E.domar x j * d j)) 0 := by
  have hS := E.hasDerivAt_S x d
  have hS0 : E.S (x + (0 : ℝ) • d) = E.S x := by simp
  have hne : E.S (x + (0 : ℝ) • d) ≠ 0 := by rw [hS0]; exact (E.S_pos x).ne'
  have hN := (E.hasDerivAt_num_aux x d i).const_mul (E.b i)
  have hq := hN.div hS hne
  convert hq using 1
  · funext t; simp [domar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · have hSx := (E.S_pos x).ne'
    rw [hS0]
    simp only [zero_mul, add_zero, domar]
    have e1 : ∑ j, E.b j * exp ((E.θ - 1) * x j) / E.S x * d j =
        (∑ j, E.b j * exp ((E.θ - 1) * x j) * d j) / E.S x := by
      rw [Finset.sum_div]; exact sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, E.b j * (exp ((E.θ - 1) * x j) * ((E.θ - 1) * d j)) =
        (E.θ - 1) * ∑ j, E.b j * exp ((E.θ - 1) * x j) * d j := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    field_simp

/-- The first derivative of log GDP along `d` at every point of the line. -/
theorem deriv_logY_line (hθ : E.θ ≠ 1) (x d : n → ℝ) :
    deriv (fun t : ℝ => E.logY (x + t • d)) = fun t => ∑ i, E.domar (x + t • d) i * d i := by
  funext t
  have h := E.hasDerivAt_logY hθ (x + t • d) d
  rw [← sub_self t] at h
  have hc := h.comp_sub_const t t
  have e : (fun s : ℝ => E.logY (x + t • d + (s - t) • d)) = fun s => E.logY (x + s • d) := by
    funext s; congr 1; funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e] at hc
  exact hc.deriv

/-- **The second-order term** (Baqaee–Farhi 2019): the second derivative of log
GDP along `d` is `(θ − 1) Var_λ(d) = (θ − 1)(Σ λᵢ dᵢ² − (Σ λᵢ dᵢ)²)`. Hulten's
first-order approximation is exact only when `θ = 1` or shocks are uniform. -/
theorem second_order (hθ : E.θ ≠ 1) (x d : n → ℝ) :
    deriv (deriv fun t : ℝ => E.logY (x + t • d)) 0 =
      (E.θ - 1) * (∑ i, E.domar x i * d i ^ 2 - (∑ i, E.domar x i * d i) ^ 2) := by
  rw [E.deriv_logY_line hθ]
  have h := HasDerivAt.fun_sum (u := univ) fun i _ => (E.hasDerivAt_domar x d i).mul_const (d i)
  rw [h.deriv]
  set m := ∑ j, E.domar x j * d j
  calc ∑ i, (E.θ - 1) * E.domar x i * (d i - m) * d i
      = ∑ i, ((E.θ - 1) * (E.domar x i * d i ^ 2) - (E.θ - 1) * m * (E.domar x i * d i)) :=
        sum_congr rfl fun i _ => by ring
    _ = (E.θ - 1) * ∑ i, E.domar x i * d i ^ 2 - (E.θ - 1) * m * m := by
        rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
    _ = _ := by ring

/-- **Exact response** to a shock `d` in terms of initial Domar weights. -/
theorem logY_add_sub (hθ : E.θ ≠ 1) (x d : n → ℝ) :
    E.logY (x + d) - E.logY x =
      (E.θ - 1)⁻¹ * log (∑ i, E.domar x i * exp ((E.θ - 1) * d i)) := by
  have hθ' : E.θ - 1 ≠ 0 := sub_ne_zero.2 hθ
  have e : ∑ i, E.domar x i * exp ((E.θ - 1) * d i) = E.S (x + d) / E.S x := by
    simp only [domar, S, Finset.sum_div, Pi.add_apply, mul_add, exp_add]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [e, log_div (E.S_pos _).ne' (E.S_pos _).ne', logY, logY, mul_sub]

/-- Jensen: `Σ λᵢ e^{uᵢ} ≥ e^{Σ λᵢ uᵢ}`. -/
theorem jensen (x u : n → ℝ) :
    (∑ i, E.domar x i * u i) ≤ log (∑ i, E.domar x i * exp (u i)) := by
  have h := convexOn_exp.map_sum_le (t := univ) (w := E.domar x) (p := u)
    (fun i _ => (E.domar_pos x i).le) (E.sum_domar x) (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  rw [le_log_iff_exp_le (sum_pos (fun i _ => mul_pos (E.domar_pos x i) (exp_pos _))
    (by have := E.ne; exact univ_nonempty))]
  exact h

/-- **Complementarities amplify negative shocks** (Baqaee–Farhi). With
`θ < 1`, the exact change in log GDP never exceeds Hulten's first-order
approximation `Σ λᵢ dᵢ`. -/
theorem complements_le_hulten (hθ : E.θ < 1) (x d : n → ℝ) :
    E.logY (x + d) - E.logY x ≤ ∑ i, E.domar x i * d i := by
  have hθ' : E.θ - 1 < 0 := by linarith
  rw [E.logY_add_sub hθ.ne x d]
  have hj := E.jensen x fun i => (E.θ - 1) * d i
  have e : ∑ i, E.domar x i * ((E.θ - 1) * d i) = (E.θ - 1) * ∑ i, E.domar x i * d i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e] at hj
  have := mul_le_mul_of_nonpos_left hj (inv_nonpos.2 hθ'.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hθ'.ne, one_mul] at this

/-- With **substitutes** (`θ > 1`) the exact change is at least Hulten's
approximation. -/
theorem substitutes_ge_hulten (hθ : 1 < E.θ) (x d : n → ℝ) :
    ∑ i, E.domar x i * d i ≤ E.logY (x + d) - E.logY x := by
  have hθ' : 0 < E.θ - 1 := by linarith
  rw [E.logY_add_sub hθ.ne' x d]
  have hj := E.jensen x fun i => (E.θ - 1) * d i
  have e : ∑ i, E.domar x i * ((E.θ - 1) * d i) = (E.θ - 1) * ∑ i, E.domar x i * d i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [e] at hj
  have := mul_le_mul_of_nonneg_left hj (inv_nonneg.2 hθ'.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hθ'.ne', one_mul] at this

/-- **Asymmetry.** With complements, the GDP gain from a productivity
improvement `s` in one sector is no larger than the loss from a decline `s`:
`log Y(x + s eᵢ) + log Y(x − s eᵢ) ≤ 2 log Y(x)`. -/
theorem complements_asymmetry [DecidableEq n] (hθ : E.θ < 1) (x : n → ℝ) (i : n) (s : ℝ) :
    E.logY (x + Pi.single i s) + E.logY (x + Pi.single i (-s)) ≤ 2 * E.logY x := by
  have h1 := E.complements_le_hulten hθ x (Pi.single i s)
  have h2 := E.complements_le_hulten hθ x (Pi.single i (-s))
  have e : ∀ v : ℝ, ∑ j, E.domar x j * (Pi.single i v : n → ℝ) j = E.domar x i * v := by
    intro v
    rw [sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [e] at h1 h2
  linarith

end Economy
end BaqaeeFarhi
end Econ

end
