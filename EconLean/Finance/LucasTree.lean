/-
# The Lucas tree: Euler pricing on a finite Markov chain

Lucas (1978); Ljungqvist–Sargent ch. 13; Cochrane, *Asset Pricing*, ch. 1 and 5;
Hansen–Jagannathan (1991); Mehra–Prescott (1985).

**Setup.** The state `z` follows a Markov chain with stochastic matrix `Q`
(`Econ.IsStochastic`). A tree pays dividend `d(z) > 0`. A representative
consumer with discount factor `β ∈ (0,1)` and marginal utility `u' > 0` holds
the tree; in equilibrium consumption equals the dividend. The ex-dividend price
`p(z)` must satisfy the consumer's Euler equation

  `u'(d(z)) p(z) = β Σ_{z'} Q(z,z') u'(d(z')) (p(z') + d(z'))`   (`IsPrice`).

Equivalently `p(z) = E_z[m (p' + d')]` with stochastic discount factor
`m(z,z') = β u'(d(z'))/u'(d(z))` (`isPrice_iff_sdf`).

**Results.**
* `existsUnique_price`: there is exactly one price function. (The map
  `f ↦ β Q f` contracts in the sup norm, so `I − βQ` is invertible.)
* `price_pos`: that price is strictly positive.
* `isPrice_log`: with log utility, `p(z) = β/(1−β) · d(z)`.
* `euler_return`: the gross return `R = (p' + d')/p` satisfies `E_z[m R] = 1`.
* `riskFree`: a one-period risk-free bond has return `R_f(z) = 1/E_z[m]`.
* `premium_eq`: **equity premium** formula
  `E_z[R] − R_f(z) = −R_f(z) Cov_z(m, R)`.
* `hansen_jagannathan`: `(E_z[R] − R_f)² ≤ (Var_z m / (E_z m)²) Var_z R`, i.e.
  the Sharpe ratio is bounded by `σ(m)/E(m)`. `hj_bound` is the general bound
  for any return `r` with `E[m r] = 1`.

**Deviations.** Finite state space. Concavity of utility is not assumed (only
`u' > 0`), so the sign of the equity premium is not determined here. Equilibrium is defined by the
representative consumer's Euler equation with consumption equal to dividends;
the household's optimization problem itself is not modelled here.
-/
module

public import EconLean.Macro.DP.MarkovChain
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

namespace Econ
namespace LucasTree

open Finset Matrix

/-! ### Conditional moments under a finite probability vector -/

section Moments

variable {Z : Type*} [Fintype Z]

/-- Expectation `Σ w_z f_z`. -/
def expect (w f : Z → ℝ) : ℝ := ∑ z, w z * f z

/-- Covariance `E[(f − Ef)(g − Eg)]`. -/
def cov (w f g : Z → ℝ) : ℝ := expect w fun z => (f z - expect w f) * (g z - expect w g)

/-- Variance. -/
def var (w f : Z → ℝ) : ℝ := cov w f f

theorem expect_mul_eq {w : Z → ℝ} (hw : ∑ z, w z = 1) (f g : Z → ℝ) :
    expect w (fun z => f z * g z) = expect w f * expect w g + cov w f g := by
  simp only [cov, expect]
  have e : ∀ z, w z * ((f z - ∑ z, w z * f z) * (g z - ∑ z, w z * g z)) =
      w z * (f z * g z) - (∑ z, w z * g z) * (w z * f z) - (∑ z, w z * f z) * (w z * g z) +
      (∑ z, w z * f z) * (∑ z, w z * g z) * w z := fun z => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, hw]
  ring

/-- Cauchy–Schwarz: `Cov(f,g)² ≤ Var f · Var g`. -/
theorem cov_sq_le {w : Z → ℝ} (hw : ∀ z, 0 ≤ w z) (f g : Z → ℝ) :
    cov w f g ^ 2 ≤ var w f * var w g := by
  simp only [var, cov, expect]
  refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun z _ => mul_nonneg (hw z) (mul_self_nonneg _))
    (fun z _ => mul_nonneg (hw z) (mul_self_nonneg _)) fun z _ => le_of_eq (by ring)

theorem expect_const {w : Z → ℝ} (hw : ∑ z, w z = 1) (c : ℝ) : expect w (fun _ => c) = c := by
  simp [expect, ← sum_mul, hw]

theorem var_sub_const {w : Z → ℝ} (hw : ∑ z, w z = 1) (f : Z → ℝ) (c : ℝ) :
    var w (fun z => f z - c) = var w f := by
  have : expect w (fun z => f z - c) = expect w f - c := by
    simp only [expect, mul_sub, sum_sub_distrib, ← sum_mul, hw, one_mul]
  simp only [var, cov, this]
  congr 1; funext z; ring

/-- **Hansen–Jagannathan bound** for any return `r` priced by `m`
(`E[m r] = 1`, `E[m] > 0`): `(E r − 1/E m)² ≤ (Var m / (E m)²) · Var r`. -/
theorem hj_bound {w : Z → ℝ} (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1) {m r : Z → ℝ}
    (hm : 0 < expect w m) (he : expect w (fun z => m z * r z) = 1) :
    (expect w r - 1 / expect w m) ^ 2 ≤ var w m / expect w m ^ 2 * var w r := by
  rw [expect_mul_eq hw1] at he
  have hcs := cov_sq_le hw m r
  have e : expect w r - 1 / expect w m = -cov w m r / expect w m := by
    field_simp; linarith
  rw [e, div_mul_eq_mul_div, div_pow, neg_sq]
  exact div_le_div_of_nonneg_right hcs (by positivity)

end Moments

/-- A Lucas tree economy on a finite Markov chain. -/
structure Tree (Z : Type*) [Fintype Z] where
  Q : Matrix Z Z ℝ
  hQ : IsStochastic Q
  /-- Dividend (= consumption in equilibrium). -/
  d : Z → ℝ
  hd : ∀ z, 0 < d z
  /-- Marginal utility. -/
  u' : ℝ → ℝ
  hu' : ∀ c, 0 < c → 0 < u' c
  β : ℝ
  hβ₀ : 0 < β
  hβ₁ : β < 1

namespace Tree

variable {Z : Type*} [Fintype Z] (T : Tree Z)

/-- Marginal utility of the dividend in each state. -/
def mu (z : Z) : ℝ := T.u' (T.d z)

theorem mu_pos (z : Z) : 0 < T.mu z := T.hu' _ (T.hd z)

/-- **Equilibrium price function**: the Euler equation with `c = d`. -/
def IsPrice (p : Z → ℝ) : Prop :=
  ∀ z, T.mu z * p z = T.β * ∑ z', T.Q z z' * (T.mu z' * (p z' + T.d z'))

/-- Stochastic discount factor `m(z,z') = β u'(d(z'))/u'(d(z))`. -/
def sdf (z z' : Z) : ℝ := T.β * T.mu z' / T.mu z

theorem sdf_pos (z z' : Z) : 0 < T.sdf z z' :=
  div_pos (mul_pos T.hβ₀ (T.mu_pos z')) (T.mu_pos z)

/-- Euler pricing in SDF form: `p(z) = E_z[m (p' + d')]`. -/
theorem isPrice_iff_sdf (p : Z → ℝ) :
    T.IsPrice p ↔ ∀ z, p z = expect (T.Q z) fun z' => T.sdf z z' * (p z' + T.d z') := by
  refine forall_congr' fun z => ?_
  have h := (T.mu_pos z).ne'
  have e : ∑ z', T.Q z z' * (T.sdf z z' * (p z' + T.d z')) =
      (T.β * ∑ z', T.Q z z' * (T.mu z' * (p z' + T.d z'))) / T.mu z := by
    rw [mul_sum, sum_div]
    exact sum_congr rfl fun _ _ => by simp only [sdf]; field_simp
  simp only [expect]
  rw [e, eq_div_iff h]
  constructor <;> intro e' <;> linarith

/-- Discounted transition operator `f ↦ β Q f` as a linear map. -/
def op : (Z → ℝ) →ₗ[ℝ] (Z → ℝ) := LinearMap.id - T.β • Matrix.mulVecLin T.Q

/-- Fixed points of `f = β Q f` vanish (sup-norm contraction). -/
theorem eq_zero_of_fixed {δ : Z → ℝ} (h : ∀ z, δ z = T.β * ∑ z', T.Q z z' * δ z') : δ = 0 := by
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact funext fun z => hZ.elim z
  obtain ⟨z₀, hz₀⟩ := Finite.exists_max fun z => |δ z|
  have hb : |δ z₀| ≤ T.β * |δ z₀| := by
    calc |δ z₀| = T.β * |∑ z', T.Q z₀ z' * δ z'| := by
          rw [← abs_of_pos T.hβ₀, ← abs_mul, ← h z₀]
      _ ≤ T.β * |δ z₀| := mul_le_mul_of_nonneg_left ?_ T.hβ₀.le
    calc |∑ z', T.Q z₀ z' * δ z'| ≤ ∑ z', |T.Q z₀ z' * δ z'| := abs_sum_le_sum_abs _ _
      _ = ∑ z', T.Q z₀ z' * |δ z'| := sum_congr rfl fun z' _ => by
          rw [abs_mul, abs_of_nonneg (T.hQ.1 _ _)]
      _ ≤ ∑ z', T.Q z₀ z' * |δ z₀| :=
          sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (hz₀ z') (T.hQ.1 _ _)
      _ = |δ z₀| := by rw [← sum_mul, T.hQ.2, one_mul]
  have h0 : |δ z₀| = 0 := by
    have := abs_nonneg (δ z₀); nlinarith [T.hβ₁]
  funext z
  have := hz₀ z
  rw [h0] at this
  exact abs_nonpos_iff.1 this

theorem op_apply (f : Z → ℝ) (z : Z) :
    T.op f z = f z - T.β * ∑ z', T.Q z z' * f z' := by
  simp [op, Matrix.mulVec, dotProduct]

theorem op_injective : Function.Injective T.op := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro δ hδ
  refine T.eq_zero_of_fixed fun z => ?_
  have := congrFun hδ z
  rw [op_apply] at this
  simpa [sub_eq_zero] using this

/-- `IsPrice p` iff `f = u'(d) p` solves `(I − βQ) f = βQ (u'(d) d)`. -/
theorem isPrice_iff_op (p : Z → ℝ) :
    T.IsPrice p ↔ T.op (fun z => T.mu z * p z) =
      fun z => T.β * ∑ z', T.Q z z' * (T.mu z' * T.d z') := by
  simp only [IsPrice, funext_iff, op_apply]
  refine forall_congr' fun z => ?_
  have : ∑ z', T.Q z z' * (T.mu z' * (p z' + T.d z')) =
      ∑ z', T.Q z z' * (T.mu z' * p z') + ∑ z', T.Q z z' * (T.mu z' * T.d z') := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
  rw [this]
  constructor <;> intro h <;> linarith

/-- **Existence and uniqueness of the equilibrium price function.** -/
theorem existsUnique_price : ∃! p, T.IsPrice p := by
  obtain ⟨f, hf⟩ := (LinearMap.injective_iff_surjective.1 T.op_injective)
    fun z => T.β * ∑ z', T.Q z z' * (T.mu z' * T.d z')
  refine ⟨fun z => f z / T.mu z, ?_, fun p hp => ?_⟩
  · show T.IsPrice _
    rw [isPrice_iff_op]
    convert hf using 2
    funext z; field_simp [(T.mu_pos z).ne']
  · change T.IsPrice p at hp
    rw [isPrice_iff_op, ← hf] at hp
    funext z
    have := congrFun (T.op_injective hp) z
    field_simp [(T.mu_pos z).ne']
    linarith

/-- **The equilibrium price is strictly positive.** -/
theorem price_pos {p : Z → ℝ} (hp : T.IsPrice p) (z : Z) : 0 < p z := by
  have hZ : Nonempty Z := ⟨z⟩
  obtain ⟨z₀, hz₀⟩ := Finite.exists_min fun z => T.mu z * p z
  -- expected marginal-utility-weighted dividends are positive
  have hg : 0 < ∑ z', T.Q z₀ z' * (T.mu z' * T.d z') := by
    obtain ⟨z', hz'⟩ : ∃ z', 0 < T.Q z₀ z' := by
      by_contra hc; push Not at hc
      have : ∑ z', T.Q z₀ z' ≤ 0 := sum_nonpos fun z' _ => hc z'
      rw [T.hQ.2] at this; norm_num at this
    exact sum_pos' (fun z'' _ => mul_nonneg (T.hQ.1 _ _) (mul_pos (T.mu_pos _) (T.hd _)).le)
      ⟨z', mem_univ _, mul_pos hz' (mul_pos (T.mu_pos _) (T.hd _))⟩
  have hS : T.mu z₀ * p z₀ + ∑ z', T.Q z₀ z' * (T.mu z' * T.d z') ≤
      ∑ z', T.Q z₀ z' * (T.mu z' * (p z' + T.d z')) :=
    calc T.mu z₀ * p z₀ + ∑ z', T.Q z₀ z' * (T.mu z' * T.d z')
        = ∑ z', T.Q z₀ z' * (T.mu z₀ * p z₀ + T.mu z' * T.d z') := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, T.hQ.2 z₀, one_mul]
      _ ≤ ∑ z', T.Q z₀ z' * (T.mu z' * (p z' + T.d z')) :=
          sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (by nlinarith [hz₀ z']) (T.hQ.1 _ _)
  have h1 := mul_le_mul_of_nonneg_left hS T.hβ₀.le
  have hp0 := hp z₀
  have hG := mul_pos T.hβ₀ hg
  have h2 : 0 < T.mu z₀ * p z₀ := by nlinarith [T.hβ₁, T.hβ₀]
  have h3 : 0 < T.mu z * p z := h2.trans_le (hz₀ z)
  exact pos_of_mul_pos_right h3 (T.mu_pos z).le

/-- **Log utility.** With `u'(c) = 1/c` the price–dividend ratio is constant:
`p(z) = β/(1−β) · d(z)`. -/
theorem isPrice_log (hlog : ∀ c, 0 < c → T.u' c = c⁻¹) :
    T.IsPrice fun z => T.β / (1 - T.β) * T.d z := by
  intro z
  have hm : ∀ z, T.mu z = (T.d z)⁻¹ := fun z => hlog _ (T.hd z)
  have h1 : (1 - T.β) ≠ 0 := by linarith [T.hβ₁]
  have e : ∀ z', T.Q z z' * (T.mu z' * (T.β / (1 - T.β) * T.d z' + T.d z')) =
      T.Q z z' * (1 / (1 - T.β)) := fun z' => by
    rw [hm]; field_simp [(T.hd z').ne']; ring
  rw [sum_congr rfl fun z' _ => e z', ← sum_mul, T.hQ.2, hm]
  field_simp [(T.hd z).ne']

/-- Gross return on the tree from `z` to `z'`. -/
def ret (p : Z → ℝ) (z z' : Z) : ℝ := (p z' + T.d z') / p z

/-- **Euler equation for returns**: `E_z[m R] = 1`. -/
theorem euler_return {p : Z → ℝ} (hp : T.IsPrice p) (z : Z) :
    expect (T.Q z) (fun z' => T.sdf z z' * T.ret p z z') = 1 := by
  have h := (T.isPrice_iff_sdf p).1 hp z
  have hpz := (T.price_pos hp z).ne'
  simp only [expect, ret] at h ⊢
  have e : ∑ z', T.Q z z' * (T.sdf z z' * ((p z' + T.d z') / p z)) =
      (∑ z', T.Q z z' * (T.sdf z z' * (p z' + T.d z'))) / p z := by
    rw [sum_div]; exact sum_congr rfl fun _ _ => by ring
  rw [e, ← h, div_self hpz]

/-- Price of a one-period risk-free bond paying `1` in every state. -/
def bondPrice (z : Z) : ℝ := expect (T.Q z) (T.sdf z)

theorem bondPrice_pos [Nonempty Z] (z : Z) : 0 < T.bondPrice z := by
  obtain ⟨z', hz'⟩ : ∃ z', 0 < T.Q z z' := by
    by_contra hc; push Not at hc
    have : ∑ z', T.Q z z' ≤ 0 := sum_nonpos fun z' _ => hc z'
    rw [T.hQ.2] at this; norm_num at this
  exact sum_pos' (fun z'' _ => mul_nonneg (T.hQ.1 _ _) (T.sdf_pos _ _).le)
    ⟨z', mem_univ _, mul_pos hz' (T.sdf_pos _ _)⟩

/-- Risk-free gross return `R_f(z) = 1/E_z[m]`. -/
def riskFree (z : Z) : ℝ := 1 / T.bondPrice z

/-- The risk-free return satisfies the Euler equation `E_z[m R_f] = 1`. -/
theorem euler_riskFree [Nonempty Z] (z : Z) :
    expect (T.Q z) (fun z' => T.sdf z z' * T.riskFree z) = 1 := by
  simp only [expect, riskFree, ← mul_assoc, ← sum_mul]
  rw [← expect, ← bondPrice]
  field_simp [(T.bondPrice_pos z).ne']

/-- **Equity premium**: `E_z[R] − R_f(z) = −R_f(z) · Cov_z(m, R)`. Assets whose
returns covary negatively with the SDF (pay off in good times) earn a premium. -/
theorem premium_eq {p : Z → ℝ} (hp : T.IsPrice p) (z : Z) :
    expect (T.Q z) (T.ret p z) - T.riskFree z =
      -T.riskFree z * cov (T.Q z) (T.sdf z) (T.ret p z) := by
  have hZ : Nonempty Z := ⟨z⟩
  have h := T.euler_return hp z
  rw [expect_mul_eq (T.hQ.2 z)] at h
  have hb := (T.bondPrice_pos z).ne'
  simp only [riskFree, bondPrice] at hb ⊢
  field_simp
  linarith

/-- **Hansen–Jagannathan bound.** The squared Sharpe ratio of the tree is at
most `Var(m)/E(m)²`: `(E_z R − R_f)² ≤ (Var_z m / (E_z m)²) · Var_z R`. -/
theorem hansen_jagannathan {p : Z → ℝ} (hp : T.IsPrice p) (z : Z) :
    (expect (T.Q z) (T.ret p z) - T.riskFree z) ^ 2 ≤
      var (T.Q z) (T.sdf z) / T.bondPrice z ^ 2 * var (T.Q z) (T.ret p z) := by
  have hZ : Nonempty Z := ⟨z⟩
  rw [T.premium_eq hp z]
  have hb := T.bondPrice_pos z
  have hcs := cov_sq_le (T.hQ.1 z) (T.sdf z) (T.ret p z)
  simp only [riskFree]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have : (-(1 / T.bondPrice z) * cov (T.Q z) (T.sdf z) (T.ret p z)) ^ 2 * T.bondPrice z ^ 2 =
      cov (T.Q z) (T.sdf z) (T.ret p z) ^ 2 := by field_simp
  linarith

end Tree

/-- **Non-vacuity.** Two states, i.i.d. with probability `1/2`, dividends `1`
and `2`, log utility, `β = 1/2`. The price `p = d` (`β/(1−β) = 1`) is the
equilibrium price function. -/
example : ∃ T : Tree Bool, T.IsPrice T.d := by
  refine ⟨⟨fun _ _ => 1 / 2, ⟨fun _ _ => by norm_num, fun _ => by norm_num⟩,
    fun z => if z then 2 else 1, fun z => by split_ifs <;> norm_num, fun c => c⁻¹,
    fun c hc => inv_pos.2 hc, 1 / 2, by norm_num, by norm_num⟩, ?_⟩
  have := Tree.isPrice_log (⟨fun _ _ => 1 / 2, ⟨fun _ _ => by norm_num, fun _ => by norm_num⟩,
    fun z => if z then 2 else 1, fun z => by split_ifs <;> norm_num, fun c => c⁻¹,
    fun c hc => inv_pos.2 hc, 1 / 2, by norm_num, by norm_num⟩ : Tree Bool) fun _ _ => rfl
  convert this using 2
  norm_num

end LucasTree
end Econ

end
