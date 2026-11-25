/-
# Optimal fiscal policy with state-contingent debt: perfect tax smoothing

Lucas and Stokey (1983), "Optimal Fiscal and Monetary Policy in an Economy
without Capital", JME; Ljungqvist–Sargent, *Recursive Macroeconomic Theory*,
ch. 16 (the primal approach); Chari–Kehoe (1999), §2.

**Setting.** A finite set `ι` of date–event histories `n = (t, sᵗ)` with
weights `w n = βᵗ π(sᵗ) > 0`. The household has quasilinear utility
`c − v(l)` with `v(l) = l^{γ+1}/(γ+1)` (`γ ≥ 1`, Frisch elasticity `1/γ`);
output is linear in labour, so `c n = l n − g n` with exogenous, possibly
stochastic, government purchases `g`. With complete markets (state-contingent
government debt), the **primal approach** characterizes competitive
equilibria by feasibility plus the single **implementability constraint**
`Σ w (u_c c − v'(l) l) = b₀`, i.e. `Σ w (l − g − l^{γ+1}) = b₀`
(`implement`). The labour tax implementing the allocation is
`τ n = 1 − v'(l n)/u_c = 1 − l n ^ γ` (`tax`).

**Results.** At any local maximum of welfare `Σ w (l − g − v(l))` on the
implementability set (the Ramsey problem):
* `ramsey_foc`: Lagrange conditions `a (1 − (γ+1) l^γ) + b (1 − l^γ) = 0`
  history by history, with `(a, b) ≠ 0`;
* `tax_smoothing`: the labour tax is **constant across all dates and states**,
  however volatile government purchases are;
* `labour_constant`: with nonnegative labour, labour itself is constant, so
  consumption absorbs all of the spending shocks one-for-one.
* `first_best`: non-vacuity — when no distortionary revenue is needed, `l ≡ 1`
  is a Ramsey optimum with zero taxes.

`ramsey_foc` is in Fritz John form: `a` multiplies the gradient of the
implementability constraint and `b` that of welfare, with `(a, b) ≠ 0`.

**Deviations.** Quasilinear utility with isoelastic disutility. The general
Lucas–Stokey result is only that taxes are history-independent, `τ_t =
τ(g_t)` for `t ≥ 1`, with date 0 special; full constancy here comes from
quasilinearity (`g` shifts welfare and the implementability constraint only in
levels, and `u_c ≡ 1` removes the `u_{c,0} b₀` term). Government debt is not
modelled explicitly: fixing `b₀` is fixing the level of the implementability
constraint, and the state-contingent debt that implements the allocation is
not constructed. A finite set of histories (finite truncation of the
infinite horizon); interior Ramsey optimum (no nonnegativity constraints).
Existence of a Ramsey optimum is shown only in the first-best case.
-/
module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

noncomputable section

namespace Econ
namespace LucasStokey

open Finset

variable {ι : Type*} [Fintype ι]

/-- Ramsey welfare `Σ w (l − g − l^{γ+1}/(γ+1))`. -/
def welfare (γ : ℕ) (w g : ι → ℝ) (l : ι → ℝ) : ℝ :=
  ∑ n, w n * (l n - g n - l n ^ (γ + 1) / (γ + 1))

/-- The implementability constraint's left side `Σ w (l − g − l^{γ+1})`
(the present value of the primary surplus valued at equilibrium prices). -/
def implement (γ : ℕ) (w g : ι → ℝ) (l : ι → ℝ) : ℝ :=
  ∑ n, w n * (l n - g n - l n ^ (γ + 1))

/-- The labour-income tax implementing `l`: `τ = 1 − v'(l)/u_c`. -/
def tax (γ : ℕ) (l : ι → ℝ) (n : ι) : ℝ := 1 - l n ^ γ

theorem hasStrictFDerivAt_term (γ : ℕ) (w g : ι → ℝ) (c : ℝ) (l₀ : ι → ℝ) (n : ι) :
    HasStrictFDerivAt (fun l : ι → ℝ => w n * (l n - g n - c * l n ^ (γ + 1)))
      ((w n * (1 - c * ((γ + 1 : ℕ) * l₀ n ^ γ))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) n) l₀ := by
  have hp : HasStrictDerivAt (fun x : ℝ => w n * (x - g n - c * x ^ (γ + 1)))
      (w n * (1 - c * ((γ + 1 : ℕ) * l₀ n ^ γ))) (l₀ n) := by
    have h1 := HasStrictDerivAt.sub (HasStrictDerivAt.sub (hasStrictDerivAt_id (l₀ n)) (hasStrictDerivAt_const (l₀ n) (g n)))
      (HasStrictDerivAt.const_mul c (hasStrictDerivAt_pow (γ + 1) (l₀ n)))
    have h2 := HasStrictDerivAt.const_mul (w n) h1
    convert h2 using 1 <;> simp
  have := HasStrictDerivAt.comp_hasStrictFDerivAt l₀ hp (hasStrictFDerivAt_apply (𝕜 := ℝ) n l₀)
  simpa [Function.comp_def] using this

variable [DecidableEq ι]

/-- **Ramsey first-order conditions** (primal approach). -/
theorem ramsey_foc {γ : ℕ} {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n)
    (hmax : IsLocalMaxOn (welfare γ w g)
      {l | implement γ w g l = implement γ w g l₀} l₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧
      ∀ n, a * (1 - (γ + 1) * l₀ n ^ γ) + b * (1 - l₀ n ^ γ) = 0 := by
  have hW : HasStrictFDerivAt (welfare γ w g)
      (∑ n, (w n * (1 - (1 / (γ + 1 : ℝ)) * ((γ + 1 : ℕ) * l₀ n ^ γ))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) n) l₀ := by
    have := HasStrictFDerivAt.fun_sum (u := univ)
      (fun n _ => hasStrictFDerivAt_term γ w g (1 / (γ + 1 : ℝ)) l₀ n)
    convert this using 1
    funext l
    simp only [welfare]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hI : HasStrictFDerivAt (implement γ w g)
      (∑ n, (w n * (1 - 1 * ((γ + 1 : ℕ) * l₀ n ^ γ))) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) n) l₀ := by
    have := HasStrictFDerivAt.fun_sum (u := univ)
      (fun n _ => hasStrictFDerivAt_term γ w g 1 l₀ n)
    convert this using 1
    funext l
    simp only [implement, one_mul]
  obtain ⟨a, b, hab, heq⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inr hmax) hI hW
  refine ⟨a, b, hab, fun n => ?_⟩
  have h := congrArg (fun L => L (Pi.single n 1)) heq
  simp [sum_apply, Pi.single_apply] at h
  have hγ : (γ + 1 : ℝ) ≠ 0 := by positivity
  have h' : w n * (a * (1 - (γ + 1) * l₀ n ^ γ) + b * (1 - l₀ n ^ γ)) = 0 := by
    have e : (γ + 1 : ℝ)⁻¹ * ((γ + 1) * l₀ n ^ γ) = l₀ n ^ γ := by field_simp
    rw [e] at h
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (hw n).ne'

/-- **Perfect tax smoothing.** At a Ramsey optimum the labour tax is the same
at every date and in every state, whatever the path of government purchases. -/
theorem tax_smoothing {γ : ℕ} (hγ : 1 ≤ γ) {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n)
    (hmax : IsLocalMaxOn (welfare γ w g)
      {l | implement γ w g l = implement γ w g l₀} l₀) :
    ∃ τ : ℝ, ∀ n, tax γ l₀ n = τ := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨n₀⟩⟩
  · exact ⟨0, fun n => isEmptyElim n⟩
  obtain ⟨a, b, hab, hk⟩ := ramsey_foc hw hmax
  have hc : a * (γ + 1) + b ≠ 0 := by
    intro h0
    apply hab
    have hb : b = -(a * (γ + 1)) := by linarith
    have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
    have := hk n₀
    rw [hb] at this
    have ha : a * γ = 0 := by linear_combination -this
    have ha0 : a = 0 := (mul_eq_zero.1 ha).resolve_right hγ'.ne'
    simp [ha0, hb]
  refine ⟨1 - (a + b) / (a * (γ + 1) + b), fun n => ?_⟩
  have hX : l₀ n ^ γ = (a + b) / (a * (γ + 1) + b) := by
    rw [eq_div_iff hc]
    linear_combination -(hk n)
  simp only [tax, hX]

/-- **Labour is constant** across dates and states (given nonnegative labour):
consumption `l − g` absorbs every spending shock. -/
theorem labour_constant {γ : ℕ} (hγ : 1 ≤ γ) {w g l₀ : ι → ℝ} (hw : ∀ n, 0 < w n)
    (hl : ∀ n, 0 ≤ l₀ n)
    (hmax : IsLocalMaxOn (welfare γ w g)
      {l | implement γ w g l = implement γ w g l₀} l₀) (n m : ι) :
    l₀ n = l₀ m := by
  obtain ⟨τ, hτ⟩ := tax_smoothing hγ hw hmax
  have h : l₀ n ^ γ = l₀ m ^ γ := by
    have h1 := hτ n
    have h2 := hτ m
    simp only [tax] at h1 h2
    linarith
  exact (pow_left_inj₀ (hl n) (hl m) (by omega : γ ≠ 0)).1 h

omit [DecidableEq ι] in
/-- **Non-vacuity: the first best.** If initial claims are such that the
government needs no distortionary revenue (`b₀ = implement 1`), then `l ≡ 1`
is a Ramsey optimum (a local, indeed global on `l ≥ 0`, maximum of welfare)
and the tax is zero in every state. -/
theorem first_best (γ : ℕ) {w g : ι → ℝ} (hw : ∀ n, 0 ≤ w n) :
    IsLocalMaxOn (welfare γ w g) {l | implement γ w g l = implement γ w g 1} 1 ∧
      ∀ n, tax γ (1 : ι → ℝ) n = 0 := by
  refine ⟨IsLocalMax.isLocalMaxOn ?_ _, fun n => by simp [tax]⟩
  have hpos : ∀ᶠ l in nhds (1 : ι → ℝ), ∀ n, 0 < l n :=
    Filter.eventually_all.2 fun n =>
      (continuous_apply n).continuousAt.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hpos] with l hl
  simp only [welfare]
  refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (hw n)
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ l n - 1 by linarith [hl n]) (γ + 1)
  have hγ : (0 : ℝ) < γ + 1 := by positivity
  simp only [Pi.one_apply, one_pow]
  rw [show 1 + (l n - 1) = l n by ring] at hb
  push_cast at hb
  have : 1 / ((γ : ℝ) + 1) + l n - 1 ≤ l n ^ (γ + 1) / (γ + 1) := by
    rw [le_div_iff₀ hγ]; field_simp; nlinarith
  linarith

end LucasStokey
end Econ

end
