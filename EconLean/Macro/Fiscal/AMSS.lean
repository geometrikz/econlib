/-
# Tax smoothing with risk-free debt: martingale taxes (Barro; AMSS)

Barro (1979), "On the Determination of the Public Debt", JPE; Aiyagari,
Marcet, Sargent and Seppälä (2002), "Optimal Taxation without
State-Contingent Debt", JPE; Ljungqvist–Sargent, *Recursive Macroeconomic
Theory*, ch. 16–17.

**Setting.** One step of the government's problem. Today the government owes
`b₀`, buys `g₀` and raises taxes `τ₀`; tomorrow one of finitely many states
`s` occurs with probability `π s` and spending is `g s`. Tax revenue `τ`
(a level, not a rate, in this reduced form) costs
`C τ` in deadweight loss (`C` convex, e.g. Barro's quadratic). Bonds are
priced at `1/R`.
* **Incomplete markets** (Barro, AMSS): only a risk-free bond `b` is traded:
  `τ₀ = g₀ + b₀ − b/R` and `τ s = g s + b` (`taxRF`). The government chooses
  `b` to minimize `C(τ₀) + β Σ π C(τ s)` (`costRF`).
* **Complete markets** (Lucas–Stokey): Arrow securities `b s` priced at
  `π s / R` (`taxCM`, `costCM`).

**Results.**
* `euler_rf`: at an optimum, `C'(τ₀) = β R Σ π C'(τ s)`, so with `β R = 1`
  the marginal cost of taxation is a **martingale**; with quadratic cost
  (`martingale_quad`), `τ₀ = E τ₁`: tax revenue itself is a martingale
  (Barro's random walk). The AMSS refinements (a risk-adjusted martingale
  for the multiplier, binding debt limits) are not formalized.
* `rf_spread`: with risk-free debt tomorrow's taxes differ across states by
  exactly the spending difference. This is a two-period artifact (the last
  period must absorb the shock); with a longer horizon debt spreads shocks
  over all future periods.
* `euler_cm`, `cm_constant`: with complete markets and `β R = 1`, `C'` is
  equalized across today and every state, so with strictly monotone `C'`
  the tax is **constant** across states.
* `costCM_const`, `cm_le_rf`: a portfolio paying the same in every state is
  the risk-free bond, so complete markets do at least as well.
* `quad_optimum`: non-vacuity: with quadratic costs the risk-free problem
  has the explicit global minimizer `b* = R(g₀ + b₀ − E g)/(1 + R)`.

**Deviations.** Two periods (the general AMSS result is the same Euler
equation at every node of an event tree, with debt limits possibly binding);
the tax-cost function is a primitive (Barro's reduced form) rather than
derived from labour supply; no debt limits; no explicit optimum is exhibited
for the complete-markets problem.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace AMSS

open Finset

variable {S : Type*} [Fintype S]

/-- Primitives. -/
structure Env (S : Type*) [Fintype S] where
  β : ℝ
  R : ℝ
  π : S → ℝ
  g₀ : ℝ
  b₀ : ℝ
  g : S → ℝ
  hR : 0 < R
  hπ : ∀ s, 0 ≤ π s
  hπ1 : ∑ s, π s = 1

namespace Env

variable (E : Env S)

/-- Taxes under risk-free debt `b`: today, and in state `s`. -/
def tax₀RF (b : ℝ) : ℝ := E.g₀ + E.b₀ - b / E.R
def taxRF (b : ℝ) (s : S) : ℝ := E.g s + b

/-- Expected discounted deadweight cost under risk-free debt. -/
def costRF (C : ℝ → ℝ) (b : ℝ) : ℝ := C (E.tax₀RF b) + E.β * ∑ s, E.π s * C (E.taxRF b s)

/-- **The AMSS / Barro Euler equation.** -/
theorem euler_rf {C C' : ℝ → ℝ} (hC : ∀ x, HasDerivAt C (C' x) x) {b : ℝ}
    (hmin : IsLocalMin (E.costRF C) b) :
    C' (E.tax₀RF b) = E.β * E.R * ∑ s, E.π s * C' (E.taxRF b s) := by
  have h0 : HasDerivAt (fun b => C (E.tax₀RF b)) (C' (E.tax₀RF b) * (-(1 / E.R))) b := by
    have hin : HasDerivAt (fun b : ℝ => E.g₀ + E.b₀ - b / E.R) (-(1 / E.R)) b := by
      have := ((hasDerivAt_id b).div_const E.R).const_sub (E.g₀ + E.b₀)
      simpa [div_eq_mul_inv] using this
    exact (hC _).comp b hin
  have hs : ∀ s, HasDerivAt (fun b => E.π s * C (E.taxRF b s)) (E.π s * C' (E.taxRF b s)) b := by
    intro s
    have hin : HasDerivAt (fun b : ℝ => E.g s + b) 1 b := (hasDerivAt_id b).const_add _
    have := ((hC (E.taxRF b s)).comp b hin).const_mul (E.π s)
    convert this using 1 <;> simp [taxRF]
  have hsum := HasDerivAt.fun_sum (u := univ) (fun s _ => hs s)
  have hD := h0.add (hsum.const_mul E.β)
  have hz := hmin.hasDerivAt_eq_zero (by
    convert hD using 1
    funext x
    simp only [costRF, tax₀RF, taxRF]
    rfl)
  have hR := E.hR.ne'
  field_simp at hz
  linarith

/-- **Martingale taxes** (quadratic deadweight cost `κ τ²/2`, `β R = 1`). -/
theorem martingale_quad {κ : ℝ} (hκ : 0 < κ) (hβR : E.β * E.R = 1) {b : ℝ}
    (hmin : IsLocalMin (E.costRF fun τ => κ * τ ^ 2 / 2) b) :
    E.tax₀RF b = ∑ s, E.π s * E.taxRF b s := by
  have hC : ∀ x, HasDerivAt (fun τ : ℝ => κ * τ ^ 2 / 2) (κ * x) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_mul κ).div_const 2
    convert this using 1
    simp; ring
  have h := E.euler_rf hC hmin
  rw [hβR, one_mul] at h
  have e : ∑ s, E.π s * (κ * E.taxRF b s) = κ * ∑ s, E.π s * E.taxRF b s := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e] at h
  exact mul_left_cancel₀ hκ.ne' h

/-- With risk-free debt, tomorrow's taxes inherit every spending shock. -/
theorem rf_spread (b : ℝ) (s s' : S) : E.taxRF b s - E.taxRF b s' = E.g s - E.g s' := by
  simp only [taxRF]; ring

/-- Today's tax under complete markets (Arrow securities `bs`, priced `π s/R`). -/
def tax₀CM (bs : S → ℝ) : ℝ := E.g₀ + E.b₀ - ∑ s, E.π s * bs s / E.R
def taxCM (bs : S → ℝ) (s : S) : ℝ := E.g s + bs s

/-- Expected discounted deadweight cost under complete markets. -/
def costCM (C : ℝ → ℝ) (bs : S → ℝ) : ℝ :=
  C (E.tax₀CM bs) + E.β * ∑ s, E.π s * C (E.taxCM bs s)

/-- **Complete markets: the marginal cost of taxation is equalized** across
today and every state with positive probability (`β R = 1`). -/
theorem euler_cm [DecidableEq S] {C C' : ℝ → ℝ} (hC : ∀ x, HasDerivAt C (C' x) x)
    (hβR : E.β * E.R = 1) {bs : S → ℝ} (hmin : ∀ s, IsLocalMin (fun x => E.costCM C
      (Function.update bs s x)) (bs s)) (s : S) (hs : 0 < E.π s) :
    C' (E.taxCM bs s) = C' (E.tax₀CM bs) := by
  -- vary the Arrow security for state `s` only
  set f : ℝ → ℝ := fun x => E.costCM C (Function.update bs s x)
  have e : ∀ x, f x = C (E.g₀ + E.b₀ - (∑ s' ∈ univ.erase s, E.π s' * bs s' / E.R) -
      E.π s * x / E.R) + E.β * ((∑ s' ∈ univ.erase s, E.π s' * C (E.g s' + bs s')) +
      E.π s * C (E.g s + x)) := by
    intro x
    simp only [f, costCM, tax₀CM, taxCM]
    rw [← Finset.add_sum_erase _ _ (mem_univ s), ← Finset.add_sum_erase _ _ (mem_univ s)]
    have h1 : ∀ s' ∈ univ.erase s, Function.update bs s x s' = bs s' := fun s' hs' =>
      Function.update_of_ne (Finset.ne_of_mem_erase hs') _ _
    rw [Finset.sum_congr rfl (fun s' hs' => by rw [h1 s' hs']),
      Finset.sum_congr rfl (fun s' hs' => by rw [h1 s' hs'] : ∀ s' ∈ univ.erase s,
        E.π s' * C (E.g s' + Function.update bs s x s') = E.π s' * C (E.g s' + bs s'))]
    simp only [Function.update_self]
    ring_nf
  set A := E.g₀ + E.b₀ - (∑ s' ∈ univ.erase s, E.π s' * bs s' / E.R)
  have hD : HasDerivAt f (C' (A - E.π s * bs s / E.R) * (-(E.π s / E.R)) +
      E.β * (E.π s * C' (E.g s + bs s))) (bs s) := by
    have hin : HasDerivAt (fun x : ℝ => A - E.π s * x / E.R) (-(E.π s / E.R)) (bs s) := by
      have := (((hasDerivAt_id (bs s)).const_mul (E.π s)).div_const E.R).const_sub A
      simpa using this
    have h1 := (hC _).comp (bs s) hin
    have h2 := (((hC _).comp (bs s) ((hasDerivAt_id (bs s)).const_add (E.g s))).const_mul
      (E.π s)).const_add (∑ s' ∈ univ.erase s, E.π s' * C (E.g s' + bs s'))
    have := h1.add (h2.const_mul E.β)
    convert this using 1
    · funext x; rw [e x]; rfl
    · simp
  have hz := (hmin s).hasDerivAt_eq_zero hD
  have h0 : A - E.π s * bs s / E.R = E.tax₀CM bs := by
    simp only [A, tax₀CM]
    rw [← Finset.add_sum_erase _ _ (mem_univ s)]
    ring
  rw [h0] at hz
  have hR := E.hR.ne'
  have hβ : E.β = 1 / E.R := by field_simp; linarith
  rw [hβ] at hz
  field_simp at hz
  have : E.π s * (C' (E.g s + bs s) - C' (E.tax₀CM bs)) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hs.ne'
  simp only [taxCM]
  linarith

/-- **Complete markets: constant taxes.** With strictly increasing marginal
cost, the tax is the same today and in every state with positive
probability, however volatile spending is. -/
theorem cm_constant [DecidableEq S] {C C' : ℝ → ℝ} (hC : ∀ x, HasDerivAt C (C' x) x)
    (hC' : StrictMono C') (hβR : E.β * E.R = 1) {bs : S → ℝ}
    (hmin : ∀ s, IsLocalMin (fun x => E.costCM C (Function.update bs s x)) (bs s)) (s : S)
    (hs : 0 < E.π s) : E.taxCM bs s = E.tax₀CM bs :=
  hC'.injective (E.euler_cm hC hβR hmin s hs)

/-- A state-independent Arrow portfolio is the risk-free bond. -/
theorem costCM_const (C : ℝ → ℝ) (b : ℝ) : E.costCM C (fun _ => b) = E.costRF C b := by
  simp only [costCM, costRF, tax₀CM, tax₀RF, taxCM, taxRF]
  congr 3
  have : ∑ x, E.π x * b / E.R = (∑ x, E.π x) * (b / E.R) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [this, E.hπ1, one_mul]

/-- **Complete markets weakly dominate**: if `bs` minimizes the
complete-markets cost, it does at least as well as any risk-free policy. -/
theorem cm_le_rf {C : ℝ → ℝ} {bs : S → ℝ} (hmin : ∀ bs', E.costCM C bs ≤ E.costCM C bs')
    (b : ℝ) : E.costCM C bs ≤ E.costRF C b := by
  rw [← E.costCM_const]; exact hmin _

/-- **Non-vacuity**: with quadratic costs and `β R = 1` the risk-free problem
has an explicit global minimizer. -/
theorem quad_optimum {κ : ℝ} (hκ : 0 < κ) (hβR : E.β * E.R = 1) (b : ℝ) :
    E.costRF (fun τ => κ * τ ^ 2 / 2)
        (E.R * (E.g₀ + E.b₀ - ∑ s, E.π s * E.g s) / (1 + E.R)) ≤
      E.costRF (fun τ => κ * τ ^ 2 / 2) b := by
  set Eg := ∑ s, E.π s * E.g s
  set b' := E.R * (E.g₀ + E.b₀ - Eg) / (1 + E.R)
  have hR := E.hR
  have hβ : E.β = 1 / E.R := by field_simp; linarith
  -- second moment of tomorrow's taxes as a function of `b`
  have hsum : ∀ x : ℝ, ∑ s, E.π s * (E.g s + x) ^ 2 =
      ∑ s, E.π s * E.g s ^ 2 + 2 * x * Eg + x ^ 2 := by
    intro x
    have : ∀ s, E.π s * (E.g s + x) ^ 2 = E.π s * E.g s ^ 2 + 2 * x * (E.π s * E.g s) +
        x ^ 2 * E.π s := fun s => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, E.hπ1, Eg]
    ring
  have key : ∀ x, E.costRF (fun τ => κ * τ ^ 2 / 2) x = κ / 2 * ((E.g₀ + E.b₀ - x / E.R) ^ 2 +
      E.β * (∑ s, E.π s * E.g s ^ 2 + 2 * x * Eg + x ^ 2)) := by
    intro x
    simp only [costRF, tax₀RF, taxRF]
    rw [← hsum x]
    have e : ∑ s, E.π s * (κ * (E.g s + x) ^ 2 / 2) = κ / 2 * ∑ s, E.π s * (E.g s + x) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [e]; ring
  rw [key, key, hβ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- the difference is `(1 + R)/R² · (b − b')²`
  have hA : E.g₀ + E.b₀ = Eg + b' * (1 + E.R) / E.R := by
    simp only [b']; field_simp; ring
  clear_value b' Eg
  have : ((E.g₀ + E.b₀ - b / E.R) ^ 2 + 1 / E.R * (∑ s, E.π s * E.g s ^ 2 + 2 * b * Eg + b ^ 2)) -
      ((E.g₀ + E.b₀ - b' / E.R) ^ 2 + 1 / E.R * (∑ s, E.π s * E.g s ^ 2 + 2 * b' * Eg + b' ^ 2)) =
      (1 + E.R) / E.R ^ 2 * (b - b') ^ 2 := by
    have hRinv : E.R * E.R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
    linear_combination (-2 * (b - b') / E.R) * hA + (b' ^ 2 - b ^ 2) * E.R⁻¹ * hRinv
  have h2 : 0 ≤ (1 + E.R) / E.R ^ 2 * (b - b') ^ 2 := by positivity
  linarith

end Env
end AMSS
end Econ

end
