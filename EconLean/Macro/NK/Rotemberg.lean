/-
# The New Keynesian Phillips curve from Rotemberg adjustment costs

Rotemberg (1982), "Sticky Prices in the United States", JPE; Woodford,
*Interest and Prices*, ch. 3; Galí, *Monetary Policy, Inflation, and the
Business Cycle*, ch. 3.

**Setting** (log-linear, perfect foresight, finite horizon `T`). A firm
chooses its log price path `q`, starting from a given `q 0`, to minimize the
quadratic loss
`Σ_{s<T} β^{s+1} [(q_{s+1} − p_{s+1} − mc_{s+1})² + c (q_{s+1} − q_s)²]`
(`loss`): the first term is the profit loss from deviating from the
frictionless optimal price `p + mc` (the aggregate price level plus real
marginal cost), the second the quadratic cost of changing prices, `c > 0`.

**Results.**
* `foc`: if `q` is optimal against changes of a single interior price
  `q_n` (`0 < n < T`), then
  `(q_n − p_n − mc_n) + c (q_n − q_{n−1}) − β c (q_{n+1} − q_n) = 0`.
  This is **derived** by differentiating the loss, not assumed.
* `nkpc`: in a symmetric equilibrium (`q = p`), inflation satisfies the New
  Keynesian Phillips curve `π_n = β π_{n+1} + (1/c) mc_n` at each interior
  date where the equilibrium condition holds (one date per application).
* `isLocalMin_of_foc`: the first-order condition is also sufficient
  (convexity along each coordinate).
* `calvo_equiv`, `calvo_bridge`: the Rotemberg slope `1/c` equals the Calvo
  slope `(1 − θ)(1 − βθ)/θ` exactly when `c = θ/((1 − θ)(1 − βθ))`, and then
  the Rotemberg equilibrium condition is exactly the Calvo NKPC of
  `Econ.Calvo.nkpc`: the two models share the same Phillips curve to first
  order (they still differ in price dispersion, welfare and higher-order
  terms).
* `steady_inflation`, `optimal_exists`: non-vacuity: steady inflation
  `p_n = n πs` with `mc = c (1 − β) πs` is an equilibrium at every interior
  date; with `mc ≡ 0` a constant price path is optimal.

**Deviations.** The quadratic (linear–quadratic approximation) loss is
taken as the model; perfect foresight; finite horizon (only interior dates
are treated; the terminal-date condition, which has no forward term, is not
formalized).
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace Rotemberg

open Finset

/-- The firm's discounted quadratic loss over `T` periods. -/
def loss (β c : ℝ) (T : ℕ) (p mc q : ℕ → ℝ) : ℝ :=
  ∑ s ∈ range T, β ^ (s + 1) * ((q (s + 1) - p (s + 1) - mc (s + 1)) ^ 2 +
    c * (q (s + 1) - q s) ^ 2)

theorem hasDerivAt_update (q : ℕ → ℝ) (n k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => Function.update q n y k) (if k = n then 1 else 0) x := by
  by_cases h : k = n
  · subst h; simp only [Function.update_self, ite_true]; exact hasDerivAt_id x
  · simp only [Function.update_of_ne h, h, ite_false]; exact hasDerivAt_const x _

/-- The derivative of the loss in a single interior price `q_{m+1} = x`. -/
theorem hasDerivAt_loss {β c : ℝ} {T : ℕ} {p mc q : ℕ → ℝ} {m : ℕ} (hm : m + 2 ≤ T) (x : ℝ) :
    HasDerivAt (fun y => loss β c T p mc (Function.update q (m + 1) y))
      (2 * β ^ (m + 1) * ((x - p (m + 1) - mc (m + 1)) + c * (x - q m) -
        β * c * (q (m + 2) - x))) x := by
  set n := m + 1
  set u := Function.update q n x
  set d : ℕ → ℝ := fun k => if k = n then 1 else 0
  have hterm : ∀ s, HasDerivAt (fun y => β ^ (s + 1) *
      ((Function.update q n y (s + 1) - p (s + 1) - mc (s + 1)) ^ 2 +
        c * (Function.update q n y (s + 1) - Function.update q n y s) ^ 2))
      (β ^ (s + 1) * (2 * (u (s + 1) - p (s + 1) - mc (s + 1)) * d (s + 1) +
        c * (2 * (u (s + 1) - u s) * (d (s + 1) - d s)))) x := by
    intro s
    have h1 := hasDerivAt_update q n (s + 1) x
    have h0 := hasDerivAt_update q n s x
    have hA := ((h1.sub_const (p (s + 1))).sub_const (mc (s + 1))).pow 2
    have hB := ((h1.sub h0).pow 2).const_mul c
    have := (hA.add hB).const_mul (β ^ (s + 1))
    convert this using 1
    simp only [Pi.sub_apply, d, u]
    push_cast
    ring
  have hD := HasDerivAt.fun_sum (u := range T) (fun s _ => hterm s)
  convert hD using 1
  · funext y; simp [loss]
  rw [Finset.sum_eq_add m (m + 1) (by omega)]
  · have e1 : u (m + 1) = x := Function.update_self _ _ _
    have e2 : u m = q m := Function.update_of_ne (by omega) _ _
    have e3 : u (m + 1 + 1) = q (m + 2) := Function.update_of_ne (by omega) _ _
    simp only [d, n, show m + 1 + 1 = m + 2 by ring, ite_true, show ¬ m + 2 = m + 1 by omega,
      show ¬ m = m + 1 by omega, ite_false]
    rw [show m + 1 + 1 = m + 2 by ring] at e3
    rw [e1, e2, e3, pow_succ β (m + 1)]
    ring
  · intro s _ hs
    simp only [d, n, show ¬ s + 1 = m + 1 by omega, show ¬ s = m + 1 by omega, ite_false]
    ring
  · intro h; exact absurd (mem_range.2 (by omega)) h
  · intro h; exact absurd (mem_range.2 (by omega)) h

/-- **The firm's first-order condition** at an interior date `n = m + 1`. -/
theorem foc {β c : ℝ} (hβ : 0 < β) {T : ℕ} {p mc q : ℕ → ℝ} {m : ℕ} (hm : m + 2 ≤ T)
    (hmin : IsLocalMin (fun x => loss β c T p mc (Function.update q (m + 1) x)) (q (m + 1))) :
    (q (m + 1) - p (m + 1) - mc (m + 1)) + c * (q (m + 1) - q m) -
      β * c * (q (m + 2) - q (m + 1)) = 0 := by
  have hz := hmin.hasDerivAt_eq_zero (hasDerivAt_loss (p := p) (mc := mc) (q := q) hm (q (m + 1)))
  have hβ' : 0 < 2 * β ^ (m + 1) := by positivity
  exact (mul_eq_zero.1 hz).resolve_left hβ'.ne'

/-- **The first-order condition is also sufficient** (the loss is convex in
each price when `c ≥ 0`, `β > 0`): it makes `q_{m+1}` a global, hence local,
minimizer along its coordinate. -/
theorem isLocalMin_of_foc {β c : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) {T : ℕ} {p mc q : ℕ → ℝ}
    {m : ℕ} (hm : m + 2 ≤ T)
    (h : (q (m + 1) - p (m + 1) - mc (m + 1)) + c * (q (m + 1) - q m) -
      β * c * (q (m + 2) - q (m + 1)) = 0) :
    IsLocalMin (fun x => loss β c T p mc (Function.update q (m + 1) x)) (q (m + 1)) := by
  set f := fun x => loss β c T p mc (Function.update q (m + 1) x)
  set D := fun x => 2 * β ^ (m + 1) * ((x - p (m + 1) - mc (m + 1)) + c * (x - q m) -
    β * c * (q (m + 2) - x))
  set x₀ := q (m + 1)
  have hf : ∀ x, HasDerivAt f (D x) x := fun x => hasDerivAt_loss hm x
  -- `D x = 2 β^{m+1} (1 + c + β c) (x − x₀)`
  have hDx : ∀ x, D x = 2 * β ^ (m + 1) * (1 + c + β * c) * (x - x₀) := by
    intro x; simp only [D]; linear_combination (2 * β ^ (m + 1)) * h
  have hk : 0 < 2 * β ^ (m + 1) * (1 + c + β * c) := by
    have : 0 ≤ β * c := mul_nonneg hβ.le hc
    have : 0 < 2 * β ^ (m + 1) := by positivity
    nlinarith
  refine Filter.Eventually.of_forall fun x => ?_
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope f D hlt
      (fun y _ => (hf y).continuousAt.continuousWithinAt) (fun y _ => hf y)
    have hneg : D ξ < 0 := by rw [hDx]; exact mul_neg_of_pos_of_neg hk (by linarith [hξ.2])
    rw [hd, div_lt_iff₀ (by linarith)] at hneg
    simp only [f] at hneg ⊢
    linarith
  · rw [heq]
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope f D hgt
      (fun y _ => (hf y).continuousAt.continuousWithinAt) (fun y _ => hf y)
    have hpos : 0 < D ξ := by rw [hDx]; exact mul_pos hk (by linarith [hξ.1])
    rw [hd, lt_div_iff₀ (by linarith)] at hpos
    simp only [f] at hpos ⊢
    linarith

/-- **The Rotemberg New Keynesian Phillips curve.** In a symmetric
equilibrium (`q = p`, each firm optimal), at every interior date
`π_n = β π_{n+1} + (1/c) mc_n`. -/
theorem nkpc {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {T : ℕ} {p mc : ℕ → ℝ} {m : ℕ}
    (hm : m + 2 ≤ T)
    (hmin : IsLocalMin (fun x => loss β c T p mc (Function.update p (m + 1) x)) (p (m + 1))) :
    p (m + 1) - p m = β * (p (m + 2) - p (m + 1)) + 1 / c * mc (m + 1) := by
  have h := foc hβ hm hmin
  field_simp
  linarith

/-- **Rotemberg–Calvo equivalence** of the Phillips-curve slopes. -/
theorem calvo_equiv {β θ c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hc : 0 < c) :
    1 / c = (1 - θ) * (1 - β * θ) / θ ↔ c = θ / ((1 - θ) * (1 - β * θ)) := by
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 1 - β * θ := by nlinarith
  have hp : 0 < (1 - θ) * (1 - β * θ) := mul_pos h1 h2
  constructor
  · intro h
    rw [eq_div_iff hp.ne']
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-- **Rotemberg–Calvo bridge.** With `c = θ/((1 − θ)(1 − βθ))`, the
Rotemberg equilibrium condition at an interior date is exactly the Calvo
Phillips curve of `Econ.Calvo.nkpc`. -/
theorem calvo_bridge {β θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    {T : ℕ} {p mc : ℕ → ℝ} {m : ℕ} (hm : m + 2 ≤ T)
    (hmin : IsLocalMin (fun x => loss β (θ / ((1 - θ) * (1 - β * θ))) T p mc
      (Function.update p (m + 1) x)) (p (m + 1))) :
    p (m + 1) - p m = β * (p (m + 2) - p (m + 1)) + (1 - θ) * (1 - β * θ) / θ * mc (m + 1) := by
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 1 - β * θ := by nlinarith
  have hc : 0 < θ / ((1 - θ) * (1 - β * θ)) := by positivity
  rw [nkpc hβ hc hm hmin, (calvo_equiv hβ hβ1 hθ hθ1 hc).2 rfl]

/-- **A non-trivial witness**: steady inflation `p_n = n πs` with constant
marginal-cost gap `mc = c (1 − β) πs` is a symmetric equilibrium at every
interior date. -/
theorem steady_inflation {β c : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) (T : ℕ) (πs : ℝ) {m : ℕ}
    (hm : m + 2 ≤ T) :
    IsLocalMin (fun x => loss β c T (fun n => n * πs) (fun _ => c * (1 - β) * πs)
      (Function.update (fun n : ℕ => n * πs) (m + 1) x)) ((m + 1 : ℕ) * πs) := by
  apply isLocalMin_of_foc (p := fun n : ℕ => n * πs) hβ hc hm
  push_cast
  ring

/-- **Non-vacuity**: with zero marginal-cost gaps and a constant price level
equal to the initial price, the constant price path minimizes the loss
(against every path, in particular every path from the same initial price);
its loss is zero. -/
theorem optimal_exists {β c : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) (T : ℕ) (p₀ : ℝ) (q : ℕ → ℝ) :
    loss β c T (fun _ => p₀) (fun _ => 0) (fun _ => p₀) ≤ loss β c T (fun _ => p₀) (fun _ => 0) q := by
  simp only [loss, sub_self, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero]
  simp only [Finset.sum_const_zero]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (pow_pos hβ _).le
    (add_nonneg (sq_nonneg _) (mul_nonneg hc (sq_nonneg _)))

end Rotemberg
end Econ

end
