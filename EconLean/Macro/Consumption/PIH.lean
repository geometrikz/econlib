/-
# The permanent income hypothesis: Euler equation and Hall's martingale

Hall (1978); Ljungqvist–Sargent ch. 17; Deaton, *Understanding Consumption*, ch. 3;
Romer, *Advanced Macroeconomics*, ch. 8.

**Setup.** Uncertainty is an event tree. A node is the history of shocks so far,
written as a list `h : List S` with the newest shock first, so the children of
`h` are `s :: h` and the date of `h` is its length. At node `h` the next shock
is `s` with probability `π h s`; `prob h` is the probability of reaching `h`.
The consumer has income `y h`, starts with assets `a₀`, earns gross return `R`
and lives for dates `0, …, N`. A plan is consumption `c` and assets `a` with
(`Feasible`)

* `a [] = a₀`,
* `a (s :: h) = R (a h + y h − c h)` at every non-terminal node,
* `c h ≤ a h + y h` at every terminal node (no debt at death).

Lifetime utility is `Σ_{t ≤ N} β^t Σ_{h of length t} prob h · u(c h)`.

**Results.**
* `euler`: at every non-terminal node reached with positive probability, an
  optimal plan satisfies `u'(c_t) = β R E_t[u'(c_{t+1})]`.
* `isOptimal_of_euler`: conversely, with concave `u`, a feasible plan that
  satisfies the Euler equation at every non-terminal node, consumes all wealth
  at the end, and has non-negative terminal marginal utility is optimal.
* `hall`: **Hall's random walk.** With quadratic utility (linear `u'`) and
  `β R = 1`, optimal consumption is a martingale: `c_t = E_t[c_{t+1}]`.

**Deviations.** Finite horizon and finitely many shocks. The closed-form
permanent-income consumption function is not stated; the results are the Euler
equation and Hall's martingale property. `u` is
differentiable on all of `ℝ` (as quadratic utility is); consumption is not
constrained to be non-negative, as in the linear–quadratic PIH.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

noncomputable section

namespace Econ
namespace PIH

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Histories of length `t` (nodes at date `t`). -/
def layer : ℕ → Finset (List S)
  | 0 => {[]}
  | t + 1 => (layer t).biUnion fun h => univ.image (· :: h)

theorem mem_layer {t : ℕ} {h : List S} : h ∈ layer t ↔ h.length = t := by
  induction t generalizing h with
  | zero => simp [layer]
  | succ t ih =>
    cases h with
    | nil => simp [layer]
    | cons s h => simp [layer, ih]

theorem sum_layer_succ {M : Type*} [AddCommMonoid M] (t : ℕ) (f : List S → M) :
    ∑ x ∈ layer (t + 1), f x = ∑ h ∈ layer t, ∑ s, f (s :: h) := by
  rw [layer, sum_biUnion]
  · exact sum_congr rfl fun h _ => sum_image fun s _ s' _ e => (List.cons.inj e).1
  · intro h _ h' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_image, mem_univ, true_and] at hx hx'
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨s', e⟩ := hx'
    exact hne (List.cons.inj e).2.symm

/-- The consumption–saving problem on an event tree. -/
structure Problem (S : Type*) [Fintype S] where
  /-- Last date. -/
  N : ℕ
  β : ℝ
  R : ℝ
  a₀ : ℝ
  /-- Transition probabilities at each node. -/
  π : List S → S → ℝ
  hπ : ∀ h s, 0 ≤ π h s
  sum_π : ∀ h, ∑ s, π h s = 1
  /-- Income at each node. -/
  y : List S → ℝ
  u : ℝ → ℝ
  u' : ℝ → ℝ
  deriv : ∀ c, HasDerivAt u (u' c) c
  hβ : 0 < β

namespace Problem

variable (P : Problem S)

/-- Probability of reaching a node. -/
def prob : List S → ℝ
  | [] => 1
  | s :: h => prob h * P.π h s

omit [DecidableEq S] in
theorem prob_nonneg : ∀ h : List S, 0 ≤ P.prob h
  | [] => zero_le_one
  | s :: h => mul_nonneg (prob_nonneg h) (P.hπ h s)

/-- Feasible plans: the budget constraint at every node and no terminal debt. -/
def Feasible (c a : List S → ℝ) : Prop :=
  a [] = P.a₀ ∧ (∀ h : List S, h.length < P.N → ∀ s, a (s :: h) = P.R * (a h + P.y h - c h)) ∧
    ∀ h : List S, h.length = P.N → c h ≤ a h + P.y h

/-- Expected discounted utility. -/
def U (c : List S → ℝ) : ℝ :=
  ∑ t ∈ range (P.N + 1), ∑ h ∈ layer t, P.β ^ t * P.prob h * P.u (c h)

/-- Optimal plans. -/
def IsOptimal (c a : List S → ℝ) : Prop :=
  P.Feasible c a ∧ ∀ c' a', P.Feasible c' a' → P.U c' ≤ P.U c

/-! ### Necessity of the Euler equation -/

section Euler

variable {P} {c a : List S → ℝ} (h₀ : List S)

/-- Indicator of being a child of `h₀`. -/
def child (h : List S) : Prop := h ≠ [] ∧ h.tail = h₀

instance (h : List S) : Decidable (child h₀ h) := inferInstanceAs (Decidable (_ ∧ _))

omit [Fintype S] [DecidableEq S] in
theorem child_cons (s : S) (h : List S) : child h₀ (s :: h) ↔ h = h₀ := by simp [child]

/-- Direction of the perturbation in consumption: `−1` at `h₀`, `+R` at each child. -/
def dc (R : ℝ) (h : List S) : ℝ := (if child h₀ h then R else 0) - if h = h₀ then 1 else 0

/-- Direction of the perturbation in assets: `+R` at each child. -/
def da (R : ℝ) (h : List S) : ℝ := if child h₀ h then R else 0

omit [Fintype S] [DecidableEq S] in
theorem not_child_self : ¬ child h₀ h₀ := fun ⟨hne, ht⟩ => by
  have := congrArg List.length ht
  rw [List.length_tail] at this
  have : 0 < h₀.length := List.length_pos_iff.2 hne
  omega

theorem feasible_perturb (hf : P.Feasible c a) (hlen : h₀.length < P.N) (ε : ℝ) :
    P.Feasible (fun h => c h + ε * dc h₀ P.R h) (fun h => a h + ε * da h₀ P.R h) := by
  refine ⟨by simp [da, child, hf.1], fun h hh s => ?_, fun h hh => ?_⟩
  · simp only
    rw [hf.2.1 h hh s]
    simp only [da, dc, child_cons]
    by_cases e : h = h₀
    · subst e; simp [not_child_self]; ring
    · simp only [e, ite_false, mul_zero, add_zero, sub_zero]
      split_ifs <;> ring
  · have hne : h ≠ h₀ := by rintro rfl; omega
    have := hf.2.2 h hh
    simp only [dc, da, hne, ite_false, sub_zero]
    linarith

theorem sum_child (t : ℕ) (F : List S → ℝ) :
    ∑ h ∈ layer t, (if child h₀ h then F h else 0) =
      if t = h₀.length + 1 then ∑ s, F (s :: h₀) else 0 := by
  cases t with
  | zero => simp [layer, child]
  | succ t =>
    rw [sum_layer_succ]
    simp only [child_cons, Nat.add_right_cancel_iff]
    rw [sum_congr rfl fun h _ => (sum_ite_irrel ..)]
    simp only [sum_const_zero]
    rw [sum_ite_eq' (layer t) h₀ (fun h => ∑ s, F (s :: h))]
    simp only [mem_layer, eq_comm]

theorem sum_self (t : ℕ) (F : List S → ℝ) :
    ∑ h ∈ layer t, (if h = h₀ then F h else 0) = if t = h₀.length then F h₀ else 0 := by
  rw [sum_ite_eq' (layer t) h₀ F]
  simp only [mem_layer, eq_comm]

/-- **Euler equation.** At every non-terminal node reached with positive
probability, an optimal plan satisfies `u'(c_t) = β R E_t[u'(c_{t+1})]`. -/
theorem euler (hopt : P.IsOptimal c a) (hlen : h₀.length < P.N) (hP : 0 < P.prob h₀) :
    P.u' (c h₀) = P.β * P.R * ∑ s, P.π h₀ s * P.u' (c (s :: h₀)) := by
  set g : ℝ → ℝ := fun ε => P.U fun h => c h + ε * dc h₀ P.R h
  have hg0 : g 0 = P.U c := by simp [g]
  have hmax : IsLocalMax g 0 := Filter.Eventually.of_forall fun ε => by
    rw [hg0]; exact hopt.2 _ _ (feasible_perturb h₀ hopt.1 hlen ε)
  set D := ∑ t ∈ range (P.N + 1), ∑ h ∈ layer t,
    P.β ^ t * P.prob h * (P.u' (c h) * dc h₀ P.R h)
  have hd : HasDerivAt g D 0 := by
    apply HasDerivAt.fun_sum; intro t _
    apply HasDerivAt.fun_sum; intro h _
    apply HasDerivAt.const_mul
    have hin : HasDerivAt (fun ε => c h + ε * dc h₀ P.R h) (dc h₀ P.R h) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (dc h₀ P.R h)).const_add (c h)
    exact HasDerivAt.comp_of_eq 0 (P.deriv (c h)) hin (by simp)
  have hD : D = 0 := hmax.hasDerivAt_eq_zero hd
  -- evaluate `D`
  have e1 : ∀ t h, P.β ^ t * P.prob h * (P.u' (c h) * dc h₀ P.R h) =
      (if child h₀ h then P.R * (P.β ^ t * P.prob h * P.u' (c h)) else 0) -
        if h = h₀ then P.β ^ t * P.prob h * P.u' (c h) else 0 := fun t h => by
    simp only [dc]; split_ifs <;> ring
  simp only [D, e1, sum_sub_distrib, sum_child, sum_self] at hD
  rw [sum_ite_eq' (range (P.N + 1)), sum_ite_eq'] at hD
  simp only [mem_range, show h₀.length + 1 < P.N + 1 by omega, show h₀.length < P.N + 1 by omega,
    ite_true, prob, pow_succ] at hD
  have hpos : 0 < P.β ^ h₀.length * P.prob h₀ := mul_pos (pow_pos P.hβ _) hP
  have : P.β ^ h₀.length * P.prob h₀ *
      (P.β * P.R * ∑ s, P.π h₀ s * P.u' (c (s :: h₀)) - P.u' (c h₀)) = 0 := by
    rw [← hD, mul_sub, mul_sum, mul_sum]
    congr 1
    exact sum_congr rfl fun s _ => by ring
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hpos.ne'
  · linarith

end Euler

/-! ### Sufficiency -/

omit [DecidableEq S] in
/-- Tangent-line bound from `u'` antitone. -/
theorem u_le_tangent (hanti : Antitone P.u') (x c : ℝ) : P.u x ≤ P.u c + P.u' c * (x - c) := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope P.u P.u' hlt
      (fun z _ => (P.deriv z).continuousAt.continuousWithinAt) (fun z _ => P.deriv z)
    have := hanti hξ.2.le
    rw [eq_div_iff (by linarith)] at hd
    nlinarith
  · rw [heq]; simp
  · obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope P.u P.u' hgt
      (fun z _ => (P.deriv z).continuousAt.continuousWithinAt) (fun z _ => P.deriv z)
    have := hanti hξ.1.le
    rw [eq_div_iff (by linarith)] at hd
    nlinarith

/-- **Sufficiency.** With concave utility (`u'` antitone), a feasible plan that
satisfies the Euler equation at every non-terminal node, consumes all wealth at
the terminal date, and has non-negative terminal marginal utility is optimal. -/
theorem isOptimal_of_euler (hanti : Antitone P.u') {c a : List S → ℝ} (hf : P.Feasible c a)
    (he : ∀ h : List S, h.length < P.N →
      P.u' (c h) = P.β * P.R * ∑ s, P.π h s * P.u' (c (s :: h)))
    (hterm : ∀ h : List S, h.length = P.N → c h = a h + P.y h ∧ 0 ≤ P.u' (c h)) :
    P.IsOptimal c a := by
  refine ⟨hf, fun c' a' hf' => ?_⟩
  set lam : List S → ℝ := fun h => P.β ^ h.length * P.prob h * P.u' (c h)
  set A : ℕ → ℝ := fun t => ∑ h ∈ layer t, lam h * (a' h - a h)
  -- step 1: concavity
  have h1 : P.U c' - P.U c ≤
      ∑ t ∈ range (P.N + 1), ∑ h ∈ layer t, lam h * (c' h - c h) := by
    simp only [U, ← sum_sub_distrib]
    refine sum_le_sum fun t _ => sum_le_sum fun h hh => ?_
    rw [mem_layer] at hh
    have := P.u_le_tangent hanti (c' h) (c h)
    have hw : 0 ≤ P.β ^ t * P.prob h := mul_nonneg (pow_pos P.hβ _).le (P.prob_nonneg h)
    simp only [lam, hh]
    nlinarith [mul_le_mul_of_nonneg_left this hw]
  -- step 2: interior layers telescope
  have h2 : ∀ t < P.N, ∑ h ∈ layer t, lam h * (c' h - c h) = A t - A (t + 1) := by
    intro t ht
    simp only [A]
    rw [sum_layer_succ, ← sum_sub_distrib]
    refine sum_congr rfl fun h hh => ?_
    rw [mem_layer] at hh
    have hl : h.length < P.N := hh ▸ ht
    have hb : ∀ s, a' (s :: h) - a (s :: h) = P.R * ((a' h - a h) - (c' h - c h)) := fun s => by
      rw [hf'.2.1 h hl s, hf.2.1 h hl s]; ring
    simp only [hb, lam, List.length_cons, prob, pow_succ]
    have := he h hl
    have : ∑ s, P.β ^ h.length * P.β * (P.prob h * P.π h s) * P.u' (c (s :: h)) *
        (P.R * (a' h - a h - (c' h - c h))) =
        P.β ^ h.length * P.prob h * (a' h - a h - (c' h - c h)) *
          (P.β * P.R * ∑ s, P.π h s * P.u' (c (s :: h))) := by
      rw [mul_sum, mul_sum]; exact sum_congr rfl fun s _ => by ring
    rw [this, ← he h hl]; ring
  -- step 3: terminal layer
  have h3 : ∑ h ∈ layer P.N, lam h * (c' h - c h) ≤ A P.N := by
    refine sum_le_sum fun h hh => ?_
    rw [mem_layer] at hh
    obtain ⟨hc, hu⟩ := hterm h hh
    have := hf'.2.2 h hh
    have hl : 0 ≤ lam h := mul_nonneg (mul_nonneg (pow_pos P.hβ _).le (P.prob_nonneg h)) hu
    exact mul_le_mul_of_nonneg_left (by linarith) hl
  have hA0 : A 0 = 0 := by simp [A, layer, hf.1, hf'.1]
  rw [sum_range_succ, sum_congr rfl fun t ht => h2 t (mem_range.1 ht), sum_range_sub'] at h1
  linarith

/-- **Hall (1978).** With quadratic utility (`u'(c) = κ − γ c`, `γ ≠ 0`) and
`β R = 1`, optimal consumption is a martingale: `c_t = E_t[c_{t+1}]` at every
non-terminal node reached with positive probability. -/
theorem hall {κ γ : ℝ} (hγ : γ ≠ 0) (hu : ∀ c, P.u' c = κ - γ * c) (hβR : P.β * P.R = 1)
    {c a : List S → ℝ} (hopt : P.IsOptimal c a) (h₀ : List S) (hlen : h₀.length < P.N)
    (hP : 0 < P.prob h₀) : c h₀ = ∑ s, P.π h₀ s * c (s :: h₀) := by
  have := euler h₀ hopt hlen hP
  simp only [hu, hβR, one_mul, mul_sub, sum_sub_distrib, ← sum_mul, P.sum_π, one_mul] at this
  have e : ∑ s, P.π h₀ s * (γ * c (s :: h₀)) = γ * ∑ s, P.π h₀ s * c (s :: h₀) := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [e] at this
  exact mul_left_cancel₀ hγ (by linarith)

end Problem

/-- **Non-vacuity.** Two periods, a fair coin, `β = R = 1`, `a₀ = 1`, income
`0` today and `±1` tomorrow, quadratic utility `u(c) = 10c − c²/2`. Consuming
`1/2` today and `1/2 ± 1` tomorrow is optimal (and is a martingale). -/
example : ∃ P : Problem Bool, P.N = 1 ∧ P.IsOptimal
    (fun h => match h with | [] => 1 / 2 | s :: _ => if s then 3 / 2 else -1 / 2)
    (fun h => match h with | [] => 1 | _ :: _ => 1 / 2) := by
  refine ⟨⟨1, 1, 1, 1, fun _ _ => 1 / 2, fun _ _ => by norm_num, fun _ => by norm_num,
    fun h => match h with | [] => 0 | s :: _ => if s then 1 else -1,
    fun c => 10 * c - c ^ 2 / 2, fun c => 10 - c, fun c => ?_, one_pos⟩, rfl, ?_⟩
  · have := ((hasDerivAt_id' c).const_mul 10).sub ((hasDerivAt_pow 2 c).div_const 2)
    convert this using 1
    norm_num
  · refine Problem.isOptimal_of_euler _ (fun x y hxy => by simp only; linarith)
      ⟨rfl, fun h hh s => ?_, fun h hh => ?_⟩ (fun h hh => ?_) fun h hh => ?_
    · match h with
      | [] => cases s <;> norm_num
      | _ :: _ => simp at hh
    · match h with
      | [] => simp at hh
      | s :: [] => cases s <;> norm_num
      | _ :: _ :: _ => simp at hh
    · match h with
      | [] => norm_num
      | _ :: _ => simp at hh
    · match h with
      | [] => simp at hh
      | s :: [] => cases s <;> norm_num
      | _ :: _ :: _ => simp at hh

end PIH
end Econ

end
