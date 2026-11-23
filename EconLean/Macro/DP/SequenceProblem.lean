/-
# The sequence problem, verification theorems, and Euler + transversality

Stokey–Lucas (SL), *Recursive Methods in Economic Dynamics*, §4.1 (Thms 4.3,
4.4) and §4.5 (Thm 4.15).

**The economics.** A deterministic dynamic program in *sequence form* is

  `sup Σ_{t=0}^∞ β^t F(x_t, x_{t+1})`  over plans with `x_{t+1} ∈ Γ(x_t)`, `x_0` given.

Here `x_t` is the state (e.g. capital), `Γ` the feasibility correspondence,
`F` the one-period return, and `β` the discount factor. This file works with
the problem directly, without any topology, so it covers unbounded returns
such as log utility in the Brock–Mirman growth model.

**Avoiding junk values.** In Lean, `∑'` of a non-summable series is `0` and
`sSup` of an unbounded set of reals is `0`. With unbounded returns a plan's
discounted sum may diverge to `-∞`. So we never take an infinite sum here:
the payoff of a plan is described through its *partial sums*
`u_n = Σ_{t<n} β^t F(x_t, x_{t+1})`, and "`w` is the optimal value" is stated
as (i) some feasible plan has `u_n → w`, and (ii) every feasible plan has
`limsup u_n ≤ w`, written `∀ ε > 0, eventually u_n ≤ w + ε`. This is exactly
SL's `v*(x₀) = max_{x ∈ Π(x₀)} lim u_n(x)` with payoffs in `[-∞, ∞)`, with the
max attained.

**Contents.**
* `verification` (SL Thm 4.3 + 4.4): a function `v` satisfying the Bellman
  inequality, with a policy attaining it, plus SL's boundary condition, *is*
  the value of the sequence problem, and the policy generates an optimal plan.
* `verification_of_lowerBound`: the same with the boundary condition replaced
  by a lower bound `v ≥ a + b F` (`b ≥ 1`). SL's boundary condition fails for
  log utility (feasible plans can drive capital to `0` arbitrarily fast), and
  this variant is what verifies the Brock–Mirman closed form.
* `euler_transversality` (SL Thm 4.15): with concave returns, a plan satisfying
  the Euler equations and the transversality condition is optimal.
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

namespace Econ

open Filter Topology Finset

variable {X : Type*}

/-! ### Plans and payoffs -/

/-- A **feasible plan** from `x₀` (SL's `Π(x₀)`): a sequence of states starting
at `x₀` with `x_{t+1} ∈ Γ(x_t)` for every `t`. -/
def IsFeasiblePlan (Γ : X → Set X) (x₀ : X) (x : ℕ → X) : Prop :=
  x 0 = x₀ ∧ ∀ t, x (t + 1) ∈ Γ (x t)

/-- The **partial payoff** `u_n(x) = Σ_{t<n} β^t F(x_t, x_{t+1})` of a plan. -/
def partialPayoff (F : X → X → ℝ) (β : ℝ) (x : ℕ → X) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, β ^ t * F (x t) (x (t + 1))

/-- **`w` is the optimal value of the sequence problem at `x₀`, and it is
attained**: some feasible plan's payoffs converge to `w`, and every feasible
plan has `limsup_n u_n ≤ w`. Note this *requires attainment*: if the supremum
is not attained by any plan, no `w` satisfies it. When it holds, `w` is unique
(`IsOptimalValue.unique`). -/
def IsOptimalValue (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (x₀ : X) (w : ℝ) : Prop :=
  (∃ x, IsFeasiblePlan Γ x₀ x ∧ Tendsto (partialPayoff F β x) atTop (𝓝 w)) ∧
  ∀ x, IsFeasiblePlan Γ x₀ x → ∀ ε > 0, ∀ᶠ n in atTop, partialPayoff F β x n ≤ w + ε

/-- A feasible plan `x` is **optimal** from `x₀` if no feasible plan does better
in the limit: for every feasible `x'`, `limsup_n (u_n(x') - u_n(x)) ≤ 0`
(SL's criterion in Thm 4.15). -/
def IsOptimalPlan (Γ : X → Set X) (F : X → X → ℝ) (β : ℝ) (x₀ : X) (x : ℕ → X) : Prop :=
  IsFeasiblePlan Γ x₀ x ∧ ∀ x', IsFeasiblePlan Γ x₀ x' → ∀ ε > 0,
    ∀ᶠ n in atTop, partialPayoff F β x' n ≤ partialPayoff F β x n + ε

/-- The optimal value, when it exists (and is attained), is unique. -/
theorem IsOptimalValue.unique {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} {x₀ : X} {w w' : ℝ}
    (hw : IsOptimalValue Γ F β x₀ w) (hw' : IsOptimalValue Γ F β x₀ w') : w = w' := by
  have key : ∀ {w w' : ℝ}, IsOptimalValue Γ F β x₀ w → IsOptimalValue Γ F β x₀ w' → w ≤ w' := by
    intro w w' hw hw'
    obtain ⟨x, hx, hlim⟩ := hw.1
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact le_of_tendsto hlim (hw'.2 x hx ε hε)
  exact le_antisymm (key hw hw') (key hw' hw)

/-- The plan generated from `x₀` by a policy function `g`: `x_t = g^t(x₀)`. -/
def planOf (g : X → X) (x₀ : X) : ℕ → X := fun t => g^[t] x₀

theorem planOf_succ (g : X → X) (x₀ : X) (t : ℕ) :
    planOf g x₀ (t + 1) = g (planOf g x₀ t) :=
  Function.iterate_succ_apply' g t x₀

theorem isFeasiblePlan_planOf {Γ : X → Set X} {g : X → X} (hg : ∀ x, g x ∈ Γ x) (x₀ : X) :
    IsFeasiblePlan Γ x₀ (planOf g x₀) :=
  ⟨rfl, fun t => by rw [planOf_succ]; exact hg _⟩

/-- If the optimal value is attained, the attaining plan is an optimal plan. -/
theorem IsOptimalValue.isOptimalPlan {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} {x₀ : X}
    {w : ℝ} (hw : IsOptimalValue Γ F β x₀ w) {x : ℕ → X} (hx : IsFeasiblePlan Γ x₀ x)
    (hlim : Tendsto (partialPayoff F β x) atTop (𝓝 w)) : IsOptimalPlan Γ F β x₀ x := by
  refine ⟨hx, fun x' hx' ε hε => ?_⟩
  have h1 := hw.2 x' hx' (ε / 2) (by positivity)
  have h2 : ∀ᶠ n in atTop, w - ε / 2 < partialPayoff F β x n :=
    hlim.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h1, h2] with n a b
  linarith

/-- If `w` is the optimal value, every optimal plan's partial payoffs
converge to `w`. -/
theorem IsOptimalValue.tendsto_of_isOptimalPlan {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ}
    {x₀ : X} {w : ℝ} (hw : IsOptimalValue Γ F β x₀ w) {x : ℕ → X}
    (hx : IsOptimalPlan Γ F β x₀ x) : Tendsto (partialPayoff F β x) atTop (𝓝 w) := by
  obtain ⟨xs, hxs, hlim⟩ := hw.1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, h1⟩ := eventually_atTop.1 (hw.2 x hx.1 (ε / 2) (by positivity))
  obtain ⟨N₂, h2⟩ := eventually_atTop.1 (hx.2 xs hxs (ε / 3) (by positivity))
  obtain ⟨N₃, h3⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (by linarith : w - ε / 3 < w)))
  refine ⟨max N₁ (max N₂ N₃), fun n hn => ?_⟩
  have a := h1 n (le_of_max_le_left hn)
  have b := h2 n (le_of_max_le_left (le_of_max_le_right hn))
  have c := h3 n (le_of_max_le_right (le_of_max_le_right hn))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### The telescoping identity

The engine of every result below. For any `v : X → ℝ` and any plan, write the
**Bellman gap** at date `t` as `v(x_t) - F(x_t, x_{t+1}) - β v(x_{t+1})`
(nonnegative when `v` satisfies the Bellman inequality, zero along a policy).
Then
  `v(x₀) = u_n + β^n v(x_n) + Σ_{t<n} β^t · gap_t`. -/

theorem telescope (F : X → X → ℝ) (β : ℝ) (v : X → ℝ) (x : ℕ → X) (n : ℕ) :
    v (x 0) = partialPayoff F β x n + β ^ n * v (x n) +
      ∑ t ∈ range n, β ^ t * (v (x t) - F (x t) (x (t + 1)) - β * v (x (t + 1))) := by
  induction n with
  | zero => simp [partialPayoff]
  | succ n ih =>
    rw [ih, partialPayoff, partialPayoff, sum_range_succ, sum_range_succ, pow_succ]
    ring

/-- **Bellman inequality ⇒ upper bound on partial payoffs.** If
`F(x, y) + β v(y) ≤ v(x)` along a plan (and `β ≥ 0`), then
`u_n + β^n v(x_n) ≤ v(x₀)`. -/
theorem partialPayoff_add_le {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β) {v : X → ℝ} {x : ℕ → X}
    (h : ∀ t, F (x t) (x (t + 1)) + β * v (x (t + 1)) ≤ v (x t)) (n : ℕ) :
    partialPayoff F β x n + β ^ n * v (x n) ≤ v (x 0) := by
  rw [telescope F β v x n]
  have : 0 ≤ ∑ t ∈ range n, β ^ t * (v (x t) - F (x t) (x (t + 1)) - β * v (x (t + 1))) :=
    sum_nonneg fun t _ => mul_nonneg (pow_nonneg hβ t) (by linarith [h t])
  linarith

/-- **Bellman equality ⇒ exact partial payoffs.** Along a plan where
`F(x_t, x_{t+1}) + β v(x_{t+1}) = v(x_t)`, `u_n + β^n v(x_n) = v(x₀)`. -/
theorem partialPayoff_add_eq {F : X → X → ℝ} {β : ℝ} {v : X → ℝ} {x : ℕ → X}
    (h : ∀ t, F (x t) (x (t + 1)) + β * v (x (t + 1)) = v (x t)) (n : ℕ) :
    partialPayoff F β x n + β ^ n * v (x n) = v (x 0) := by
  rw [telescope F β v x n]
  have : ∑ t ∈ range n, β ^ t * (v (x t) - F (x t) (x (t + 1)) - β * v (x (t + 1))) = 0 :=
    sum_eq_zero fun t _ => by rw [← h t]; ring
  linarith

/-! ### Verification theorems (SL Thms 4.3–4.4) -/

/-- Feasible plans starting in an invariant set `S` stay in `S`. -/
theorem IsFeasiblePlan.mem {Γ : X → Set X} {S : Set X} (hS : ∀ x ∈ S, Γ x ⊆ S) {x₀ : X}
    (hx₀ : x₀ ∈ S) {x : ℕ → X} (hx : IsFeasiblePlan Γ x₀ x) : ∀ t, x t ∈ S := by
  intro t
  induction t with
  | zero => exact hx.1 ▸ hx₀
  | succ t ih => exact hS _ ih (hx.2 t)

/-- **Verification theorem** (SL Thm 4.3 with the attainment part of Thm 4.4).
State space `S` (invariant under `Γ`), `0 ≤ β`. Suppose `v : X → ℝ` and a
policy `g` satisfy
* the **Bellman inequality** `F(x, y) + β v(y) ≤ v(x)` for `y ∈ Γ(x)`;
* `g(x) ∈ Γ(x)` attains it: `F(x, g x) + β v(g x) = v(x)`;
* SL's **boundary condition**, in the weak form `liminf_n β^n v(x_n) ≥ 0`
  for every feasible plan (SL Thm 4.3 assume `lim β^n v(x_n) = 0`);
* along the plan generated by `g`, `limsup_n β^n v(x_n) ≤ 0` (SL Thm 4.4).

Then for every `x₀ ∈ S`, `v(x₀)` is the optimal value of the sequence problem,
and the plan generated by `g` attains it. -/
theorem verification {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ : 0 ≤ β) {S : Set X}
    (hS : ∀ x ∈ S, Γ x ⊆ S) {v : X → ℝ} {g : X → X}
    (hineq : ∀ x ∈ S, ∀ y ∈ Γ x, F x y + β * v y ≤ v x)
    (hg : ∀ x ∈ S, g x ∈ Γ x ∧ F x (g x) + β * v (g x) = v x)
    (hbound : ∀ x₀ ∈ S, ∀ x, IsFeasiblePlan Γ x₀ x →
      ∀ ε > 0, ∀ᶠ n in atTop, -ε ≤ β ^ n * v (x n))
    (hpol : ∀ x₀ ∈ S, ∀ ε > 0, ∀ᶠ n in atTop, β ^ n * v (planOf g x₀ n) ≤ ε)
    {x₀ : X} (hx₀ : x₀ ∈ S) :
    IsOptimalValue Γ F β x₀ (v x₀) ∧
      Tendsto (partialPayoff F β (planOf g x₀)) atTop (𝓝 (v x₀)) := by
  -- Upper bound for every feasible plan: `u_n ≤ v(x₀) - β^n v(x_n) ≤ v(x₀) + ε`.
  have hupper : ∀ x, IsFeasiblePlan Γ x₀ x → ∀ ε > 0, ∀ᶠ n in atTop,
      partialPayoff F β x n ≤ v x₀ + ε := by
    intro x hx ε hε
    have hmem := hx.mem hS hx₀
    filter_upwards [hbound x₀ hx₀ x hx ε hε] with n hn
    have := partialPayoff_add_le hβ (fun t => hineq _ (hmem t) _ (hx.2 t)) n
    rw [hx.1] at this
    linarith
  -- The plan generated by `g`. Note `g` maps `S` into `S`, so it is feasible
  -- from `x₀` and Bellman holds with equality along it.
  set xs := planOf g x₀ with hxs
  have hmemg : ∀ t, xs t ∈ S := by
    intro t
    induction t with
    | zero => exact hx₀
    | succ t ih => rw [hxs, planOf_succ]; exact hS _ ih (hg _ ih).1
  have hfeas : IsFeasiblePlan Γ x₀ xs :=
    ⟨rfl, fun t => by rw [hxs, planOf_succ]; exact (hg _ (hmemg t)).1⟩
  have heq : ∀ n, partialPayoff F β xs n + β ^ n * v (xs n) = v x₀ := fun n => by
    have := partialPayoff_add_eq (x := xs) (v := v)
      (fun t => by rw [hxs, planOf_succ]; exact (hg _ (hmemg t)).2) n
    simpa [hxs, planOf] using this
  -- Along the policy plan `u_n = v(x₀) - β^n v(x_n)`, squeezed by the upper
  -- bound and by `limsup β^n v(x_n) ≤ 0`.
  have hconv : Tendsto (partialPayoff F β xs) atTop (𝓝 (v x₀)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hupper xs hfeas (ε / 2) (by positivity))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hpol x₀ hx₀ (ε / 2) (by positivity))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have a := hN₁ n (le_of_max_le_left hn)
    have b := hN₂ n (le_of_max_le_right hn)
    have c := heq n
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith
  exact ⟨⟨⟨xs, hfeas, hconv⟩, hupper⟩, hconv⟩

/-- An auxiliary limit: if `s_{n+1} ≤ r s_n + d β^n` with `s ≥ 0`, `0 ≤ r < 1`,
`r < 1`, `0 ≤ β < 1`, `d ≥ 0`, then `s_n → 0`. -/
theorem tendsto_zero_of_le_mul_add_pow {s : ℕ → ℝ} {r d β : ℝ} (hs : ∀ n, 0 ≤ s n)
    (hr1 : r < 1) (hd : 0 ≤ d) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hrec : ∀ n, s (n + 1) ≤ r * s n + d * β ^ n) : Tendsto s atTop (𝓝 0) := by
  -- Dominate by `(s 0 + n d / q) q^n` with `q = max r β ½ ∈ (0, 1)`.
  set q := max (max r β) (1 / 2) with hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq1 : q < 1 := max_lt (max_lt hr1 hβ1) (by norm_num)
  have hrq : r ≤ q := (le_max_left _ _).trans (le_max_left _ _)
  have hβq : β ≤ q := (le_max_right _ _).trans (le_max_left _ _)
  have hbound : ∀ n : ℕ, s n ≤ (s 0 + n * (d / q)) * q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : r * s n ≤ q * ((s 0 + n * (d / q)) * q ^ n) :=
        mul_le_mul hrq ih (hs n) hq0.le
      have h2 : d * β ^ n ≤ d * q ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ0 hβq n) hd
      have h3 : (s 0 + ((n + 1 : ℕ) : ℝ) * (d / q)) * q ^ (n + 1) =
          q * ((s 0 + n * (d / q)) * q ^ n) + d * q ^ n := by
        push_cast; rw [pow_succ]; field_simp; ring
      rw [h3]; linarith [hrec n]
  have hlim : Tendsto (fun n : ℕ => (s 0 + n * (d / q)) * q ^ n) atTop (𝓝 0) := by
    have e1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul (s 0)
    have e2 := (tendsto_self_mul_const_pow_of_lt_one hq0.le hq1).const_mul (d / q)
    have := e1.add e2
    simp only [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    ring
  exact squeeze_zero hs hbound hlim

/-- **Verification theorem for returns unbounded below.**
Same as `verification`, but SL's boundary condition (which fails for log
utility) is replaced by a lower bound of `v` by the current return:
`a + b F(x, y) ≤ v(x)` for `y ∈ Γ(x)`, with `b ≥ 1`; and `0 ≤ β < 1`.
The policy plan must satisfy `limsup β^n v(x_n) ≤ 0` (SL Thm 4.4's condition).

Idea: if a plan does badly late on, its returns are very negative, which
offsets the small `v(x_n)` in the telescoping bound. -/
theorem verification_of_lowerBound {Γ : X → Set X} {F : X → X → ℝ} {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {S : Set X} (hS : ∀ x ∈ S, Γ x ⊆ S) {v : X → ℝ} {g : X → X}
    (hineq : ∀ x ∈ S, ∀ y ∈ Γ x, F x y + β * v y ≤ v x)
    (hg : ∀ x ∈ S, g x ∈ Γ x ∧ F x (g x) + β * v (g x) = v x)
    {a b : ℝ} (hb : 1 ≤ b) (hlow : ∀ x ∈ S, ∀ y ∈ Γ x, a + b * F x y ≤ v x)
    (hpol : ∀ x₀ ∈ S, ∀ ε > 0, ∀ᶠ n in atTop, β ^ n * v (planOf g x₀ n) ≤ ε)
    {x₀ : X} (hx₀ : x₀ ∈ S) :
    IsOptimalValue Γ F β x₀ (v x₀) ∧
      Tendsto (partialPayoff F β (planOf g x₀)) atTop (𝓝 (v x₀)) := by
  -- Upper bound for an arbitrary feasible plan.
  have hupper : ∀ x, IsFeasiblePlan Γ x₀ x → ∀ ε > 0, ∀ᶠ n in atTop,
      partialPayoff F β x n ≤ v x₀ + ε := by
    intro x hx ε hε
    have hmem := hx.mem hS hx₀
    set u := partialPayoff F β x
    -- `w_n = u_n - v(x₀)`; we show `max w_n 0 → 0`.
    set s : ℕ → ℝ := fun n => max (u n - v x₀) 0
    have hb0 : 0 < b := by linarith
    have hrec : ∀ n, s (n + 1) ≤ ((b - 1) / b) * s n + (|a| / b) * β ^ n := by
      intro n
      -- telescoping bound at date `n`
      have h1 := partialPayoff_add_le hβ0 (fun t => hineq _ (hmem t) _ (hx.2 t)) n
      rw [hx.1] at h1
      -- lower bound on `v(x_n)` via the date-`n` return, times `β^n ≥ 0`
      have h2 := mul_le_mul_of_nonneg_left (hlow _ (hmem n) _ (hx.2 n)) (pow_nonneg hβ0 n)
      -- `u_{n+1} = u_n + β^n F(x_n, x_{n+1})`
      have h3 : u (n + 1) = u n + β ^ n * F (x n) (x (n + 1)) := by
        simp only [u, partialPayoff, sum_range_succ]
      have hβn : 0 ≤ β ^ n := pow_nonneg hβ0 n
      have ha : -(|a| * β ^ n) ≤ a * β ^ n := by
        have := neg_abs_le a; nlinarith
      have hsn : u n - v x₀ ≤ s n := le_max_left _ _
      have hsn0 : 0 ≤ s n := le_max_right _ _
      -- `b w_{n+1} ≤ (b - 1) w_n - β^n a ≤ (b - 1) s_n + β^n |a|`
      have key : b * (u (n + 1) - v x₀) ≤ (b - 1) * s n + |a| * β ^ n := by
        have : (b - 1) * (u n - v x₀) ≤ (b - 1) * s n :=
          mul_le_mul_of_nonneg_left hsn (by linarith)
        nlinarith
      apply max_le
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hb0]
        linarith
      · have : 0 ≤ (b - 1) / b * s n := mul_nonneg (div_nonneg (by linarith) hb0.le) hsn0
        have : 0 ≤ |a| / b * β ^ n := mul_nonneg (div_nonneg (abs_nonneg a) hb0.le) hβn
        linarith
    have hlim : Tendsto s atTop (𝓝 0) :=
      tendsto_zero_of_le_mul_add_pow (fun n => le_max_right _ _)
        (by rw [div_lt_one hb0]; linarith)
        (div_nonneg (abs_nonneg a) hb0.le) hβ0 hβ1 hrec
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    have : u n - v x₀ ≤ s n := le_max_left _ _
    linarith
  -- The policy plan, exactly as in `verification`.
  set xs := planOf g x₀ with hxs
  have hmemg : ∀ t, xs t ∈ S := by
    intro t
    induction t with
    | zero => exact hx₀
    | succ t ih => rw [hxs, planOf_succ]; exact hS _ ih (hg _ ih).1
  have hfeas : IsFeasiblePlan Γ x₀ xs :=
    ⟨rfl, fun t => by rw [hxs, planOf_succ]; exact (hg _ (hmemg t)).1⟩
  have heq : ∀ n, partialPayoff F β xs n + β ^ n * v (xs n) = v x₀ := fun n => by
    have := partialPayoff_add_eq (x := xs) (v := v)
      (fun t => by rw [hxs, planOf_succ]; exact (hg _ (hmemg t)).2) n
    simpa [hxs, planOf] using this
  have hconv : Tendsto (partialPayoff F β xs) atTop (𝓝 (v x₀)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hupper xs hfeas (ε / 2) (by positivity))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hpol x₀ hx₀ (ε / 2) (by positivity))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have a := hN₁ n (le_of_max_le_left hn)
    have b := hN₂ n (le_of_max_le_right hn)
    have c := heq n
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith
  exact ⟨⟨⟨xs, hfeas, hconv⟩, hupper⟩, hconv⟩

/-! ### Euler equations and transversality (SL Thm 4.15) -/

section Euler

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]

/-- **Sufficiency of the Euler equations and the transversality condition**
(SL Thm 4.15). States live in an ordered real vector space `E` (SL: `ℝ^l`),
and feasible states are nonnegative. The return `F` has partial derivatives
`F_x(x, y)`, `F_y(x, y)` (linear functionals) and is concave in the sense of
the **supergradient inequality** on the graph of `Γ`:
  `F(x', y') ≤ F(x, y) + F_x(x, y)(x' - x) + F_y(x, y)(y' - y)`
(this is what concavity plus differentiability gives, and all SL's proof
uses). `F` is nondecreasing in the state: `F_x(x, y) z ≥ 0` for `z ≥ 0`.

If a feasible plan `x*` satisfies the **Euler equations**
`F_y(x*_t, x*_{t+1}) + β F_x(x*_{t+1}, x*_{t+2}) = 0` and the **transversality
condition** `β^t F_x(x*_t, x*_{t+1}) x*_t → 0`, then `x*` is optimal. -/
theorem euler_transversality {F : E → E → ℝ} {Γ : E → Set E} {β : ℝ}
    (hβ : 0 ≤ β) (Fx Fy : E → E → E →ₗ[ℝ] ℝ)
    (hconc : ∀ x y x' y', y ∈ Γ x → y' ∈ Γ x' →
      F x' y' ≤ F x y + Fx x y (x' - x) + Fy x y (y' - y))
    (hΓ : ∀ x y, y ∈ Γ x → 0 ≤ y)
    (hFx : ∀ x y z, y ∈ Γ x → 0 ≤ z → 0 ≤ Fx x y z)
    {x₀ : E} {xs : ℕ → E} (hxs : IsFeasiblePlan Γ x₀ xs)
    (heuler : ∀ t, Fy (xs t) (xs (t + 1)) + β • Fx (xs (t + 1)) (xs (t + 2)) = 0)
    (htvc : Tendsto (fun t => β ^ t * Fx (xs t) (xs (t + 1)) (xs t)) atTop (𝓝 0)) :
    IsOptimalPlan Γ F β x₀ xs := by
  refine ⟨hxs, fun x hx ε hε => ?_⟩
  -- Abbreviations: derivatives along the candidate plan, and the gap `z = x* - x`.
  set Dx : ℕ → E →ₗ[ℝ] ℝ := fun t => Fx (xs t) (xs (t + 1))
  set Dy : ℕ → E →ₗ[ℝ] ℝ := fun t => Fy (xs t) (xs (t + 1))
  set z : ℕ → E := fun t => xs t - x t
  have hz0 : z 0 = 0 := by simp [z, hx.1, hxs.1]
  -- Step 1 (concavity): each period's shortfall is bounded by the linear terms.
  have hstep : ∀ t, Dx t (z t) + Dy t (z (t + 1)) ≤
      F (xs t) (xs (t + 1)) - F (x t) (x (t + 1)) := by
    intro t
    have := hconc (xs t) (xs (t + 1)) (x t) (x (t + 1)) (hxs.2 t) (hx.2 t)
    have e1 : Fx (xs t) (xs (t + 1)) (x t - xs t) = - Dx t (z t) := by
      simp only [Dx, z, ← map_neg, neg_sub]
    have e2 : Fy (xs t) (xs (t + 1)) (x (t + 1) - xs (t + 1)) = - Dy t (z (t + 1)) := by
      simp only [Dy, z, ← map_neg, neg_sub]
    rw [e1, e2] at this
    linarith
  -- Step 2 (Euler): the linear terms telescope to `-β^n F_x z_n`.
  have htel : ∀ n, ∑ t ∈ range n, β ^ t * (Dx t (z t) + Dy t (z (t + 1))) =
      - (β ^ n * Dx n (z n)) := by
    intro n
    induction n with
    | zero => simp [hz0]
    | succ n ih =>
      rw [sum_range_succ, ih]
      have he := congrArg (fun L : E →ₗ[ℝ] ℝ => L (z (n + 1))) (heuler n)
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        smul_eq_mul] at he
      have : Dy n (z (n + 1)) = - (β * Dx (n + 1) (z (n + 1))) := by
        simp only [Dy, Dx]; linarith
      rw [this, pow_succ]; ring
  -- Step 3: so `u_n(x*) - u_n(x) ≥ -β^n F_x(x*_n)(x*_n - x_n) ≥ -β^n F_x(x*_n) x*_n`.
  have hdiff : ∀ n, 1 ≤ n → - (β ^ n * Dx n (xs n)) ≤
      partialPayoff F β xs n - partialPayoff F β x n := by
    intro n hn
    have hsum : - (β ^ n * Dx n (z n)) ≤
        partialPayoff F β xs n - partialPayoff F β x n := by
      rw [← htel n, partialPayoff, partialPayoff, ← sum_sub_distrib]
      exact sum_le_sum fun t _ => by
        rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (hstep t) (pow_nonneg hβ t)
    -- `x_n ≥ 0` for `n ≥ 1` (feasible states are nonnegative) and `F_x ≥ 0`.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hxn : 0 ≤ Dx (m + 1) (x (m + 1)) :=
      hFx _ _ _ (hxs.2 (m + 1)) (hΓ _ _ (hx.2 m))
    have : Dx (m + 1) (z (m + 1)) = Dx (m + 1) (xs (m + 1)) - Dx (m + 1) (x (m + 1)) := by
      simp only [z, map_sub]
    rw [this] at hsum
    have := mul_nonneg (pow_nonneg hβ (m + 1)) hxn
    nlinarith
  -- Step 4: transversality makes the bound vanish.
  filter_upwards [htvc.eventually (Ioo_mem_nhds (by linarith : -ε < 0) hε),
    eventually_ge_atTop 1] with n hn h1
  have := hdiff n h1
  have := hn.1
  linarith

end Euler

end Econ
