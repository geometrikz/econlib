/-
# An endogenous asset bound for the income fluctuation problem

Schechtman–Escudero (1977); Aiyagari (1994), §II; Ljungqvist–Sargent ch. 18.

The savings problems of `StochSavings` and `AiyagariEconomy` impose an upper
bound `k̄` on assets. This file **derives** a bound `A` that does not depend on
`k̄`, so once `k̄ > A` the imposed cap never binds.

**Setting.** Cash on hand `h(a, z) = R a + y(z)` with gross return `R > 1`,
income `0 ≤ y(z) ≤ ȳ`, and i.i.d. shocks (all rows of `Q` equal). Utility `u`
satisfies, besides the standing assumptions (continuous, nondecreasing,
strictly concave on `[0, ∞)`):
* an Inada-type condition: `u(d) - u(0)` beats any linear function for small `d`;
* the **Euler gap** (`EulerGap`, a derivative-free form of
  `β R u'(c - y) < u'(c)`) with `y = 0` for every `c > 0`, and with `y = ȳ`
  for every `c > C*`. For `u = √c` both hold whenever `β R < 1`, with
  `C* = ȳ / (1 - (βR)²)` (`sqrt_eulerGap`, `sqrt_inada`).

**Results.**
* `StochSavings.policy_mono`, `cons_mono`: savings and consumption are
  monotone in cash on hand (derivative-free, from concavity and uniqueness).
* `StochSavings.policy_lt_self`: for `A ≥ max(C* / (R - 1), ȳ / R)`,
  households with assets `a ≥ A` run them down, `g(a, z) < a`.
* `policy_le_max`, `policy_lt_kbar`: `[0, A]` is absorbing, and if `A < k̄`
  the cap is slack in every state.
* `measure_gt_eq_zero`: every stationary distribution puts no mass above `A`.
* `StochSavings.riskyHousehold_assetBound`, `AiyagariEconomy.household_cap_slack`,
  `AiyagariEconomy.risky_cap_slack`: instances with genuine income risk.

**Proof idea.** (1) If assets do not fall at `(a, z)`, tomorrow's consumption
is at least `c - ȳ` in every shock (monotonicity), so the one-period
deviation "save `d` less, consume `R d` less tomorrow" and the Euler gap give
`c ≤ C*`. (2) Among states with `a ≥ A` where assets do not fall, take one
with least consumption `c₀ > 0`. Tomorrow consumption is at least `c₀`: either
again such a state (minimality), or assets fall, and then consumption exceeds
`(R - 1) a ≥ C* ≥ c₀`. The Euler gap with `y = 0` (that is, `β R < 1`) then
gives a contradiction.

**Scope and gaps.**
* *Meaning of "slack".* The results show the cap `k̄` never binds and give a
  bound independent of `k̄`. They do not prove that the capped value function
  and policy coincide with those of the problem on `[0, ∞)` (which is not
  formalized).
* *Utility.* The framework needs `u` finite and continuous at `0`, and the
  Inada hypothesis needs `u'(0+) = ∞`; `√c` (CRRA with `σ = 1/2`) qualifies.
  Log and CRRA with `σ ≥ 1`, used by Aiyagari, are excluded.
* The borrowing limit is `0`.
* `household_cap_slack` holds at one `r`; `A` depends on `r` (through
  `C*/r`), and no uniform bound over `[r_lo, r_hi]` or location of the
  equilibrium `r` is given.
* `R > 1` (`r > 0`) is needed: the bound `C* / (R - 1)` blows up as `r ↓ 0`.
  The case `r ≤ 0` is not covered (for `R < 1` a cruder bound `ȳ / (1 - R)`
  is immediate; `R = 1` is open here).
* Shocks are i.i.d.; persistent (Markov) income is not covered.
* The general-equilibrium statement with a slack cap is not packaged: in
  `AiyagariEconomy.exists_stationary_equilibrium` the upper boundary condition
  `hhi` is still a hypothesis, and in our examples it can only be derived (via
  `le_policy`) when `β(1 + r_hi) > 1`, exactly where this bound fails. A
  witness economy where both boundary conditions are derived *and* the cap is
  slack needs the supply-divergence argument as `β(1 + r) ↑ 1`, which is open.
-/
module

public import EconLean.Macro.HA.StochSavings
public import EconLean.Macro.HA.AiyagariGE
public import EconLean.Macro.DP.StochasticConcavity
public import Mathlib.Analysis.Convex.Slope

@[expose] public section

namespace Econ

open Set Filter Topology MeasureTheory ProbabilityTheory BoundedContinuousFunction

/-- **Swap inequality for concave functions.** If `q₁, q₂` lie between `p` and
`r` and have the same sum, then `f p + f r ≤ f q₁ + f q₂`. -/
theorem ConcaveOn.add_le_add_of_between {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f)
    {p q₁ q₂ r : ℝ} (hp : p ∈ s) (hr : r ∈ s) (h1 : p ≤ q₁) (h2 : q₁ ≤ r)
    (hsum : q₁ + q₂ = p + r) : f p + f r ≤ f q₁ + f q₂ := by
  rcases eq_or_lt_of_le (h1.trans h2) with hpr | hpr
  · have hq1 : q₁ = p := le_antisymm (hpr ▸ h2) h1
    have hq2 : q₂ = r := by linarith
    rw [hq1, hq2]
  · have hrp : 0 < r - p := sub_pos.2 hpr
    set l := (r - q₁) / (r - p) with hl
    set m := (q₁ - p) / (r - p) with hm
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hrp.le
    have hm0 : 0 ≤ m := div_nonneg (by linarith) hrp.le
    have hlm : l + m = 1 := by rw [hl, hm, ← add_div]; field_simp; ring
    have e1 : l * p + m * r = q₁ := by rw [hl, hm]; field_simp; ring
    have e2 : m * p + l * r = q₂ := by linear_combination (p + r) * hlm - e1 - hsum
    have c1 := hf.2 hp hr hl0 hm0 hlm
    have c2 := hf.2 hp hr hm0 hl0 (by linarith)
    simp only [smul_eq_mul] at c1 c2
    rw [e1] at c1
    rw [e2] at c2
    have : (l + m) * (f p + f r) = l * f p + m * f r + (m * f p + l * f r) := by ring
    rw [hlm, one_mul] at this
    linarith

/-- **Increments of a concave function are antitone**: for `p ≤ q`,
`f q - f (q - e) ≤ f p - f (p - e)`. -/
theorem ConcaveOn.sub_le_sub_of_le {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f)
    {p q e : ℝ} (hpe : p - e ∈ s) (hq : q ∈ s) (he : 0 ≤ e) (hpq : p ≤ q) :
    f q - f (q - e) ≤ f p - f (p - e) := by
  have := ConcaveOn.add_le_add_of_between hf (q₁ := p) (q₂ := q - e) hpe hq (by linarith) hpq (by ring)
  linarith

/-- The **Euler gap** condition at consumption `c`, income gap `y` and gross
return `R`: arbitrarily small `d > 0` exist with `R d ≤ c - y` and

  `β [u(c - y) - u(c - y - R d)] < u(c + d) - u(c)`.

For differentiable `u` this is the strict inequality `β R u'(c - y) < u'(c)`
in difference form. With `y = 0` it is `β R < 1`. -/
def EulerGap (u : ℝ → ℝ) (β R y c : ℝ) : Prop :=
  ∀ ε > 0, ∃ d, 0 < d ∧ d ≤ ε ∧ R * d ≤ c - y ∧
    β * (u (c - y) - u (c - y - R * d)) < u (c + d) - u c

namespace StochSavings

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] (M : StochSavings Z)

/-- Consumption under a savings policy `g`: `c = h(a, z) - g(a, z)`. -/
def cons (g : M.S × Z → M.S) (s : M.S × Z) : ℝ := M.h s.1 s.2 - g s

/-- The Bellman objective of choosing `y` at `s`. -/
noncomputable def obj (s : M.S × Z) (y : M.S) : ℝ :=
  M.u (M.h s.1 s.2 - y) + M.β * ∑ z', M.Q s.2 z' * M.toStochDynProg.value (y, z')

variable {M} {g : M.S × Z → M.S}

theorem feasible (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (s : M.S × Z) :
    (g s : ℝ) ≤ M.h s.1 s.2 :=
  ((hg s).symm ▸ Set.mem_singleton (g s) : g s ∈ M.toStochDynProg.policy s).1

theorem cons_nonneg (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (s : M.S × Z) :
    0 ≤ M.cons g s :=
  sub_nonneg.2 (feasible hg s)

theorem obj_policy (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (s : M.S × Z) :
    M.obj s (g s) = M.toStochDynProg.value s :=
  M.toStochDynProg.value_eq_of_mem_policy ((hg s).symm ▸ Set.mem_singleton _)

theorem obj_le (s : M.S × Z) (y : M.S) (hy : (y : ℝ) ≤ M.h s.1 s.2) :
    M.obj s y ≤ M.toStochDynProg.value s :=
  M.toStochDynProg.value_ge s hy

/-- If a pair of alternative choices does at least as well, in sum, as the
optimal choices at two states, the alternative at the first state is optimal,
hence equal to the (unique) policy. -/
theorem eq_of_swap (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {s₁ s₂ : M.S × Z}
    {y₁ y₂ : M.S} (hy₁ : (y₁ : ℝ) ≤ M.h s₁.1 s₁.2) (hy₂ : (y₂ : ℝ) ≤ M.h s₂.1 s₂.2)
    (hle : M.obj s₁ (g s₁) + M.obj s₂ (g s₂) ≤ M.obj s₁ y₁ + M.obj s₂ y₂) : y₁ = g s₁ := by
  have e1 := obj_policy hg s₁
  have e2 := obj_policy hg s₂
  have l2 := obj_le s₂ y₂ hy₂
  have hge : M.toStochDynProg.value s₁ ≤ M.obj s₁ y₁ := by linarith
  have hmem : y₁ ∈ M.toStochDynProg.policy s₁ :=
    ⟨hy₁, fun y' hy' => (obj_le s₁ y' hy').trans hge⟩
  rw [hg s₁] at hmem
  exact hmem

omit [TopologicalSpace Z] [DiscreteTopology Z] in
theorem sum_eq_of_row {z₁ z₂ : Z} (hQ : ∀ z', M.Q z₁ z' = M.Q z₂ z') (f : Z → ℝ) :
    ∑ z', M.Q z₁ z' * f z' = ∑ z', M.Q z₂ z' * f z' :=
  Finset.sum_congr rfl fun z' _ => by rw [hQ]

/-- **Savings are monotone in cash on hand** (for states with the same
transition row). Only concavity of `u` and uniqueness of the policy are used. -/
theorem policy_mono (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {s₁ s₂ : M.S × Z}
    (hQ : ∀ z', M.Q s₁.2 z' = M.Q s₂.2 z') (hh : M.h s₁.1 s₁.2 ≤ M.h s₂.1 s₂.2) :
    (g s₁ : ℝ) ≤ g s₂ := by
  by_contra hlt
  rw [not_le] at hlt
  have f1 := feasible hg s₁
  have f2 := feasible hg s₂
  have key := eq_of_swap hg (s₁ := s₁) (s₂ := s₂) (y₁ := g s₂) (y₂ := g s₁) (by linarith) (by linarith) (by
    have hu := ConcaveOn.add_le_add_of_between M.u_strictConcave.concaveOn
      (p := M.h s₁.1 s₁.2 - g s₁) (q₁ := M.h s₁.1 s₁.2 - g s₂) (q₂ := M.h s₂.1 s₂.2 - g s₁)
      (r := M.h s₂.1 s₂.2 - g s₂) (show _ ∈ Ici (0 : ℝ) from sub_nonneg.2 f1)
      (show _ ∈ Ici (0 : ℝ) from sub_nonneg.2 f2) (by linarith) (by linarith) (by ring)
    have hE := fun y : M.S =>
      sum_eq_of_row hQ (fun z' => M.toStochDynProg.value (y, z'))
    simp only [obj, hE]
    linarith)
  exact absurd (congrArg Subtype.val key) (ne_of_lt hlt)

omit [TopologicalSpace Z] [DiscreteTopology Z] in
theorem extendS_coe (f : M.S → ℝ) (x : M.S) : extendS f (x : ℝ) = f x := by
  simp [extendS]

/-- `V(·, z)` is concave on `[0, k̄]`. -/
theorem value_concaveOn (z : Z) :
    ConcaveOn ℝ (Icc 0 M.kbar) (extendS fun x : M.S => M.toStochDynProg.value (x, z)) :=
  (M.toStochDynProg.value_concave (convex_Icc 0 M.kbar) M.convexTech M.concaveRet z).concaveOn
    (convex_Icc 0 M.kbar)

/-- **Consumption is monotone in cash on hand** (for states with the same
transition row): uses concavity of the value function and uniqueness of the
policy. -/
theorem cons_mono (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {s₁ s₂ : M.S × Z}
    (hQ : ∀ z', M.Q s₁.2 z' = M.Q s₂.2 z') (hh : M.h s₁.1 s₁.2 ≤ M.h s₂.1 s₂.2) :
    M.cons g s₁ ≤ M.cons g s₂ := by
  by_contra hlt
  rw [not_le] at hlt
  have f1 := feasible hg s₁
  have f2 := feasible hg s₂
  have c2 := cons_nonneg hg s₂
  unfold cons at hlt c2
  set h₁ := M.h s₁.1 s₁.2
  set h₂ := M.h s₂.1 s₂.2
  let y₁ : M.S := ⟨h₁ - (h₂ - g s₂), by linarith [(g s₁).2.1], by linarith [(g s₂).2.2]⟩
  let y₂ : M.S := ⟨h₂ - (h₁ - g s₁), by linarith [(g s₁).2.1], by linarith [(g s₂).2.2]⟩
  have key := eq_of_swap hg (s₁ := s₁) (s₂ := s₂) (y₁ := y₁) (y₂ := y₂) (show h₁ - (h₂ - g s₂) ≤ h₁ by linarith)
    (show h₂ - (h₁ - g s₁) ≤ h₂ by linarith [(g s₁).2.1]) (by
    have hE := fun y : M.S =>
      sum_eq_of_row hQ (fun z' => M.toStochDynProg.value (y, z'))
    have hV : ∀ z', M.toStochDynProg.value (g s₁, z') + M.toStochDynProg.value (g s₂, z') ≤
        M.toStochDynProg.value (y₁, z') + M.toStochDynProg.value (y₂, z') := fun z' => by
      have := ConcaveOn.add_le_add_of_between (value_concaveOn (M := M) z') (g s₁).2 (g s₂).2
        (q₁ := (y₁ : ℝ)) (q₂ := (y₂ : ℝ)) (show (g s₁ : ℝ) ≤ h₁ - (h₂ - g s₂) by linarith)
        (show h₁ - (h₂ - g s₂) ≤ (g s₂ : ℝ) by linarith) (by simp only [y₁, y₂]; ring)
      simpa only [extendS_coe] using this
    have hsum : ∑ z', M.Q s₁.2 z' * M.toStochDynProg.value (g s₁, z') +
        ∑ z', M.Q s₁.2 z' * M.toStochDynProg.value (g s₂, z') ≤
        ∑ z', M.Q s₁.2 z' * M.toStochDynProg.value (y₁, z') +
        ∑ z', M.Q s₁.2 z' * M.toStochDynProg.value (y₂, z') := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun z' _ => ?_
      rw [← mul_add, ← mul_add]
      exact mul_le_mul_of_nonneg_left (hV z') (M.Q_nonneg _ _)
    have hu1 : h₁ - (y₁ : ℝ) = h₂ - g s₂ := by simp only [y₁]; ring
    have hu2 : h₂ - (y₂ : ℝ) = h₁ - g s₁ := by simp only [y₂]; ring
    simp only [obj, ← hE]
    rw [hu1, hu2]
    nlinarith [M.β_pos])
  have := congrArg Subtype.val key
  simp only [y₁] at this
  linarith

/-- **Envelope inequality.** Lowering cash on hand by `D ≤ c` at a state (same
shock) lowers the value by at most `u(c) - u(c - D)`: keep the same savings
choice and consume `D` less. -/
theorem value_sub_le (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (t t' : M.S × Z)
    (hz : t'.2 = t.2) {D : ℝ} (hD : M.h t'.1 t'.2 = M.h t.1 t.2 - D) (hDc : D ≤ M.cons g t) :
    M.toStochDynProg.value t - M.toStochDynProg.value t' ≤
      M.u (M.cons g t) - M.u (M.cons g t - D) := by
  have e := obj_policy hg t
  have l := obj_le t' (g t) (by rw [hD]; unfold cons at hDc; linarith)
  unfold obj at e l
  rw [hD] at l
  rw [hz] at l
  have : M.h t.1 t.2 - D - g t = M.cons g t - D := by unfold cons; ring
  rw [this] at l
  unfold cons at *
  linarith

/-- **One-period deviation today**: saving `y ≤ g(s)` instead of `g(s)` raises
utility today by at most the discounted expected loss in value tomorrow. -/
theorem dev_le (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (s : M.S × Z) (y : M.S)
    (hy : (y : ℝ) ≤ g s) :
    M.u (M.cons g s + (g s - y)) - M.u (M.cons g s) ≤
      M.β * ∑ z', M.Q s.2 z' *
        (M.toStochDynProg.value (g s, z') - M.toStochDynProg.value (y, z')) := by
  have e := obj_policy hg s
  have l := obj_le s y (hy.trans (feasible hg s))
  unfold obj at e l
  have : M.h s.1 s.2 - y = M.cons g s + (g s - y) := by unfold cons; ring
  rw [this] at l
  simp only [mul_sub, Finset.sum_sub_distrib]
  unfold cons at *
  linarith

/-! ### The income fluctuation problem with i.i.d. income

From here on cash on hand is `h(a, z) = R a + y(z)` with `0 ≤ y(z) ≤ ȳ`, and
the shock is i.i.d. (all rows of `Q` are equal). -/

/-- **The Euler inequality in difference form.** At a state `s`, if tomorrow's
consumption is at least `p ≥ R d` in every shock, then saving `d` less today
gains at most `β [u(p) - u(p - R d)]`. -/
theorem euler_ineq (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {R : ℝ} {inc : Z → ℝ}
    (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 0 < R) (s : M.S × Z) {p d : ℝ} (hd0 : 0 ≤ d)
    (hd : d ≤ g s) (hpR : R * d ≤ p) (hp : ∀ z', p ≤ M.cons g (g s, z')) :
    M.u (M.cons g s + d) - M.u (M.cons g s) ≤ M.β * (M.u p - M.u (p - R * d)) := by
  let y : M.S := ⟨g s - d, by linarith, by linarith [(g s).2.2]⟩
  have hdev := dev_le hg s y (show (g s : ℝ) - d ≤ g s by linarith)
  have hgy : (g s : ℝ) - y = d := by simp only [y]; ring
  rw [hgy] at hdev
  have hz : ∀ z', M.toStochDynProg.value (g s, z') - M.toStochDynProg.value (y, z') ≤
      M.u p - M.u (p - R * d) := fun z' => by
    have env := value_sub_le hg (g s, z') (y, z') rfl (D := R * d)
      (by simp only [hh, y]; ring) ((hpR.trans (hp z')))
    have inc := ConcaveOn.sub_le_sub_of_le M.u_strictConcave.concaveOn
      (p := p) (q := M.cons g (g s, z')) (e := R * d)
      (show p - R * d ∈ Ici (0 : ℝ) from sub_nonneg.2 hpR)
      (show _ ∈ Ici (0 : ℝ) from cons_nonneg hg _) (by positivity) (hp z')
    linarith
  have hsum : ∑ z', M.Q s.2 z' *
      (M.toStochDynProg.value (g s, z') - M.toStochDynProg.value (y, z')) ≤
      M.u p - M.u (p - R * d) := by
    calc _ ≤ ∑ z', M.Q s.2 z' * (M.u p - M.u (p - R * d)) :=
          Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (hz z') (M.Q_nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul, M.Q_sum, one_mul]
  nlinarith [M.β_pos]

/-- **Step 1: consumption is bounded when assets do not fall.** If saving at
least the current assets at `(a, z)` with `a ≥ ȳ / R`, consumption is at most
`C*`, the level above which the Euler gap condition (income gap `ȳ`) holds.
Tomorrow's consumption is at least `c - ȳ` by monotonicity of savings and
consumption, and the Euler inequality then contradicts the gap. -/
theorem cons_le_of_le_policy (hg : ∀ s, M.toStochDynProg.policy s = {g s}) {R ybar Cstar : ℝ}
    {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 0 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hE : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c) (s : M.S × Z)
    (ha : ybar / R ≤ s.1) (ha0 : 0 < (s.1 : ℝ)) (hnd : (s.1 : ℝ) ≤ g s) :
    M.cons g s ≤ Cstar := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨d, hd0, hdε, hdR, hgap⟩ := hE _ hc (g s) (by linarith)
  have hyb : 0 ≤ ybar := (hinc0 s.2).trans (hincb s.2)
  let a' : M.S := ⟨s.1 - ybar / R, by linarith, by linarith [s.1.2.2, div_nonneg hyb hR.le]⟩
  let s' : M.S × Z := (a', s.2)
  have hhs' : M.h s'.1 s'.2 = M.h s.1 s.2 - ybar := by
    simp only [s', a', hh]; field_simp; ring
  have hmono := policy_mono hg (s₁ := s') (s₂ := s) (fun _ => rfl) (by linarith)
  have hcs' : M.cons g s - ybar ≤ M.cons g s' := by unfold cons at *; linarith
  have hp : ∀ z', M.cons g s - ybar ≤ M.cons g (g s, z') := fun z' => by
    refine hcs'.trans (cons_mono hg (fun _ => hiid _ _ _) ?_)
    rw [hhs', hh, hh]
    nlinarith [hincb s.2, hinc0 z']
  have := euler_ineq hg hh hR s hd0.le hdε hdR hp
  linarith

/-- **Step 2: consumption is positive whenever saving is positive**, under the
Inada-type condition that `u(d) - u(0)` beats any linear function for small
`d`. (Uses the chord-slope bound for the concave value function.) -/
theorem cons_pos (hg : ∀ s, M.toStochDynProg.policy s = {g s})
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (s : M.S × Z) (hpos : 0 < (g s : ℝ)) : 0 < M.cons g s := by
  by_contra hc
  have hc0 : M.cons g s = 0 := le_antisymm (not_lt.1 hc) (cons_nonneg hg s)
  set y₁ : ℝ := (g s : ℝ)
  have hy₁k : y₁ ≤ M.kbar := (g s).2.2
  let zero : M.S := ⟨0, le_rfl, M.kbar_pos.le⟩
  let half : M.S := ⟨y₁ / 2, by positivity, by linarith⟩
  set K := M.β * ∑ z', M.Q s.2 z' *
    ((M.toStochDynProg.value (half, z') - M.toStochDynProg.value (zero, z')) / (y₁ / 2))
  obtain ⟨d, hd0, hdε, hK⟩ := hI K (y₁ / 4) (by positivity)
  let y : M.S := ⟨y₁ - d, by linarith, by linarith⟩
  have hdev := dev_le hg s y (show y₁ - d ≤ y₁ by linarith)
  have hgy : (g s : ℝ) - y = d := by simp only [y, y₁]; ring
  rw [hgy, hc0, zero_add] at hdev
  have hz : ∀ z', M.toStochDynProg.value (g s, z') - M.toStochDynProg.value (y, z') ≤
      d * ((M.toStochDynProg.value (half, z') - M.toStochDynProg.value (zero, z')) /
        (y₁ / 2)) := fun z' => by
    have hf := value_concaveOn (M := M) z'
    have s1 := hf.slope_anti_adjacent (x := y₁ / 2) (y := y₁ - d) (z := y₁) half.2 (g s).2
      (by linarith) (by linarith)
    have s2 := hf.slope_anti_adjacent (x := 0) (y := y₁ / 2) (z := y₁ - d) zero.2 y.2
      (by linarith) (by linarith)
    have e1 : extendS (fun x : M.S => M.toStochDynProg.value (x, z')) y₁ =
        M.toStochDynProg.value (g s, z') := extendS_coe _ (g s)
    have e2 : extendS (fun x : M.S => M.toStochDynProg.value (x, z')) (y₁ - d) =
        M.toStochDynProg.value (y, z') := extendS_coe _ y
    have e3 : extendS (fun x : M.S => M.toStochDynProg.value (x, z')) (y₁ / 2) =
        M.toStochDynProg.value (half, z') := extendS_coe _ half
    have e4 : extendS (fun x : M.S => M.toStochDynProg.value (x, z')) 0 =
        M.toStochDynProg.value (zero, z') := extendS_coe _ zero
    rw [e1, e2, e3] at s1
    rw [e2, e3, e4, sub_zero] at s2
    have hle := s1.trans s2
    rw [show y₁ - (y₁ - d) = d by ring, div_le_iff₀ hd0] at hle
    linarith
  have hsum : ∑ z', M.Q s.2 z' *
      (M.toStochDynProg.value (g s, z') - M.toStochDynProg.value (y, z')) ≤
      d * ∑ z', M.Q s.2 z' *
        ((M.toStochDynProg.value (half, z') - M.toStochDynProg.value (zero, z')) / (y₁ / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z' _ => ?_
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hz z') (M.Q_nonneg _ _)
  have : M.u d - M.u 0 ≤ K * d := by
    simp only [K]
    nlinarith [M.β_pos]
  linarith

/-- **The endogenous asset bound** (Schechtman–Escudero 1977; Aiyagari 1994,
§II). Income fluctuation problem with gross return `R > 1`, i.i.d. income
`0 ≤ y(z) ≤ ȳ`, and utility satisfying an Inada condition at `0`, the Euler gap
`β R u'(c) < u'(c)` (in difference form, for all `c > 0`) and the Euler gap
with income spread `ȳ` above some `C*` (`β R u'(c - ȳ) < u'(c)` for `c > C*`;
this is where `β R < 1` and curvature enter). Then for any
`A ≥ max(C* / (R - 1), ȳ / R)`, `A > 0`, households with assets `a ≥ A` run
assets down: `g(a, z) < a`. The bound `A` does not depend on the cap `k̄`.

Proof: suppose some state with `a ≥ A` has `g ≥ a`; the set of such states is
compact, so pick one, `s₀`, with least consumption `c₀`. By Step 1,
`c₀ ≤ C*`; by Step 2, `c₀ > 0`. Tomorrow, from assets `a₁ = g(s₀) ≥ A`,
consumption is at least `c₀` in every shock: either the state is again in the
set (minimality), or assets fall and consumption exceeds `(R - 1) a₁ ≥ C*`.
The Euler inequality with gap `0` then contradicts `β R < 1`. -/
theorem policy_lt_self (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A)
    (s : M.S × Z) (hs : A ≤ s.1) : (g s : ℝ) < s.1 := by
  by_contra hns
  rw [not_lt] at hns
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  let N : Set (M.S × Z) := {t | A ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ g t}
  have hNc : IsClosed N :=
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst)).inter
      (isClosed_le (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp hgc))
  have hcc : Continuous (M.cons g) := M.continuous_h.sub (continuous_subtype_val.comp hgc)
  obtain ⟨s₀, hs₀, hmin⟩ := hNc.isCompact.exists_isMinOn ⟨s, hs, hns⟩ hcc.continuousOn
  have hc₀ : M.cons g s₀ ≤ Cstar :=
    cons_le_of_le_policy hg hh (by linarith) hinc0 hincb hiid hEC s₀ (hAy.trans hs₀.1)
      (by linarith [hs₀.1]) hs₀.2
  have hy₁A : A ≤ (g s₀ : ℝ) := hs₀.1.trans hs₀.2
  have hc₀pos : 0 < M.cons g s₀ := cons_pos hg hI s₀ (by linarith)
  obtain ⟨d, hd0, hdε, hdR, hgap⟩ := hE0 _ hc₀pos (g s₀) (by linarith)
  rw [sub_zero] at hdR hgap
  have hp : ∀ z', M.cons g s₀ ≤ M.cons g (g s₀, z') := fun z' => by
    by_cases ht : ((g s₀ : M.S) : ℝ) ≤ g (g s₀, z')
    · exact hmin (show (g s₀, z') ∈ N from ⟨hy₁A, ht⟩)
    · rw [not_le] at ht
      have : (R - 1) * A ≤ (R - 1) * (g s₀ : ℝ) :=
        mul_le_mul_of_nonneg_left hy₁A (by linarith)
      have e : M.cons g (g s₀, z') = R * (g s₀ : ℝ) + inc z' - g (g s₀, z') := by
        unfold cons; rw [hh]
      rw [e]
      nlinarith [hinc0 z']
  have := euler_ineq hg hh (by linarith) s₀ hd0.le hdε hdR hp
  linarith

/-- **Assets above `A` never grow, and `[0, A]` is absorbing**:
`g(a, z) ≤ max(A, a)`. -/
theorem policy_le_max (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A) (s : M.S × Z) :
    (g s : ℝ) ≤ max A s.1 := by
  by_cases hs : A ≤ s.1
  · exact (policy_lt_self hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC s hs).le.trans
      (le_max_right _ _)
  · rw [not_le] at hs
    by_cases hAk : A ≤ M.kbar
    · let sA : M.S × Z := (⟨A, hA0.le, hAk⟩, s.2)
      have h1 := policy_mono hg (s₁ := s) (s₂ := sA) (fun _ => rfl)
        (by simp only [sA, hh]; nlinarith)
      have h2 := policy_lt_self hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC sA le_rfl
      exact (h1.trans h2.le).trans (le_max_left _ _)
    · exact ((g s).2.2.trans (not_le.1 hAk).le).trans (le_max_left _ _)

/-- **The asset cap does not bind** once it exceeds the endogenous bound:
if `A < k̄` then `g(a, z) < k̄` in every state. -/
theorem policy_lt_kbar (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A) (hAk : A < M.kbar)
    (s : M.S × Z) : (g s : ℝ) < M.kbar := by
  by_cases hs : A ≤ s.1
  · exact (policy_lt_self hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC s hs).trans_le
      s.1.2.2
  · have := policy_le_max hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC s
    rw [max_eq_left (not_le.1 hs).le] at this
    linarith

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Every stationary distribution lives on `[0, A]`**: `π{a > A} = 0`.
(Proof: `φ(a) = max(a - A, 0)` has the same mean under `π` and under its image
by the policy, while `φ(g) ≤ φ(a)` with strict inequality when `a > A`.) -/
theorem measure_gt_eq_zero (hg : ∀ s, M.toStochDynProg.policy s = {g s})
    (hgc : Continuous g)
    {R ybar Cstar A : ℝ} {inc : Z → ℝ} (hh : ∀ k z, M.h k z = R * k + inc z) (hR : 1 < R)
    (hinc0 : ∀ z, 0 ≤ inc z) (hincb : ∀ z, inc z ≤ ybar)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap M.u M.β R 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap M.u M.β R ybar c)
    (hA0 : 0 < A) (hAy : ybar / R ≤ A) (hAC : Cstar ≤ (R - 1) * A)
    (hgm : Measurable g) (μ : Measure (M.S × Z)) [IsProbabilityMeasure μ]
    (hμ : Kernel.Invariant (policyKernel M.Q g hgm) μ) : μ {s | A < (s.1 : ℝ)} = 0 := by
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  let φ : M.S × Z →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun s => max ((s.1 : ℝ) - A) 0,
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const).max continuous_const⟩
  let D : M.S × Z →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun s => max ((s.1 : ℝ) - A) 0 - max ((g s : ℝ) - A) 0,
      (((continuous_subtype_val.comp continuous_fst).sub continuous_const).max
        continuous_const).sub
        (((continuous_subtype_val.comp hgc).sub continuous_const).max continuous_const)⟩
  have hD0 : 0 ≤ ⇑D := fun s => by
    have := policy_le_max hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC s
    show 0 ≤ max ((s.1 : ℝ) - A) 0 - max ((g s : ℝ) - A) 0
    rw [sub_nonneg]
    refine max_le ?_ (le_max_right _ _)
    rcases le_total A s.1 with h | h
    · rw [max_eq_right h] at this; exact (sub_le_sub_right this A).trans (le_max_left _ _)
    · rw [max_eq_left h] at this; linarith [le_max_right ((s.1 : ℝ) - A) 0]
  -- `∫ φ dμ = ∫ φ ∘ g dμ` by invariance
  have := isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum g hgm
  have hμ' : policyKernel M.Q g hgm ∘ₘ μ = μ := hμ
  have hφ : ∫ s, φ s ∂μ = ∫ s, max ((g s : ℝ) - A) 0 ∂μ := by
    conv_lhs => rw [← hμ']
    rw [integral_comp_measure (φ.integrable _)]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show ∫ y, φ y ∂(policyKernel M.Q g hgm s) = _
    rw [integral_policyKernel M.Q_nonneg]
    show ∑ z', M.Q s.2 z' * max ((g s : ℝ) - A) 0 = _
    rw [← Finset.sum_mul, M.Q_sum, one_mul]
  have hint : ∫ s, D s ∂μ = 0 := by
    have hi2 : Integrable (fun s : M.S × Z => max ((g s : ℝ) - A) 0) μ := by
      refine (φ - D).integrable μ |>.congr (ae_of_all _ fun s => ?_)
      show max ((s.1 : ℝ) - A) 0 - (max ((s.1 : ℝ) - A) 0 - max ((g s : ℝ) - A) 0) = _
      ring
    show ∫ s, (φ s - max ((g s : ℝ) - A) 0) ∂μ = 0
    rw [integral_sub (φ.integrable μ) hi2]
    exact sub_eq_zero.2 hφ
  have hae := (integral_eq_zero_iff_of_nonneg hD0 (D.integrable μ)).1 hint
  refine measure_mono_null (fun s (hs : A < (s.1 : ℝ)) => ?_) (ae_iff.1 hae)
  show D s ≠ 0
  have hlt := policy_lt_self hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy hAC s hs.le
  show max ((s.1 : ℝ) - A) 0 - max ((g s : ℝ) - A) 0 ≠ 0
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ s.1 - A)]
  have : max ((g s : ℝ) - A) 0 < (s.1 : ℝ) - A := max_lt (by linarith) (by linarith)
  linarith

end StochSavings

/-! ### Square-root utility satisfies the conditions -/

/-- `√` satisfies the Inada-type condition at `0`. -/
theorem sqrt_inada (K ε : ℝ) (hε : 0 < ε) :
    ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < Real.sqrt d - Real.sqrt 0 := by
  set t := min (Real.sqrt ε) (1 / (2 * (|K| + 1))) with ht
  have hK : 0 ≤ |K| := abs_nonneg K
  have ht0 : 0 < t := lt_min (Real.sqrt_pos.2 hε) (by positivity)
  have ht1 : t ≤ Real.sqrt ε := min_le_left _ _
  have ht2 : t ≤ 1 / (2 * (|K| + 1)) := min_le_right _ _
  refine ⟨t ^ 2, by positivity, ?_, ?_⟩
  · calc t ^ 2 ≤ Real.sqrt ε ^ 2 := pow_le_pow_left₀ ht0.le ht1 2
      _ = ε := Real.sq_sqrt hε.le
  · rw [Real.sqrt_sq ht0.le, Real.sqrt_zero, sub_zero]
    have h2 : 2 * (|K| + 1) * t ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at ht2; linarith
    have hKt : K * t ^ 2 ≤ |K| * t ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    nlinarith

/-- **`√` satisfies the Euler gap** at `c` with income gap `y` whenever
`y < (1 - (βR)²) c`, i.e. `c > y / (1 - (βR)²)`. (In derivative form:
`β R / (2√(c - y)) < 1 / (2√c)`.) With `y = 0` this holds for every `c > 0`. -/
theorem sqrt_eulerGap {β R y c : ℝ} (hβ : 0 < β) (hR : 0 < R) (hβR : β * R < 1) (hy : 0 ≤ y)
    (hc : y < (1 - (β * R) ^ 2) * c) : EulerGap Real.sqrt β R y c := by
  have hθ : 0 < β * R := mul_pos hβ hR
  have hθ2 : (β * R) ^ 2 < 1 := by nlinarith
  have hc0 : 0 < c := by
    by_contra h; rw [not_lt] at h; nlinarith
  have hcy : 0 < c - y := by nlinarith
  have key0 : β * R * Real.sqrt c < Real.sqrt (c - y) := by
    rw [Real.lt_sqrt (by positivity), mul_pow, Real.sq_sqrt hc0.le]
    nlinarith
  intro ε hε
  let φ : ℝ → ℝ := fun d => Real.sqrt (c - y) + Real.sqrt (c - y - R * d) -
    β * R * (Real.sqrt (c + d) + Real.sqrt c)
  have hφc : Continuous φ := by fun_prop
  have hφ0 : 0 < φ 0 := by simp only [φ, mul_zero, sub_zero, add_zero]; linarith
  have h1 : ∀ᶠ d in 𝓝 (0 : ℝ), 0 < φ d := (hφc.tendsto 0).eventually (lt_mem_nhds hφ0)
  have h2 : ∀ᶠ d in 𝓝 (0 : ℝ), d < ε := Iio_mem_nhds hε
  have hRd : Tendsto (fun d : ℝ => R * d) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun d : ℝ => R * d := by fun_prop
    have := hc.tendsto (0 : ℝ)
    simp only [mul_zero] at this
    exact this
  have h3 : ∀ᶠ d in 𝓝 (0 : ℝ), R * d < c - y := hRd.eventually (gt_mem_nhds hcy)
  obtain ⟨d, ⟨⟨hφd, hdε⟩, hdR⟩, hd0⟩ :=
    ((((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hd0' : (0 : ℝ) < d := hd0
  refine ⟨d, hd0', hdε.le, hdR.le, ?_⟩
  set a1 := Real.sqrt (c + d)
  set a2 := Real.sqrt c
  set b1 := Real.sqrt (c - y)
  set b2 := Real.sqrt (c - y - R * d)
  have e1 : a1 ^ 2 = c + d := Real.sq_sqrt (by linarith)
  have e2 : a2 ^ 2 = c := Real.sq_sqrt hc0.le
  have e3 : b1 ^ 2 = c - y := Real.sq_sqrt hcy.le
  have e4 : b2 ^ 2 = c - y - R * d := Real.sq_sqrt (by linarith)
  have hX : 0 < a1 - a2 := sub_pos.2 (Real.sqrt_lt_sqrt hc0.le (by linarith))
  have hb1 : 0 < b1 := Real.sqrt_pos.2 hcy
  have hb2 : 0 ≤ b2 := Real.sqrt_nonneg _
  have hφd' : 0 < b1 + b2 - β * R * (a1 + a2) := hφd
  have hL : (b1 + b2) * (β * (b1 - b2)) = β * R * d := by linear_combination β * (e3 - e4)
  have hM : (b1 + b2) * (a1 - a2) = (a1 - a2) * (b1 + b2 - β * R * (a1 + a2)) + β * R * d := by
    linear_combination β * R * (e1 - e2)
  have : (b1 + b2) * (β * (b1 - b2)) < (b1 + b2) * (a1 - a2) := by
    rw [hL, hM]; nlinarith [mul_pos hX hφd']
  have := lt_of_mul_lt_mul_left this (by linarith)
  show β * (b1 - b2) < a1 - a2
  exact this

/-! ### A household with income risk where the bound is slack -/

/-- **An Aiyagari household with income risk**: `u = √c`, gross return
`R = 11/10`, `β = 1/2` (so `β R = 11/20 < 1`), i.i.d. income `y ∈ {0, 1}` with
probability `1/2` each, asset space `[0, 20]`. -/
noncomputable def StochSavings.riskyHousehold : StochSavings (Fin 2) where
  u := Real.sqrt
  h := fun a z => 11 / 10 * a + ![0, 1] z
  Q := fun _ _ => 1 / 2
  β := 1 / 2
  kbar := 20
  Q_nonneg := fun _ _ => by norm_num
  Q_sum := fun _ => by norm_num [Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  h_continuous := fun _ => (continuous_const.mul continuous_id).add continuous_const
  h_nonneg := fun z k hk => by fin_cases z <;> simp <;> positivity
  h_concave := fun z => ⟨convex_Ici 0, fun x _ y _ a b _ _ hab => by
    simp only [smul_eq_mul]
    exact le_of_eq (by linear_combination (![(0 : ℝ), 1] z) * hab)⟩

/-- **The asset cap is slack in the risky household**: with `A = 15 < k̄ = 20`,
households with assets `a ≥ 15` run them down, saving is strictly below the
cap in every state, a stationary wealth distribution exists, and every
stationary wealth distribution lives on `[0, 15]`. Here `C* = 3/2 > ȳ / (1 - (βR)²) = 400/279` and
`A = C* / (R - 1) = 15`. -/
theorem StochSavings.riskyHousehold_assetBound :
    ∃ g : StochSavings.riskyHousehold.S × Fin 2 → StochSavings.riskyHousehold.S,
      Continuous g ∧ (∀ s, StochSavings.riskyHousehold.toStochDynProg.policy s = {g s}) ∧
      (∀ s, (15 : ℝ) ≤ s.1 → (g s : ℝ) < s.1) ∧ (∀ s, (g s : ℝ) < 20) ∧
      ∃ (hg : Measurable g) (μ : Measure (StochSavings.riskyHousehold.S × Fin 2)),
        IsProbabilityMeasure μ ∧ Kernel.Invariant (policyKernel (fun _ _ => 1 / 2) g hg) μ ∧
        ∀ ν : Measure (StochSavings.riskyHousehold.S × Fin 2), IsProbabilityMeasure ν →
          Kernel.Invariant (policyKernel (fun _ _ => 1 / 2) g hg) ν → ν {s | (15 : ℝ) < s.1} = 0 := by
  set M := StochSavings.riskyHousehold
  obtain ⟨g, hgc, hg, hgm, μ, hμp, hμ⟩ := M.exists_stationary
  have hh : ∀ k z, M.h k z = 11 / 10 * k + ![(0 : ℝ), 1] z := fun _ _ => rfl
  have hinc0 : ∀ z, (0 : ℝ) ≤ ![(0 : ℝ), 1] z := fun z => by fin_cases z <;> norm_num
  have hincb : ∀ z, ![(0 : ℝ), 1] z ≤ 1 := fun z => by fin_cases z <;> norm_num
  have hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z' := fun _ _ _ => rfl
  have hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < M.u d - M.u 0 := sqrt_inada
  have hu : M.u = Real.sqrt := rfl
  have hβ : M.β = 1 / 2 := rfl
  have hE0 : ∀ c, 0 < c → EulerGap M.u M.β (11 / 10) 0 c := fun c hc => by
    rw [hu, hβ]; exact sqrt_eulerGap (by norm_num) (by norm_num) (by norm_num) le_rfl (by nlinarith)
  have hEC : ∀ c, (3 / 2 : ℝ) < c → EulerGap M.u M.β (11 / 10) 1 c := fun c hc => by
    rw [hu, hβ]; exact sqrt_eulerGap (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by nlinarith)
  have hR : (1 : ℝ) < 11 / 10 := by norm_num
  have hA0 : (0 : ℝ) < 15 := by norm_num
  have hAy : (1 : ℝ) / (11 / 10) ≤ 15 := by norm_num
  have hAC : (3 / 2 : ℝ) ≤ (11 / 10 - 1) * 15 := by norm_num
  refine ⟨g, hgc, hg, fun s hs => StochSavings.policy_lt_self hg hgc hh hR hinc0 hincb hiid hI
    hE0 hEC hA0 hAy hAC s hs, fun s => StochSavings.policy_lt_kbar hg hgc hh hR hinc0 hincb hiid
    hI hE0 hEC hA0 hAy hAC (by show (15 : ℝ) < 20; norm_num) s, hgm, μ, hμp, hμ,
    fun ν _ hν => StochSavings.measure_gt_eq_zero hg hgc hh hR hinc0 hincb hiid hI hE0 hEC hA0 hAy
      hAC hgm ν hν⟩

/-! ### The Aiyagari household at a given interest rate -/

namespace AiyagariEconomy

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] (E : AiyagariEconomy Z)

/-- **The asset cap is slack for the Aiyagari household** at any interest rate
`r > 0` with the Euler gap conditions (which need `β(1 + r) < 1`), when income
is i.i.d. and efficiency units are at most `ē`: with `ȳ = w(r) ē`, any
`A ≥ max(C* / r, ȳ / (1 + r))`, `0 < A < k̄`, households with assets `a ≥ A`
decumulate, saving is strictly below the cap, and every stationary
distribution at `r` lives on `[0, A]`. -/
theorem household_cap_slack (r : Icc E.rlo E.rhi) (hr : 0 < (r : ℝ)) {emax Cstar A : ℝ}
    (he : ∀ z, E.e z ≤ emax) (hiid : ∀ z₁ z₂ z', E.Q z₁ z' = E.Q z₂ z')
    (hI : ∀ K ε : ℝ, 0 < ε → ∃ d, 0 < d ∧ d ≤ ε ∧ K * d < E.u d - E.u 0)
    (hE0 : ∀ c, 0 < c → EulerGap E.u E.β (1 + r) 0 c)
    (hEC : ∀ c, Cstar < c → EulerGap E.u E.β (1 + r) (E.firm.wage r * emax) c)
    (hA0 : 0 < A) (hAy : E.firm.wage r * emax / (1 + r) ≤ A) (hAC : Cstar ≤ r * A)
    (hAk : A < E.kbar) {g : E.household.S × Z → E.household.S}
    (hg : ∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) (hgc : Continuous g) :
    (∀ s, A ≤ (s.1 : ℝ) → (g s : ℝ) < s.1) ∧ (∀ s, (g s : ℝ) < E.kbar) ∧
      ∀ [MeasurableSpace Z] [BorelSpace Z] (hgm : Measurable g) (μ : Measure (E.household.S × Z))
        [IsProbabilityMeasure μ], Kernel.Invariant (policyKernel E.Q g hgm) μ →
        μ {s | A < (s.1 : ℝ)} = 0 := by
  set M := E.household.slice r
  have hw := (E.firm.wage_pos E.mem_Ioi (r := r)).le
  have hh : ∀ k z, M.h k z = (1 + r) * k + E.firm.wage r * E.e z := fun _ _ => rfl
  have hinc0 : ∀ z, 0 ≤ E.firm.wage r * E.e z := fun z => mul_nonneg hw (E.e_nonneg z)
  have hincb : ∀ z, E.firm.wage r * E.e z ≤ E.firm.wage r * emax := fun z =>
    mul_le_mul_of_nonneg_left (he z) hw
  have hR : (1 : ℝ) < 1 + r := by linarith
  have hAC' : Cstar ≤ (1 + r - 1) * A := by rw [add_sub_cancel_left]; exact hAC
  have hiid' : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z' := hiid
  refine ⟨fun s hs => StochSavings.policy_lt_self hg hgc hh hR hinc0 hincb hiid' hI hE0 hEC
    hA0 hAy hAC' s hs, fun s => StochSavings.policy_lt_kbar hg hgc hh hR hinc0 hincb hiid' hI
    hE0 hEC hA0 hAy hAC' hAk s, fun hgm μ _ hμ => ?_⟩
  exact StochSavings.measure_gt_eq_zero (M := M) hg hgc hh hR hinc0 hincb hiid' hI hE0 hEC hA0
    hAy hAC' hgm μ hμ

/-- **An Aiyagari economy with income risk** (witness for
`household_cap_slack`): `u = √c`, `β = 1/2`, i.i.d. efficiency units
`e ∈ {0, 2}` with probability `1/2` (so `L = 1`), cap `k̄ = 50`, Cobb–Douglas
firm with `α = 1/2`, `δ = 1/10`, `r ∈ [1/10, 1/5]`. -/
noncomputable def riskyEconomy : AiyagariEconomy (Fin 2) where
  u := Real.sqrt
  Q := fun _ _ => 1 / 2
  β := 1 / 2
  kbar := 50
  e := ![0, 2]
  firm := CDFirm.half
  rlo := 1 / 10
  rhi := 1 / 5
  qbar := fun _ => 1 / 2
  Q_nonneg := fun _ _ => by norm_num
  Q_sum := fun _ => by norm_num [Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  e_nonneg := fun z => by fin_cases z <;> norm_num
  rlo_gt := by norm_num [CDFirm.half]
  rlo_ge := by norm_num
  rlo_le := by norm_num
  qbar_inv := half_isInvariant
  qbar_unique := fun π hπ => by
    have hQ : IsStochastic (fun _ _ => (1 / 2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨fun _ _ => by norm_num, fun _ => by norm_num [Fin.sum_univ_two]⟩
    obtain ⟨π₀, -, hu, -⟩ := doeblin hQ (ε := 1 / 2) (by norm_num) (fun _ _ => le_rfl)
    rw [hu π hπ, ← hu _ half_isInvariant]
  labor_pos := by norm_num [Fin.sum_univ_two]

/-- **In the risky economy at `r = 1/10` the asset cap is slack**: `w = 5/4`,
`ȳ = 5/2`, `C* = 4`, `A = 40 < k̄ = 50`. Households with `a ≥ 40` decumulate,
saving stays below the cap, and every stationary distribution lives on
`[0, 40]`. -/
theorem risky_cap_slack :
    ∃ g : riskyEconomy.household.S × Fin 2 → riskyEconomy.household.S, Continuous g ∧
      (∀ s, (riskyEconomy.household.slice ⟨1 / 10, le_rfl, riskyEconomy.rlo_le⟩).toStochDynProg.policy
        s = {g s}) ∧
      (∀ s, (40 : ℝ) ≤ s.1 → (g s : ℝ) < s.1) ∧ (∀ s, (g s : ℝ) < 50) ∧
      ∃ (hg : Measurable g) (μ : Measure (riskyEconomy.household.S × Fin 2)),
        IsProbabilityMeasure μ ∧ Kernel.Invariant (policyKernel riskyEconomy.Q g hg) μ ∧
        ∀ ν : Measure (riskyEconomy.household.S × Fin 2), IsProbabilityMeasure ν →
          Kernel.Invariant (policyKernel riskyEconomy.Q g hg) ν → ν {s | (40 : ℝ) < s.1} = 0 := by
  set E := riskyEconomy
  set r : Icc E.rlo E.rhi := ⟨1 / 10, le_rfl, E.rlo_le⟩
  obtain ⟨g, hgc, hg, hgm, μ, hμp, hμ⟩ := (E.household.slice r).exists_stationary
  have hw : E.firm.wage r = 5 / 4 := by
    rw [show E.firm = CDFirm.half from rfl, CDFirm.half_wage _ (by norm_num [r])]
    norm_num [r]
  have hu : E.u = Real.sqrt := rfl
  have hβ : E.β = 1 / 2 := rfl
  have hr : ((r : ℝ)) = 1 / 10 := rfl
  have hE0 : ∀ c, 0 < c → EulerGap E.u E.β (1 + r) 0 c := fun c hc => by
    rw [hu, hβ, hr]
    exact sqrt_eulerGap (by norm_num) (by norm_num) (by norm_num) le_rfl (by nlinarith)
  have hEC : ∀ c, (4 : ℝ) < c → EulerGap E.u E.β (1 + r) (E.firm.wage r * 2) c := fun c hc => by
    rw [hu, hβ, hr, hw]
    exact sqrt_eulerGap (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by nlinarith)
  have he : ∀ z, E.e z ≤ 2 := fun z => by fin_cases z <;> norm_num [E, riskyEconomy]
  obtain ⟨h1, h2, h3⟩ := E.household_cap_slack r (by rw [hr]; norm_num) he (fun _ _ _ => rfl)
    (by rw [hu]; exact sqrt_inada) hE0 hEC (A := 40) (by norm_num)
    (by rw [hw, hr]; norm_num) (by rw [hr]; norm_num) (by show (40 : ℝ) < 50; norm_num) hg hgc
  exact ⟨g, hgc, hg, h1, h2, hgm, μ, hμp, hμ, fun ν _ hν => h3 hgm ν hν⟩

end AiyagariEconomy

end Econ
