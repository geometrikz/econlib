/-
# The Bellman equation for bounded continuous returns

Stokey–Lucas (SL), *Recursive Methods in Economic Dynamics*, §4.2
(Thms 4.2–4.7).

**The economics.** A stationary deterministic dynamic program has a state
space `X`, a feasibility correspondence `Γ : X ↠ X` (tomorrow's feasible
states given today's), a one-period return `F(x, y)` from moving from `x` to
`y`, and a discount factor `β`. Its **Bellman (functional) equation** is

  `v(x) = max_{y ∈ Γ(x)} [F(x, y) + β v(y)]`.

Under SL's Assumptions 4.3–4.4 (Γ nonempty, compact-valued and continuous;
`F` bounded and continuous; `0 < β < 1`) we prove:

* the **Bellman operator** `(T v)(x) = max_{y ∈ Γ(x)} [F(x, y) + β v(y)]` maps
  bounded continuous functions to bounded continuous functions (via Berge's
  maximum theorem, `Foundations/Maximum.lean`) and is a contraction by
  Blackwell's conditions (`Blackwell.lean`);
* hence the Bellman equation has a **unique** bounded continuous solution
  `V = value`, and value-function iteration converges to it (SL Thm 4.6);
* the **policy correspondence** `G(x) = argmax_{y ∈ Γ(x)} [F(x, y) + β V(y)]`
  is nonempty, compact-valued and UHC (SL Thm 4.6);
* **principle of optimality** (SL Thms 4.2–4.5): `V(x₀)` is the maximal
  discounted payoff over all feasible plans; a feasible plan is optimal iff it
  follows the policy correspondence at every date;
* **monotonicity** of `V` (SL Thm 4.7).

**Documented deviations from SL.**
* `F` is assumed continuous on all of `X × X` (SL: on the graph `A` of `Γ`),
  inherited from our Berge theorem; `F` is bounded on the graph, as in SL.
  For metric `X` this loses nothing (the graph is closed, so Tietze extends a
  continuous `F` from the graph), but on a general space it is a restriction.
  Log utility is outside `DynProg` (unbounded); see `BrockMirman.lean`.
* The principle of optimality here is the bounded case of SL Thms 4.2–4.5.
  For unbounded returns use the verification theorems of
  `SequenceProblem.lean`; SL's general Thms 4.2/4.4 under Assumptions 4.1–4.2
  are not yet formalized.
* `X` is any topological space (SL: a convex subset of `ℝ^l`; convexity is
  only used for concavity results, see `Concavity.lean`).

**Junk-value note.** `maxValue` is an `sSup`, meaningful only when attained;
every value here is attained (compact nonempty `Γ x`), and the headline
statements say so with `IsGreatest`. The payoff `∑'` is only used for
feasible plans, where we prove the series is summable (`summable_payoff`).
-/
module

public import EconLean.Foundations.Maximum
public import EconLean.Macro.DP.Blackwell
public import EconLean.Macro.DP.SequenceProblem

@[expose] public section

namespace Econ

open BoundedContinuousFunction Filter Topology Set Finset

/-- A **stationary dynamic program** satisfying SL Assumptions 4.3–4.4. -/
structure DynProg (X : Type*) [TopologicalSpace X] where
  /-- feasibility correspondence: `y ∈ Γ x` means `y` can follow `x` -/
  Γ : X → Set X
  /-- one-period return from moving from `x` to `y` -/
  F : X → X → ℝ
  /-- discount factor -/
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  Γ_compact : ∀ x, IsCompact (Γ x)
  Γ_continuous : ContinuousCorrespondence Γ
  F_continuous : Continuous (Function.uncurry F)
  F_bounded : ∃ M, ∀ x, ∀ y ∈ Γ x, |F x y| ≤ M

namespace DynProg

variable {X : Type*} [TopologicalSpace X] (P : DynProg X)

/-- The right-hand side of the Bellman equation, `F(x, y) + β v(y)`. -/
def objective (v : X →ᵇ ℝ) (x y : X) : ℝ := P.F x y + P.β * v y

theorem continuous_objective (v : X →ᵇ ℝ) : Continuous (Function.uncurry (P.objective v)) := by
  show Continuous fun p : X × X => P.F p.1 p.2 + P.β * v p.2
  exact P.F_continuous.add (continuous_const.mul (v.continuous.comp continuous_snd))

/-- A bound on `|F|` over the graph of `Γ`. -/
noncomputable def bound : ℝ := Classical.choose P.F_bounded

theorem abs_F_le {x y : X} (hy : y ∈ P.Γ x) : |P.F x y| ≤ P.bound :=
  Classical.choose_spec P.F_bounded x y hy

theorem isGreatest_maxValue_objective (v : X →ᵇ ℝ) (x : X) :
    IsGreatest (P.objective v x '' P.Γ x) (maxValue (P.objective v) P.Γ x) :=
  isGreatest_maxValue (P.continuous_objective v) (P.Γ_nonempty x) (P.Γ_compact x)

/-- The **Bellman operator** `(T v)(x) = max_{y ∈ Γ(x)} [F(x, y) + β v(y)]`
on bounded continuous functions. Continuity of `T v` is Berge's theorem;
boundedness is `|T v| ≤ sup |F| + β ‖v‖`. -/
noncomputable def bellmanOp (v : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (maxValue (P.objective v) P.Γ)
    (continuous_maxValue (P.continuous_objective v) P.Γ_continuous P.Γ_nonempty
      P.Γ_compact)
    (P.bound + P.β * ‖v‖) (fun x => by
      obtain ⟨y, hy, he⟩ := (P.isGreatest_maxValue_objective v x).1
      rw [← he, Real.norm_eq_abs, objective]
      have h1 := P.abs_F_le hy
      have h2 : |v y| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm y
      have hβ := P.β_pos.le
      calc |P.F x y + P.β * v y| ≤ |P.F x y| + |P.β * v y| := abs_add_le _ _
        _ = |P.F x y| + P.β * |v y| := by rw [abs_mul, abs_of_pos P.β_pos]
        _ ≤ P.bound + P.β * ‖v‖ := by gcongr)

theorem bellmanOp_apply (v : X →ᵇ ℝ) (x : X) :
    P.bellmanOp v x = maxValue (P.objective v) P.Γ x := rfl

/-- `T v (x)` is the attained maximum of `F(x, y) + β v(y)` over `y ∈ Γ(x)`. -/
theorem isGreatest_bellmanOp (v : X →ᵇ ℝ) (x : X) :
    IsGreatest ((fun y => P.F x y + P.β * v y) '' P.Γ x) (P.bellmanOp v x) :=
  P.isGreatest_maxValue_objective v x

/-- **The Bellman operator is a contraction of modulus `β`**, by Blackwell's
sufficient conditions (SL Thm 4.6, first step). -/
theorem contracting : ContractingWith ⟨P.β, P.β_pos.le⟩ P.bellmanOp := by
  refine blackwell P.β_pos.le P.β_lt_one _ (fun f g hfg x => ?_) (fun f a ha x => ?_)
  · -- monotone: a maximizer for `f` does at least as well under `g`.
    obtain ⟨y, hy, he⟩ := (P.isGreatest_bellmanOp f x).1
    rw [← he]
    refine le_trans ?_ ((P.isGreatest_bellmanOp g x).2 ⟨y, hy, rfl⟩)
    have := hfg y
    have := P.β_pos
    simp only; nlinarith
  · -- discounting: a maximizer for `f + a` earns `β a` more than under `f`.
    obtain ⟨y, hy, he⟩ := (P.isGreatest_bellmanOp (f + const X a) x).1
    rw [← he]
    have := (P.isGreatest_bellmanOp f x).2 ⟨y, hy, rfl⟩
    simp only [add_apply, const_apply] at this ⊢
    linarith

/-- The **value function**: the unique fixed point of the Bellman operator. -/
noncomputable def value : X →ᵇ ℝ := ContractingWith.fixedPoint P.bellmanOp P.contracting

theorem bellmanOp_value : P.bellmanOp P.value = P.value :=
  ContractingWith.fixedPoint_isFixedPt P.contracting

/-- **`V` solves the Bellman equation** (SL Thm 4.6), with the max attained:
`V(x) = max_{y ∈ Γ(x)} [F(x, y) + β V(y)]`. -/
theorem bellman_equation (x : X) :
    IsGreatest ((fun y => P.F x y + P.β * P.value y) '' P.Γ x) (P.value x) := by
  have h := P.isGreatest_bellmanOp P.value x
  rwa [P.bellmanOp_value] at h

/-- **Uniqueness** (SL Thm 4.6): `V` is the only bounded continuous function
solving the Bellman equation. -/
theorem value_unique (w : X →ᵇ ℝ)
    (hw : ∀ x, IsGreatest ((fun y => P.F x y + P.β * w y) '' P.Γ x) (w x)) :
    w = P.value := by
  have hfix : P.bellmanOp w = w := by
    ext x
    exact (P.isGreatest_bellmanOp w x).unique (hw x)
  exact ContractingWith.fixedPoint_unique P.contracting hfix

/-- **Value-function iteration converges** (SL Thm 4.6 / 3.2): from any
bounded continuous initial guess `v₀`, `T^n v₀ → V` uniformly, with error at
most `β^n ‖v₀ - T v₀‖ / (1 - β)`. -/
theorem iterate_converges (v₀ : X →ᵇ ℝ) :
    Tendsto (fun n => P.bellmanOp^[n] v₀) atTop (𝓝 P.value) ∧
      ∀ n, dist (P.bellmanOp^[n] v₀) P.value ≤ dist v₀ (P.bellmanOp v₀) * P.β ^ n / (1 - P.β) :=
  ⟨ContractingWith.tendsto_iterate_fixedPoint P.contracting v₀,
    ContractingWith.apriori_dist_iterate_fixedPoint_le P.contracting v₀⟩

/-! ### The policy correspondence (SL Thm 4.6) -/

/-- The **optimal policy correspondence**
`G(x) = {y ∈ Γ(x) | F(x, y) + β V(y) ≥ F(x, y') + β V(y') ∀ y' ∈ Γ(x)}`. -/
noncomputable def policy (x : X) : Set X := argmax (P.objective P.value) P.Γ x

/-- `y` is an optimal choice at `x` iff it is feasible and attains `V(x)`. -/
theorem mem_policy_iff {x y : X} :
    y ∈ P.policy x ↔ y ∈ P.Γ x ∧ P.F x y + P.β * P.value y = P.value x := by
  have hg := P.bellman_equation x
  constructor
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, le_antisymm (hg.2 ⟨y, hy, rfl⟩) ?_⟩
    obtain ⟨y₀, hy₀, he⟩ := hg.1
    rw [← he]; exact hmax y₀ hy₀
  · rintro ⟨hy, he⟩
    refine ⟨hy, fun y' hy' => ?_⟩
    show P.objective P.value x y' ≤ P.objective P.value x y
    rw [objective, objective, he]
    exact hg.2 ⟨y', hy', rfl⟩

theorem policy_subset (x : X) : P.policy x ⊆ P.Γ x := fun _ hy => hy.1

/-- **SL Thm 4.6**: the policy correspondence has nonempty compact values and
is upper hemicontinuous (Berge's maximum theorem). -/
theorem policy_nonempty_compact_uhc :
    (∀ x, (P.policy x).Nonempty ∧ IsCompact (P.policy x)) ∧ UpperHemicontinuous P.policy :=
  ⟨fun x => ⟨argmax_nonempty (P.continuous_objective _) (P.Γ_nonempty x) (P.Γ_compact x),
      isCompact_argmax (P.continuous_objective _) (P.Γ_nonempty x) (P.Γ_compact x)⟩,
    upperHemicontinuous_argmax (P.continuous_objective _) P.Γ_continuous P.Γ_nonempty
      P.Γ_compact⟩

theorem policy_nonempty (x : X) : (P.policy x).Nonempty :=
  (P.policy_nonempty_compact_uhc.1 x).1

/-- If the optimal choice is unique at every state, the policy function is
continuous (SL Thm 4.6 / Berge). -/
theorem continuous_policy_of_singleton {g : X → X} (hg : ∀ x, P.policy x = {g x}) :
    Continuous g :=
  continuous_of_argmax_eq_singleton (P.continuous_objective _) P.Γ_continuous P.Γ_nonempty
    P.Γ_compact hg

/-! ### The principle of optimality (SL Thms 4.2–4.5)

For bounded `F` the discounted payoff of any feasible plan is an absolutely
convergent series, so we can use `∑'` honestly. -/

/-- The discounted payoff `Σ_t β^t F(x_t, x_{t+1})` of a plan. Meaningful for
feasible plans, where the series converges (`summable_payoff`). -/
noncomputable def payoff (x : ℕ → X) : ℝ := ∑' t, P.β ^ t * P.F (x t) (x (t + 1))

theorem summable_payoff {x₀ : X} {x : ℕ → X} (hx : IsFeasiblePlan P.Γ x₀ x) :
    Summable fun t => P.β ^ t * P.F (x t) (x (t + 1)) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one P.β_pos.le P.β_lt_one).mul_left P.bound) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t), mul_comm]
  exact mul_le_mul_of_nonneg_right (P.abs_F_le (hx.2 t)) (pow_pos P.β_pos t).le

theorem tendsto_partialPayoff {x₀ : X} {x : ℕ → X} (hx : IsFeasiblePlan P.Γ x₀ x) :
    Tendsto (partialPayoff P.F P.β x) atTop (𝓝 (P.payoff x)) :=
  (P.summable_payoff hx).hasSum.tendsto_sum_nat

/-- `β^n V(x_n) → 0` along any sequence, because `V` is bounded. -/
theorem tendsto_discounted_value (x : ℕ → X) :
    Tendsto (fun n => P.β ^ n * P.value (x n)) atTop (𝓝 0) := by
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one P.β_pos.le P.β_lt_one).mul_const
    ‖P.value‖
  rw [zero_mul] at hg
  refine squeeze_zero_norm (fun n => ?_) hg
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos n)]
  exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact P.value.norm_coe_le_norm _)
    (pow_pos P.β_pos n).le

theorem bellman_le {x y : X} (hy : y ∈ P.Γ x) : P.F x y + P.β * P.value y ≤ P.value x :=
  (P.bellman_equation x).2 ⟨y, hy, rfl⟩

/-- **No feasible plan beats `V`** (SL Thm 4.3, bounded case). -/
theorem payoff_le_value {x₀ : X} {x : ℕ → X} (hx : IsFeasiblePlan P.Γ x₀ x) :
    P.payoff x ≤ P.value x₀ := by
  have hlim : Tendsto (fun n => P.value x₀ - P.β ^ n * P.value (x n)) atTop
      (𝓝 (P.value x₀)) := by
    simpa using (tendsto_const_nhds (x := P.value x₀)).sub (P.tendsto_discounted_value x)
  refine le_of_tendsto_of_tendsto' (P.tendsto_partialPayoff hx) hlim fun n => ?_
  have := partialPayoff_add_le P.β_pos.le (v := P.value) (fun t => P.bellman_le (hx.2 t)) n
  rw [hx.1] at this
  linarith

/-- **Plans that follow the policy attain `V`** (SL Thm 4.4, bounded case). -/
theorem payoff_eq_value_of_policy {x₀ : X} {x : ℕ → X} (hx : IsFeasiblePlan P.Γ x₀ x)
    (hpol : ∀ t, x (t + 1) ∈ P.policy (x t)) : P.payoff x = P.value x₀ := by
  have heq : ∀ n, partialPayoff P.F P.β x n = P.value x₀ - P.β ^ n * P.value (x n) := by
    intro n
    have := partialPayoff_add_eq (F := P.F) (v := P.value)
      (fun t => (P.mem_policy_iff.1 (hpol t)).2) n
    rw [hx.1] at this
    linarith
  have hlim : Tendsto (partialPayoff P.F P.β x) atTop (𝓝 (P.value x₀)) := by
    have := (tendsto_const_nhds (x := P.value x₀)).sub (P.tendsto_discounted_value x)
    rw [sub_zero] at this
    exact this.congr fun n => (heq n).symm
  exact tendsto_nhds_unique (P.tendsto_partialPayoff hx) hlim

/-- **Optimal plans follow the policy** (SL Thm 4.5, bounded case): if a
feasible plan attains `V(x₀)`, then `x_{t+1} ∈ G(x_t)` at every date. -/
theorem policy_of_payoff_eq_value {x₀ : X} {x : ℕ → X} (hx : IsFeasiblePlan P.Γ x₀ x)
    (hopt : P.payoff x = P.value x₀) : ∀ t, x (t + 1) ∈ P.policy (x t) := by
  -- Cumulative discounted Bellman gaps `G_n = Σ_{t<n} β^t gap_t ≥ 0`.
  set gap : ℕ → ℝ := fun t => P.value (x t) - P.F (x t) (x (t + 1)) - P.β * P.value (x (t + 1))
  have hgap : ∀ t, 0 ≤ gap t := fun t => by
    have := P.bellman_le (hx.2 t); simp only [gap]; linarith
  set G : ℕ → ℝ := fun n => ∑ t ∈ range n, P.β ^ t * gap t
  have hG : ∀ n, G n = P.value x₀ - partialPayoff P.F P.β x n - P.β ^ n * P.value (x n) := by
    intro n
    have := telescope P.F P.β P.value x n
    rw [hx.1] at this
    simp only [G, gap]; linarith
  -- `G` is nondecreasing and tends to `V(x₀) - payoff = 0`, so it is `≤ 0`.
  have hmono : Monotone G := monotone_nat_of_le_succ fun n => by
    simp only [G, sum_range_succ]
    linarith [mul_nonneg (pow_pos P.β_pos n).le (hgap n)]
  have hlim : Tendsto G atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := P.value x₀)).sub (P.tendsto_partialPayoff hx)).sub
      (P.tendsto_discounted_value x)
    rw [hopt, sub_self, sub_zero] at this
    exact this.congr fun n => (hG n).symm
  intro t
  have h1 : G (t + 1) ≤ 0 := hmono.ge_of_tendsto hlim (t + 1)
  have h2 : 0 ≤ G t := sum_nonneg fun s _ => mul_nonneg (pow_pos P.β_pos s).le (hgap s)
  have h3 : G (t + 1) = G t + P.β ^ t * gap t := sum_range_succ _ _
  have h4 : P.β ^ t * gap t = 0 := le_antisymm (by linarith)
    (mul_nonneg (pow_pos P.β_pos t).le (hgap t))
  have h5 : gap t = 0 := (mul_eq_zero.1 h4).resolve_left (pow_pos P.β_pos t).ne'
  refine P.mem_policy_iff.2 ⟨hx.2 t, ?_⟩
  simp only [gap] at h5
  linarith

/-- A plan that follows a selection from the policy correspondence. -/
noncomputable def policyPlan (x₀ : X) : ℕ → X :=
  planOf (fun x => (P.policy_nonempty x).some) x₀

theorem policyPlan_spec (x₀ : X) :
    IsFeasiblePlan P.Γ x₀ (P.policyPlan x₀) ∧
      ∀ t, P.policyPlan x₀ (t + 1) ∈ P.policy (P.policyPlan x₀ t) := by
  have hsel : ∀ x, (P.policy_nonempty x).some ∈ P.policy x := fun x => (P.policy_nonempty x).some_mem
  exact ⟨isFeasiblePlan_planOf (fun x => P.policy_subset x (hsel x)) x₀,
    fun t => by rw [policyPlan, planOf_succ]; exact hsel _⟩

/-- **Principle of optimality** (SL Thms 4.2–4.5, bounded case).
`V(x₀)` is the *maximum* discounted payoff over feasible plans from `x₀`
(the sequence-problem value `v*` exists, equals `V`, and is attained); and a
feasible plan attains it iff it follows the policy correspondence. -/
theorem principle_of_optimality (x₀ : X) :
    IsGreatest {u | ∃ x, IsFeasiblePlan P.Γ x₀ x ∧ P.payoff x = u} (P.value x₀) ∧
      ∀ x, IsFeasiblePlan P.Γ x₀ x →
        (P.payoff x = P.value x₀ ↔ ∀ t, x (t + 1) ∈ P.policy (x t)) := by
  refine ⟨⟨⟨P.policyPlan x₀, (P.policyPlan_spec x₀).1,
      P.payoff_eq_value_of_policy (P.policyPlan_spec x₀).1 (P.policyPlan_spec x₀).2⟩, ?_⟩,
    fun x hx => ⟨P.policy_of_payoff_eq_value hx, P.payoff_eq_value_of_policy hx⟩⟩
  rintro u ⟨x, hx, rfl⟩
  exact P.payoff_le_value hx

/-- The bounded theory agrees with the general sequence-problem notion of
`SequenceProblem.lean`: `V(x₀)` is the optimal value in the partial-sum sense
(via the general `verification` theorem). -/
theorem isOptimalValue_value (x₀ : X) : IsOptimalValue P.Γ P.F P.β x₀ (P.value x₀) := by
  set g := fun x => (P.policy_nonempty x).some
  have hg : ∀ x, g x ∈ P.policy x := fun x => (P.policy_nonempty x).some_mem
  refine (verification (Γ := P.Γ) (F := P.F) (v := P.value) (S := univ) (g := g) P.β_pos.le (fun _ _ => subset_univ _)
    (fun x _ y hy => P.bellman_le hy) (fun x _ => P.mem_policy_iff.1 (hg x))
    (fun x₀ _ x _ ε hε => ?_) (fun x₀ _ ε hε => ?_) (mem_univ x₀)).1
  · filter_upwards [(P.tendsto_discounted_value x).eventually
      (Ioo_mem_nhds (by linarith : -ε < 0) hε)] with n hn using hn.1.le
  · filter_upwards [(P.tendsto_discounted_value (planOf g x₀)).eventually
      (Ioo_mem_nhds (by linarith : -ε < 0) hε)] with n hn using hn.2.le

/-! ### Monotonicity of the value function (SL Thm 4.7) -/

/-- **SL Thm 4.7 (weak form)**: if `F(·, y)` is nondecreasing in the state and
`Γ` is monotone (`x ≤ x'` ⇒ `Γ(x) ⊆ Γ(x')`), then `V` is nondecreasing. -/
theorem value_monotone [Preorder X]
    (hF : ∀ x x' y, x ≤ x' → y ∈ P.Γ x → P.F x y ≤ P.F x' y)
    (hΓ : ∀ x x', x ≤ x' → P.Γ x ⊆ P.Γ x') : Monotone P.value := by
  intro x x' hxx'
  obtain ⟨y, hy, he⟩ := (P.bellman_equation x).1
  rw [← he]
  have := P.bellman_le (hΓ x x' hxx' hy)
  linarith [hF x x' y hxx' hy]

/-- **SL Thm 4.7**: if `F(·, y)` is strictly increasing in the state and `Γ`
is monotone, then `V` is strictly increasing. -/
theorem value_strictMono [Preorder X]
    (hF : ∀ x x' y, x < x' → y ∈ P.Γ x → P.F x y < P.F x' y)
    (hΓ : ∀ x x', x ≤ x' → P.Γ x ⊆ P.Γ x') : StrictMono P.value := by
  intro x x' hxx'
  obtain ⟨y, hy, he⟩ := (P.bellman_equation x).1
  rw [← he]
  have := P.bellman_le (hΓ x x' hxx'.le hy)
  linarith [hF x x' y hxx' hy]

end DynProg

end Econ
