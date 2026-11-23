/-
# Stochastic dynamic programming with a finite Markov shock

Stokey–Lucas (SL) ch. 9 (Thms 9.6–9.8), specialised to a finite shock space;
Ljungqvist–Sargent ch. 3–4.

**The economics.** The state is `(x, z)`: an endogenous state `x` (capital,
assets) and an exogenous shock `z` (productivity, income) that follows a
finite Markov chain with transition matrix `Q(z, z')`. Given `(x, z)` the agent
picks `y ∈ Γ(x, z)`, earns `F(x, y, z)`, and tomorrow's state is `(y, z')`
with probability `Q(z, z')`. The Bellman equation is

  `v(x, z) = max_{y ∈ Γ(x, z)} [F(x, y, z) + β Σ_{z'} Q(z, z') v(y, z')]`.

**Assumptions** (SL Assumptions 9.4–9.5 with finite `Z`): `Z` finite (with
the discrete topology, so the Feller property of `Q` is automatic), `Q` a
stochastic matrix, `Γ` nonempty, compact-valued and continuous on `X × Z`,
`F` continuous and bounded, `0 < β < 1`.

**Results** (SL Thm 9.6): the stochastic Bellman operator is a contraction
(Blackwell), so there is a unique bounded continuous `V` on `X × Z` solving
the Bellman equation, value iteration converges to it, and the optimal policy
correspondence has nonempty compact values and is UHC (Berge).

**Documented deviations.** `Z` is finite (SL: a compact metric space with a
Feller kernel; the general case needs measurable selections, PLAN F10). `F`
continuous on `(X × Z) × X` (SL: on the graph). The sequence-problem side
(contingent plans, SL Thm 9.2–9.5: `V` equals the supremum of expected
discounted payoffs) is not yet formalized, so `value` is characterised here
only as the unique bounded continuous solution of the Bellman equation.
-/
module

public import EconLean.Macro.DP.Bellman

@[expose] public section

namespace Econ

open BoundedContinuousFunction Filter Topology Set Finset

/-- A **stochastic dynamic program** with finite Markov shocks, satisfying
SL Assumptions 9.4–9.5 (finite `Z`). -/
structure StochDynProg (X Z : Type*) [TopologicalSpace X] [TopologicalSpace Z]
    [DiscreteTopology Z] [Fintype Z] where
  /-- feasibility: `y ∈ Γ (x, z)` -/
  Γ : X × Z → Set X
  /-- one-period return `F((x, z), y)` -/
  F : X × Z → X → ℝ
  /-- Markov transition matrix of the shock -/
  Q : Z → Z → ℝ
  β : ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1
  β_pos : 0 < β
  β_lt_one : β < 1
  Γ_nonempty : ∀ s, (Γ s).Nonempty
  Γ_compact : ∀ s, IsCompact (Γ s)
  Γ_continuous : ContinuousCorrespondence Γ
  F_continuous : Continuous (Function.uncurry F)
  F_bounded : ∃ M, ∀ s, ∀ y ∈ Γ s, |F s y| ≤ M

namespace StochDynProg

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] [DiscreteTopology Z]
  [Fintype Z] (P : StochDynProg X Z)

/-- Expected continuation value `E[v(y, z') | z] = Σ_{z'} Q(z, z') v(y, z')`. -/
def expect (v : X × Z →ᵇ ℝ) (z : Z) (y : X) : ℝ := ∑ z', P.Q z z' * v (y, z')

/-- Right-hand side of the stochastic Bellman equation. -/
def objective (v : X × Z →ᵇ ℝ) (s : X × Z) (y : X) : ℝ := P.F s y + P.β * P.expect v s.2 y

theorem continuous_objective (v : X × Z →ᵇ ℝ) :
    Continuous (Function.uncurry (P.objective v)) := by
  show Continuous fun p : (X × Z) × X => P.F p.1 p.2 + P.β * ∑ z', P.Q p.1.2 z' * v (p.2, z')
  refine P.F_continuous.add (continuous_const.mul (continuous_finsetSum _ fun z' _ => ?_))
  exact ((continuous_of_discreteTopology (f := fun z => P.Q z z')).comp
    (continuous_snd.comp continuous_fst)).mul (v.continuous.comp (continuous_snd.prodMk continuous_const))

noncomputable def bound : ℝ := Classical.choose P.F_bounded

theorem abs_F_le {s : X × Z} {y : X} (hy : y ∈ P.Γ s) : |P.F s y| ≤ P.bound :=
  Classical.choose_spec P.F_bounded s y hy

/-- `|E[v | z]| ≤ ‖v‖`, since `Q(z, ·)` is a probability vector. -/
theorem abs_expect_le (v : X × Z →ᵇ ℝ) (z : Z) (y : X) : |P.expect v z y| ≤ ‖v‖ := by
  unfold expect
  calc |∑ z', P.Q z z' * v (y, z')| ≤ ∑ z', |P.Q z z' * v (y, z')| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ z', P.Q z z' * ‖v‖ := sum_le_sum fun z' _ => by
        rw [abs_mul, abs_of_nonneg (P.Q_nonneg z z')]
        exact mul_le_mul_of_nonneg_left
          (by rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm _) (P.Q_nonneg z z')
    _ = ‖v‖ := by rw [← sum_mul, P.Q_sum, one_mul]

theorem isGreatest_objective (v : X × Z →ᵇ ℝ) (s : X × Z) :
    IsGreatest (P.objective v s '' P.Γ s) (maxValue (P.objective v) P.Γ s) :=
  isGreatest_maxValue (P.continuous_objective v) (P.Γ_nonempty s) (P.Γ_compact s)

/-- The **stochastic Bellman operator**
`(T v)(x, z) = max_{y ∈ Γ(x, z)} [F(x, y, z) + β Σ_{z'} Q(z, z') v(y, z')]`. -/
noncomputable def bellmanOp (v : X × Z →ᵇ ℝ) : X × Z →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (maxValue (P.objective v) P.Γ)
    (continuous_maxValue (P.continuous_objective v) P.Γ_continuous P.Γ_nonempty P.Γ_compact)
    (P.bound + P.β * ‖v‖) (fun s => by
      obtain ⟨y, hy, he⟩ := (P.isGreatest_objective v s).1
      rw [← he, Real.norm_eq_abs, objective]
      have h1 := P.abs_F_le hy
      have h2 := P.abs_expect_le v s.2 y
      have hβ := P.β_pos.le
      calc |P.F s y + P.β * P.expect v s.2 y| ≤ |P.F s y| + |P.β * P.expect v s.2 y| :=
            abs_add_le _ _
        _ = |P.F s y| + P.β * |P.expect v s.2 y| := by rw [abs_mul, abs_of_pos P.β_pos]
        _ ≤ P.bound + P.β * ‖v‖ := by gcongr)

theorem isGreatest_bellmanOp (v : X × Z →ᵇ ℝ) (s : X × Z) :
    IsGreatest ((fun y => P.F s y + P.β * ∑ z', P.Q s.2 z' * v (y, z')) '' P.Γ s)
      (P.bellmanOp v s) :=
  P.isGreatest_objective v s

/-- **The stochastic Bellman operator is a contraction** (Blackwell). -/
theorem contracting : ContractingWith ⟨P.β, P.β_pos.le⟩ P.bellmanOp := by
  refine blackwell P.β_pos.le P.β_lt_one _ (fun f g hfg s => ?_) (fun f a ha s => ?_)
  · obtain ⟨y, hy, he⟩ := (P.isGreatest_bellmanOp f s).1
    rw [← he]
    refine le_trans ?_ ((P.isGreatest_bellmanOp g s).2 ⟨y, hy, rfl⟩)
    have hE : ∑ z', P.Q s.2 z' * f (y, z') ≤ ∑ z', P.Q s.2 z' * g (y, z') :=
      sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (hfg _) (P.Q_nonneg _ _)
    have := P.β_pos
    simp only; nlinarith
  · obtain ⟨y, hy, he⟩ := (P.isGreatest_bellmanOp (f + const (X × Z) a) s).1
    rw [← he]
    have := (P.isGreatest_bellmanOp f s).2 ⟨y, hy, rfl⟩
    have hE : ∑ z', P.Q s.2 z' * (f + const (X × Z) a) (y, z') =
        ∑ z', P.Q s.2 z' * f (y, z') + a := by
      simp only [add_apply, const_apply, mul_add, sum_add_distrib, ← sum_mul, P.Q_sum, one_mul]
    simp only at this ⊢
    rw [hE]
    linarith

/-- The **value function** of the stochastic program. -/
noncomputable def value : X × Z →ᵇ ℝ := ContractingWith.fixedPoint P.bellmanOp P.contracting

/-- **`V` solves the stochastic Bellman equation** (SL Thm 9.6), max attained. -/
theorem bellman_equation (s : X × Z) :
    IsGreatest ((fun y => P.F s y + P.β * ∑ z', P.Q s.2 z' * P.value (y, z')) '' P.Γ s)
      (P.value s) := by
  have h := P.isGreatest_bellmanOp P.value s
  rwa [show P.bellmanOp P.value = P.value from
    ContractingWith.fixedPoint_isFixedPt P.contracting] at h

/-- **Uniqueness** (SL Thm 9.6): `V` is the only bounded continuous solution. -/
theorem value_unique (w : X × Z →ᵇ ℝ)
    (hw : ∀ s, IsGreatest ((fun y => P.F s y + P.β * ∑ z', P.Q s.2 z' * w (y, z')) '' P.Γ s)
      (w s)) : w = P.value := by
  have hfix : P.bellmanOp w = w := by
    ext s
    exact (P.isGreatest_bellmanOp w s).unique (hw s)
  exact ContractingWith.fixedPoint_unique P.contracting hfix

/-- **Value iteration converges** geometrically (SL Thm 9.6). -/
theorem iterate_converges (v₀ : X × Z →ᵇ ℝ) :
    Tendsto (fun n => P.bellmanOp^[n] v₀) atTop (𝓝 P.value) ∧
      ∀ n, dist (P.bellmanOp^[n] v₀) P.value ≤ dist v₀ (P.bellmanOp v₀) * P.β ^ n / (1 - P.β) :=
  ⟨ContractingWith.tendsto_iterate_fixedPoint P.contracting v₀,
    ContractingWith.apriori_dist_iterate_fixedPoint_le P.contracting v₀⟩

/-- The optimal **policy correspondence** `G(x, z)`. -/
noncomputable def policy (s : X × Z) : Set X := argmax (P.objective P.value) P.Γ s

/-- **SL Thm 9.6 (policy)**: nonempty compact values, UHC in `(x, z)`. -/
theorem policy_nonempty_compact_uhc :
    (∀ s, (P.policy s).Nonempty ∧ IsCompact (P.policy s)) ∧ UpperHemicontinuous P.policy :=
  ⟨fun s => ⟨argmax_nonempty (P.continuous_objective _) (P.Γ_nonempty s) (P.Γ_compact s),
      isCompact_argmax (P.continuous_objective _) (P.Γ_nonempty s) (P.Γ_compact s)⟩,
    upperHemicontinuous_argmax (P.continuous_objective _) P.Γ_continuous P.Γ_nonempty
      P.Γ_compact⟩

end StochDynProg

end Econ
