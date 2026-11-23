/-
# Stochastic savings problems: the income fluctuation problem and stochastic growth

Chamberlain–Wilson (2000), Aiyagari (1994) §II, Huggett (1993) (the
household problem); Brock–Mirman (1972) and Stokey–Lucas (SL) §10.1, §13.3
(stochastic one-sector growth); Ljungqvist–Sargent ch. 18.

One structure covers both models. The state is a stock `k ∈ [0, k̄]` (assets
or capital) and a shock `z` from a finite Markov chain `Q`. **Cash on hand**
`h(k, z) ≥ 0` is split between consumption and next period's stock:

  `max E Σ_t β^t u(c_t)`  s.t.  `c_t + k_{t+1} = h(k_t, z_t)`, `c_t ≥ 0`, `k_{t+1} ∈ [0, k̄]`.

* **Income fluctuation problem** (Aiyagari household): `h(a, z) = R a + y(z)`,
  where `R` is the gross return and `y(z) ≥ 0` is labour income. The borrowing
  limit is `a ≥ 0`.
* **Stochastic growth** (Brock–Mirman): `h(k, z) = z f(k)`.

**Assumptions.** `u` is continuous, nondecreasing and strictly concave on `[0, ∞)`.
Each `h(·, z)` is continuous, nonnegative and concave on `[0, ∞)`.

**Results.**
* The model is a `StochDynProg`, so the value function exists and is unique,
  and value iteration converges (SL Thm 9.6). The expected-utility sequence
  problem is solved by the policy (`StochasticPlan`).
* `V(·, z)` is concave. The optimal savings rule `k' = g(k, z)` is a unique,
  continuous function.
* **Existence of a stationary distribution** of `(k, z)` under the optimal rule
  (SL Thm 12.10; for the income fluctuation problem, the stationary wealth
  distribution in Aiyagari's model).

**Documented deviations.**
* *Bounded assets.* The asset space `[0, k̄]` is imposed. In Aiyagari's model
  with `βR < 1`, Schechtman–Escudero (1977) and Chamberlain–Wilson (2000)
  derive an endogenous upper bound. That derivation needs curvature conditions
  on `u` and is not formalised. For stochastic growth with `z f(k) ≤ k̄` on
  `[0, k̄]` the bound is not binding (see the example).
* `u` is finite and continuous at `0` (bounded DP), as in `Ramsey.lean`. This
  rules out log or CRRA `σ ≥ 1` utility.
* **Existence only, possibly degenerate.** The theorem asserts that *some*
  invariant distribution exists. When `h(0, z) = 0`, as in stochastic growth,
  the point mass at zero capital (times the stationary shock law) is invariant,
  so the statement holds trivially there. For the income fluctuation problem,
  mass at the borrowing limit is economically genuine, but the theorem does not
  rule out that all mass sits there. Open: the non-degenerate ergodic set for
  stochastic growth (Brock–Mirman; SL Thms 13.3–13.5, which needs `g(k, z) > k`
  near `0`), and uniqueness and stability of the stationary distribution
  (Hopenhayn–Prescott, SL Thm 12.12).
-/
module

public import EconLean.Macro.DP.StationaryDist
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- A stochastic savings problem: cash on hand `h(k, z)` is split between
consumption and next period's stock `k' ∈ [0, k̄]`. -/
structure StochSavings (Z : Type*) [Fintype Z] where
  u : ℝ → ℝ
  h : ℝ → Z → ℝ
  Q : Z → Z → ℝ
  β : ℝ
  kbar : ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1
  β_pos : 0 < β
  β_lt_one : β < 1
  kbar_pos : 0 < kbar
  u_continuous : Continuous u
  u_mono : MonotoneOn u (Ici 0)
  u_strictConcave : StrictConcaveOn ℝ (Ici 0) u
  h_continuous : ∀ z, Continuous fun k => h k z
  h_nonneg : ∀ z k, 0 ≤ k → 0 ≤ h k z
  h_concave : ∀ z, ConcaveOn ℝ (Ici 0) fun k => h k z

namespace StochSavings

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] (M : StochSavings Z)

/-- The state space `[0, k̄]`. -/
abbrev S : Set ℝ := Icc 0 M.kbar

/-- Feasible next-period stocks: `0 ≤ k' ≤ min(k̄, h(k, z))`. -/
def Γ (s : M.S × Z) : Set M.S := {y | (y : ℝ) ≤ M.h s.1 s.2}

/-- The return: utility of consumption `c = h(k, z) - k'`. -/
def F (s : M.S × Z) (y : M.S) : ℝ := M.u (M.h s.1 s.2 - y)

theorem continuous_h : Continuous fun s : M.S × Z => M.h s.1 s.2 :=
  continuous_prod_of_discrete_right.2 fun z => (M.h_continuous z).comp continuous_subtype_val

theorem Γ_isClosed_graph : IsClosed (graph M.Γ) :=
  isClosed_le (continuous_subtype_val.comp continuous_snd) (M.continuous_h.comp continuous_fst)

theorem Γ_lhc : LowerHemicontinuous M.Γ := by
  refine fun s => lowerHemicontinuousAt_iff_textbook.2 ?_
  rintro U hU ⟨y, hyΓ, hyU⟩
  let g : M.S × Z → M.S := fun s' => ⟨min (y : ℝ) (M.h s'.1 s'.2),
    le_min y.2.1 (M.h_nonneg _ _ s'.1.2.1), (min_le_left _ _).trans y.2.2⟩
  have hc : Continuous g := (continuous_const.min M.continuous_h).subtype_mk _
  have hs : g s = y := Subtype.ext (min_eq_left hyΓ)
  filter_upwards [(hc.tendsto s).eventually (hU.mem_nhds (hs ▸ hyU))] with s' hs'
  exact ⟨g s', (min_le_right _ _ : min (y : ℝ) (M.h s'.1 s'.2) ≤ M.h s'.1 s'.2), hs'⟩

/-- The model is a stochastic dynamic program (SL Assumptions 9.4–9.7). -/
noncomputable def toStochDynProg : StochDynProg M.S Z where
  Γ := M.Γ
  F := M.F
  Q := M.Q
  β := M.β
  Q_nonneg := M.Q_nonneg
  Q_sum := M.Q_sum
  β_pos := M.β_pos
  β_lt_one := M.β_lt_one
  Γ_nonempty := fun s => ⟨⟨0, le_rfl, M.kbar_pos.le⟩, M.h_nonneg _ _ s.1.2.1⟩
  Γ_compact := fun s => (isClosed_le continuous_subtype_val continuous_const).isCompact
  Γ_continuous := ⟨upperHemicontinuous_of_isClosed_graph M.Γ_isClosed_graph, M.Γ_lhc⟩
  F_continuous := M.u_continuous.comp
    ((M.continuous_h.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd))
  F_bounded := by
    obtain ⟨H, hH⟩ := (isCompact_univ.image M.continuous_h).isBounded.subset_closedBall 0
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (M.u_continuous.continuousOn (s := Icc 0 H))
    refine ⟨C, fun s y hy => ?_⟩
    have hy' : (y : ℝ) ≤ M.h s.1 s.2 := hy
    have hHs : M.h s.1 s.2 ≤ H := by
      have := hH ⟨s, trivial, rfl⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this
    have := hC (M.h s.1 s.2 - y) ⟨sub_nonneg.2 hy', by linarith [y.2.1]⟩
    rw [Real.norm_eq_abs] at this
    exact this

theorem convexTech : M.toStochDynProg.ConvexTech := by
  intro z k y k' y' w v hy hy' a b ha hb hab hw hv
  simp only [smul_eq_mul] at hw hv
  show (v : ℝ) ≤ M.h w z
  have hy1 : (y : ℝ) ≤ M.h k z := hy
  have hy2 : (y' : ℝ) ≤ M.h k' z := hy'
  have hc := (M.h_concave z).2 (show (k : ℝ) ∈ Ici 0 from k.2.1)
    (show (k' : ℝ) ∈ Ici 0 from k'.2.1) ha.le hb.le hab
  simp only [smul_eq_mul] at hc
  rw [hv, hw]
  nlinarith

theorem concaveRet : M.toStochDynProg.ConcaveRet := by
  intro z k y k' y' w v hy hy' a b ha hb hab hw hv
  simp only [smul_eq_mul] at hw hv
  show a * M.u (M.h k z - y) + b * M.u (M.h k' z - y') ≤ M.u (M.h w z - v) ∧
    (k = k' → y ≠ y' → a * M.u (M.h k z - y) + b * M.u (M.h k' z - y') < M.u (M.h w z - v))
  have hy1 : (y : ℝ) ≤ M.h k z := hy
  have hy2 : (y' : ℝ) ≤ M.h k' z := hy'
  have hc0 : (0 : ℝ) ≤ M.h k z - y := by linarith
  have hc0' : (0 : ℝ) ≤ M.h k' z - y' := by linarith
  have hhc := (M.h_concave z).2 (show (k : ℝ) ∈ Ici 0 from k.2.1)
    (show (k' : ℝ) ∈ Ici 0 from k'.2.1) ha.le hb.le hab
  simp only [smul_eq_mul] at hhc
  -- consumption at the mixture is at least the mixture of consumptions
  have hmix : a * (M.h k z - y) + b * (M.h k' z - y') ≤ M.h w z - v := by
    rw [hv, hw]; nlinarith
  have hmix0 : 0 ≤ a * (M.h k z - y) + b * (M.h k' z - y') := by positivity
  have hmono := M.u_mono (show _ ∈ Ici (0 : ℝ) from hmix0)
    (show _ ∈ Ici (0 : ℝ) from hmix0.trans hmix) hmix
  have hu := M.u_strictConcave.concaveOn.2 (show _ ∈ Ici (0 : ℝ) from hc0)
    (show _ ∈ Ici (0 : ℝ) from hc0') ha.le hb.le hab
  simp only [smul_eq_mul] at hu
  refine ⟨hu.trans hmono, fun hkk hne => ?_⟩
  subst hkk
  have hne' : M.h k z - y ≠ M.h k z - y' := by
    intro h; exact hne (Subtype.ext (by linarith))
  have hus := M.u_strictConcave.2 (show _ ∈ Ici (0 : ℝ) from hc0)
    (show _ ∈ Ici (0 : ℝ) from hc0') hne' ha hb hab
  simp only [smul_eq_mul] at hus
  exact hus.trans_le hmono

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Existence of a stationary distribution** for the stochastic savings problem
(SL Thm 12.10). The optimal savings rule `k' = g(k, z)` is a unique, continuous
function. The Markov process `k' = g(k, z)`, `z' ~ Q(z, ·)` on `[0, k̄] × Z` has
an invariant probability distribution. For the income fluctuation problem
this is a stationary wealth–income distribution. Existence only: the
distribution may be degenerate (see the module docstring). -/
theorem exists_stationary [Nonempty Z] :
    ∃ g : M.S × Z → M.S, Continuous g ∧ (∀ s, M.toStochDynProg.policy s = {g s}) ∧
      ∃ (hg : Measurable g) (μ : Measure (M.S × Z)), IsProbabilityMeasure μ ∧
        Kernel.Invariant (policyKernel M.Q g hg) μ := by
  have : Nonempty M.S := ⟨⟨0, le_rfl, M.kbar_pos.le⟩⟩
  exact M.toStochDynProg.exists_stationary (convex_Icc 0 M.kbar) isCompact_Icc
    M.convexTech M.concaveRet

end StochSavings

/-! ### Non-vacuity of the hypotheses

Two concrete instances, each with `√` utility and a fair-coin two-state
shock. They show that the assumptions can be met. They do not show
non-degeneracy: in the growth example `h(0, z) = 0`, so the point mass at zero
capital is already invariant. -/

/-- **An Aiyagari household**: `u = √c`, gross return `R = 1`, `β = 9/10`
(so `βR < 1`), income `y ∈ {1/4, 1/2}` i.i.d. with probability 1/2, asset
space `[0, 1]`. -/
noncomputable def StochSavings.aiyagariExample : StochSavings (Fin 2) where
  u := Real.sqrt
  h := fun a z => a + ![1 / 4, 1 / 2] z
  Q := fun _ _ => 1 / 2
  β := 9 / 10
  kbar := 1
  Q_nonneg := fun _ _ => by norm_num
  Q_sum := fun _ => by norm_num [Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  h_continuous := fun _ => continuous_id.add continuous_const
  h_nonneg := fun z k hk => by fin_cases z <;> simp <;> linarith
  h_concave := fun z => (concaveOn_id (convex_Ici 0)).add (concaveOn_const _ (convex_Ici 0))

/-- **Stochastic Brock–Mirman growth**: `u = √c`, `f = √k`, `β = 1/2`,
productivity `z ∈ {1/2, 1}` i.i.d. with probability 1/2, capital space
`[0, 1]`. Here `z √k ≤ 1` on `[0, 1]`, so the bound `k̄ = 1` never binds. -/
noncomputable def StochSavings.brockMirmanExample : StochSavings (Fin 2) where
  u := Real.sqrt
  h := fun k z => ![1 / 2, 1] z * Real.sqrt k
  Q := fun _ _ => 1 / 2
  β := 1 / 2
  kbar := 1
  Q_nonneg := fun _ _ => by norm_num
  Q_sum := fun _ => by norm_num [Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  h_continuous := fun _ => continuous_const.mul Real.continuous_sqrt
  h_nonneg := fun z k _ => by fin_cases z <;> simp
  h_concave := fun z => by
    have hz : 0 ≤ ![1 / 2, (1 : ℝ)] z := by fin_cases z <;> norm_num
    simpa [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.smul hz

/-- The Aiyagari household has a stationary wealth–income distribution under
its (unique, continuous) optimal savings rule. -/
example : ∃ g : StochSavings.aiyagariExample.S × Fin 2 → StochSavings.aiyagariExample.S,
    Continuous g ∧ (∀ s, StochSavings.aiyagariExample.toStochDynProg.policy s = {g s}) ∧
    ∃ (hg : Measurable g) (μ : Measure (StochSavings.aiyagariExample.S × Fin 2)),
      IsProbabilityMeasure μ ∧ Kernel.Invariant (policyKernel (fun _ _ => 1 / 2) g hg) μ :=
  StochSavings.aiyagariExample.exists_stationary

/-- Stochastic growth has a stationary distribution of capital and productivity. -/
example : ∃ g : StochSavings.brockMirmanExample.S × Fin 2 →
      StochSavings.brockMirmanExample.S,
    Continuous g ∧ (∀ s, StochSavings.brockMirmanExample.toStochDynProg.policy s = {g s}) ∧
    ∃ (hg : Measurable g) (μ : Measure (StochSavings.brockMirmanExample.S × Fin 2)),
      IsProbabilityMeasure μ ∧ Kernel.Invariant (policyKernel (fun _ _ => 1 / 2) g hg) μ :=
  StochSavings.brockMirmanExample.exists_stationary

end Econ
