/-
# Aiyagari stationary general equilibrium

Aiyagari (1994); Ljungqvist–Sargent (LS) ch. 18.2; Açıkgöz (2018).

**The economy** (`AiyagariEconomy`). A continuum of households faces
idiosyncratic labor-efficiency shocks `z` following a finite Markov chain `Q`
with a unique invariant distribution `q̄`. A household with assets `a` earns
`(1 + r) a + w e(z)`, where `e(z) ≥ 0` is its efficiency units of labor. It
solves the savings problem of `ParamSavings` (assets capped at `k̄`). A
Cobb–Douglas firm (`CDFirm`) rents capital at `r + δ` and hires labor at `w`.
Aggregate effective labor is `L = Σ_z q̄(z) e(z)`. The wage is the firm's
`w(r)`, so the household family is indexed by `r` alone.

**Stationary recursive competitive equilibrium** (LS Def. 18.2.1): an interest
rate `r`, a wage `w`, a savings policy `g` and a stationary distribution `π` on
`(a, z)` such that
1. `g` is the household's optimal policy at `(r, w)`;
2. the firm maximizes profit: `α (K/L)^{α-1} = r + δ` and `w = (1 - α)(K/L)^α`;
3. the capital market clears: `K = ∫ a dπ`;
4. the labor market clears: `∫ e(z) dπ = L`;
5. `π` is invariant under `g` and `Q`;
6. the goods market clears: `C + δK = Y`, with `C = ∫ c dπ`.

**Results.**
* `marg_isInvariant`: the income-state marginal of *any* stationary
  distribution of the household chain is `Q`-invariant. So with `q̄` unique,
  labor supply is pinned down (item 4).
* `integral_policy_eq`: in a stationary distribution, aggregate next-period
  assets equal aggregate assets (`∫ g dπ = ∫ a dπ`).
* `exists_stationary_equilibrium`: existence of a stationary equilibrium with
  all six conditions. No uniqueness of `π` is assumed.
* `ParamSavings.le_policy`: a one-period-deviation argument giving a lower
  bound `m` on optimal saving in every state. `hhi_of_le_policy` turns it into
  the upper boundary condition.
* `AiyagariEconomy.sqrtEconomy`, `sqrt_equilibrium`: a non-vacuity witness
  (`u = √c`, `β = 9/10`, `α = 1/2`, `δ = 1/10`, `r ∈ [0, 19/10]`) where every
  hypothesis is proved. **Caveat:** it has no income risk (`e ≡ 1`), and since
  supply is at most `k̄ = 1`, any equilibrium has `r ≥ 2/5`, so
  `β(1 + r) > 1` and the cap binds. It is an equilibrium of the *capped*
  economy only, not a textbook Aiyagari equilibrium (which has
  `r < 1/β - 1`).

**Hypotheses (documented).**
* `hlo : k̄ ≤ K_d(r_lo)`. This is **derived** for some `r_lo > -δ` by
  `CDFirm.exists_capDemand_ge`, since capital demand diverges as `r ↓ -δ`.
* `hhi`: at `r_hi` some stationary distribution supplies at least `K_d(r_hi)`.
  In Aiyagari's proof this comes from supply diverging as `β(1 + r) ↑ 1`; that
  limit argument is **not** formalized. Instead `le_policy` +
  `hhi_of_le_policy` give a checkable sufficient condition (households save at
  least `K_d(r_hi)` in every state at `r_hi`), verified in `sqrtEconomy`. In
  that example `β(1 + r_hi) > 1`, so the asset cap is what keeps saving
  bounded at `r_hi`; the equilibrium interest rate itself is not located.
* *The asset cap `k̄`.* It is imposed, not derived, and the conclusion does
  not say the cap is slack. So `exists_stationary_equilibrium` is existence
  for the **economy with an exogenous asset cap `k̄`**; household optimality
  is optimality subject to `a' ≤ k̄`. If the cap binds (as in `sqrtEconomy`),
  the equilibrium is not one of the uncapped economy. Deriving an endogenous
  cap from `β(1 + r) < 1` (Aiyagari 1994, Lemma; SLP ch. 9-style bounds) is
  open.
-/
module

public import EconLean.Macro.HA.Aiyagari
public import EconLean.Macro.HA.CDFirm
public import EconLean.Macro.DP.MarkovChain

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ParamSavings

variable {Θ Z : Type*} [TopologicalSpace Θ] [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z]
  [MeasurableSpace Z] [BorelSpace Z] (M : ParamSavings Θ Z)

/-- A function of the income state, as a bounded continuous function on `[0, k̄] × Z`. -/
noncomputable def zfun (F : Z → ℝ) : M.S × Z →ᵇ ℝ :=
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  BoundedContinuousFunction.mkOfCompact ⟨fun s => F s.2, continuous_of_discreteTopology.comp continuous_snd⟩

/-- The **income-state marginal** of a distribution on `(a, z)`: `μ(Z = z)`. -/
noncomputable def marg [DecidableEq Z] (μ : ProbabilityMeasure (M.S × Z)) (z : Z) : ℝ :=
  ∫ s, M.zfun (fun z' => if z' = z then 1 else 0) s ∂(μ : Measure (M.S × Z))

theorem integral_zfun [DecidableEq Z] (μ : ProbabilityMeasure (M.S × Z)) (F : Z → ℝ) :
    ∫ s, M.zfun F s ∂(μ : Measure (M.S × Z)) = ∑ z, F z * M.marg μ z := by
  have hF : ∀ s : M.S × Z, M.zfun F s =
      ∑ z, F z * M.zfun (fun z' => if z' = z then 1 else 0) s := fun s => by
    simp [zfun, mul_ite, mul_one, mul_zero]
  simp_rw [hF]
  rw [integral_finsetSum _ fun z _ => ((M.zfun _).integrable _).const_mul _]
  simp_rw [integral_const_mul]
  rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem zfun_apply (F : Z → ℝ) (s : M.S × Z) : M.zfun F s = F s.2 := rfl

/-- **The income marginal of a stationary distribution is `Q`-invariant**, for
any savings policy `g`. -/
theorem marg_isInvariant [DecidableEq Z] (g : M.S × Z → M.S) (hg : Measurable g)
    (μ : ProbabilityMeasure (M.S × Z)) (hμ : Kernel.Invariant (policyKernel M.Q g hg) μ) :
    IsInvariant M.Q (M.marg μ) := by
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  have := isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum g hg
  refine ⟨⟨fun z => integral_nonneg fun s => ?_, ?_⟩, ?_⟩
  · rw [zfun_apply]; split_ifs <;> norm_num
  · have h := M.integral_zfun μ (fun _ => 1)
    simp only [one_mul] at h
    rw [← h]
    simp [zfun_apply]
  · funext z'
    show ∑ z, M.marg μ z * M.Q z z' = M.marg μ z'
    have hμ' : policyKernel M.Q g hg ∘ₘ (μ : Measure (M.S × Z)) = μ := hμ
    have h1 : M.marg μ z' = ∫ s, ∫ y, M.zfun (fun z => if z = z' then 1 else 0) y
        ∂(policyKernel M.Q g hg s) ∂(μ : Measure (M.S × Z)) := by
      rw [← integral_comp_measure ((M.zfun _).integrable _), hμ']
      rfl
    rw [h1]
    simp_rw [integral_policyKernel M.Q_nonneg, zfun_apply]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h2 := M.integral_zfun μ (fun z => M.Q z z')
    simp only [zfun_apply] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- **Aggregate assets are stationary**: under a stationary distribution of the
policy `g`, `∫ g(a, z) dπ = ∫ a dπ`. -/
theorem integral_policy_eq (g : M.S × Z → M.S) (hg : Measurable g)
    (μ : ProbabilityMeasure (M.S × Z)) (hμ : Kernel.Invariant (policyKernel M.Q g hg) μ) :
    ∫ s, ((g s : M.S) : ℝ) ∂(μ : Measure (M.S × Z)) = ∫ s, M.assets s ∂(μ : Measure (M.S × Z)) := by
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  have := isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum g hg
  have hμ' : policyKernel M.Q g hg ∘ₘ (μ : Measure (M.S × Z)) = μ := hμ
  conv_rhs => rw [← hμ']
  rw [integral_comp_measure (M.assets.integrable _)]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  show ((g s : M.S) : ℝ) = ∫ y, M.assets y ∂(policyKernel M.Q g hg s)
  rw [integral_policyKernel M.Q_nonneg]
  show _ = ∑ z', M.Q s.2 z' * ((g s : M.S) : ℝ)
  rw [← Finset.sum_mul, M.Q_sum, one_mul]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **A lower bound on savings from a one-period deviation.** Suppose saving
`m` is always feasible, cash on hand is monotone in assets, and for every
state, every smaller saving `y < m` and every continuation choice `x(z')`
feasible after `y`, the utility cost today of raising saving from `y` to `m`
is strictly below the discounted expected utility gain tomorrow from consuming
the extra cash while keeping the same continuation choice `x`:

  `u(h(a,z) - y) - u(h(a,z) - m) < β Σ_{z'} Q(z,z') [u(h(m,z') - x(z')) - u(h(y,z') - x(z'))]`.

Then the optimal policy saves at least `m` in every state. (Proof: if `y < m`
were optimal, deviating to `m` today and to the original plan's choice
`x(z') = g(y, z')` tomorrow would be strictly better.) -/
theorem le_policy (θ : Θ) (m : M.S) (hm : ∀ s : M.S × Z, (m : ℝ) ≤ M.h θ s.1 s.2)
    (hmono : ∀ z' (a b : M.S), (a : ℝ) ≤ b → M.h θ a z' ≤ M.h θ b z')
    (hgain : ∀ (s : M.S × Z) (y : M.S) (x : Z → M.S), (y : ℝ) < m →
      (∀ z', (x z' : ℝ) ≤ M.h θ y z') →
      M.u (M.h θ s.1 s.2 - y) - M.u (M.h θ s.1 s.2 - m) <
        M.β * ∑ z', M.Q s.2 z' * (M.u (M.h θ m z' - x z') - M.u (M.h θ y z' - x z')))
    {g : M.S × Z → M.S} (hg : ∀ s, (M.slice θ).toStochDynProg.policy s = {g s}) (s : M.S × Z) :
    (m : ℝ) ≤ g s := by
  by_contra hlt
  rw [not_le] at hlt
  set P := (M.slice θ).toStochDynProg
  set y := g s
  let x : Z → M.S := fun z' => g (y, z')
  have hx : ∀ z', (x z' : ℝ) ≤ M.h θ y z' := fun z' =>
    ((hg (y, z')).symm ▸ Set.mem_singleton (g (y, z')) : g (y, z') ∈ P.policy (y, z')).1
  have hys : y ∈ P.policy s := (hg s).symm ▸ Set.mem_singleton _
  have e0 := P.value_eq_of_mem_policy hys
  have g0 := P.value_ge s (y := m) (hm s)
  have e1 : ∀ z', P.F (y, z') (x z') + P.β * ∑ z'', P.Q z' z'' * P.value (x z', z'') =
      P.value (y, z') := fun z' =>
    P.value_eq_of_mem_policy ((hg (y, z')).symm ▸ Set.mem_singleton _)
  have g1 : ∀ z', P.F (m, z') (x z') + P.β * ∑ z'', P.Q z' z'' * P.value (x z', z'') ≤
      P.value (m, z') := fun z' =>
    P.value_ge (m, z') (y := x z') ((hx z').trans (hmono z' y m hlt.le))
  -- tomorrow: `v(m, z') - v(y, z') ≥ F(m, z', x) - F(y, z', x)`
  have hsum : ∑ z', P.Q s.2 z' * (P.F (m, z') (x z') - P.F (y, z') (x z')) ≤
      ∑ z', P.Q s.2 z' * P.value (m, z') - ∑ z', P.Q s.2 z' * P.value (y, z') := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith [e1 z', g1 z']) (M.Q_nonneg _ _)
  have hG := hgain s y x hlt hx
  have hβ := M.β_pos
  have : P.F s y - P.F s m < P.β * ∑ z', P.Q s.2 z' * (P.F (m, z') (x z') - P.F (y, z') (x z')) :=
    hG
  have hP : P.β = M.β := rfl
  rw [hP] at this e0 g0
  nlinarith [mul_le_mul_of_nonneg_left hsum hβ.le]

end ParamSavings

/-- An **Aiyagari economy with an exogenous asset cap `k̄`**: households (`u`, `β`, `Q`, efficiency units `e`,
asset cap `k̄`), a Cobb–Douglas firm, and an interest-rate interval
`[r_lo, r_hi]` with `r_lo > -δ` and `r_lo ≥ -1`. The shock chain has a unique
invariant distribution `q̄` and positive aggregate labor. -/
structure AiyagariEconomy (Z : Type*) [Fintype Z] where
  u : ℝ → ℝ
  Q : Z → Z → ℝ
  β : ℝ
  kbar : ℝ
  e : Z → ℝ
  firm : CDFirm
  rlo : ℝ
  rhi : ℝ
  qbar : Z → ℝ
  Q_nonneg : ∀ z z', 0 ≤ Q z z'
  Q_sum : ∀ z, ∑ z', Q z z' = 1
  β_pos : 0 < β
  β_lt_one : β < 1
  kbar_pos : 0 < kbar
  u_continuous : Continuous u
  u_mono : MonotoneOn u (Ici 0)
  u_strictConcave : StrictConcaveOn ℝ (Ici 0) u
  e_nonneg : ∀ z, 0 ≤ e z
  rlo_gt : -firm.δ < rlo
  rlo_ge : -1 ≤ rlo
  rlo_le : rlo ≤ rhi
  qbar_inv : IsInvariant Q qbar
  qbar_unique : ∀ π, IsInvariant Q π → π = qbar
  labor_pos : 0 < ∑ z, qbar z * e z

namespace AiyagariEconomy

variable {Z : Type*} [Fintype Z] (E : AiyagariEconomy Z)

/-- Aggregate effective labor `L = Σ_z q̄(z) e(z)`. -/
noncomputable def L : ℝ := ∑ z, E.qbar z * E.e z

theorem mem_Ioi {r : Icc E.rlo E.rhi} : (r : ℝ) ∈ Ioi (-E.firm.δ) :=
  lt_of_lt_of_le E.rlo_gt r.2.1

/-- The households' problem: cash on hand `(1 + r) a + w(r) e(z)`. -/
noncomputable def household : ParamSavings (Icc E.rlo E.rhi) Z where
  u := E.u
  h := fun r a z => (1 + r) * a + E.firm.wage r * E.e z
  Q := E.Q
  β := E.β
  kbar := E.kbar
  Q_nonneg := E.Q_nonneg
  Q_sum := E.Q_sum
  β_pos := E.β_pos
  β_lt_one := E.β_lt_one
  kbar_pos := E.kbar_pos
  u_continuous := E.u_continuous
  u_mono := E.u_mono
  u_strictConcave := E.u_strictConcave
  h_continuous := fun z => by
    have hw : Continuous fun r : Icc E.rlo E.rhi => E.firm.wage r :=
      E.firm.continuousOn_wage.comp_continuous continuous_subtype_val fun r => E.mem_Ioi
    exact ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).mul continuous_snd).add
      ((hw.comp continuous_fst).mul continuous_const)
  h_nonneg := fun r z k hk => add_nonneg (mul_nonneg (by linarith [r.2.1, E.rlo_ge]) hk)
    (mul_nonneg (E.firm.wage_pos E.mem_Ioi).le (E.e_nonneg z))
  h_concave := fun r z => ⟨convex_Ici 0, fun x _ y _ a b _ _ hab => by
    simp only [smul_eq_mul]
    exact le_of_eq (by linear_combination (E.firm.wage r * E.e z) * hab)⟩

variable [TopologicalSpace Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]

/-- **Existence of a stationary recursive competitive equilibrium in the
Aiyagari model** (Aiyagari 1994; LS ch. 18.2; existence without uniqueness as
in Açıkgöz 2018). Under the lower boundary condition (derivable via
`CDFirm.exists_capDemand_ge`) and the upper boundary condition `hhi`, there
are an interest rate `r`, the wage `w(r)`, a policy `g` and a stationary
distribution `π` with:
* `g` the optimal savings policy at `r`, and `π` invariant;
* capital market clearing: `K = ∫ a dπ = L k(r)`;
* labor market clearing: `∫ e(z) dπ = L`;
* firm optimality: `α (K/L)^{α-1} = r + δ` and `w(r) = (1 - α)(K/L)^α`;
* goods market clearing: `∫ c dπ + δ K = K^α L^{1-α}`, with
  `c = (1 + r) a + w e(z) - g(a, z)`. -/
theorem exists_stationary_equilibrium [DecidableEq Z]
    (hlo : E.kbar ≤ E.firm.capDemand E.L E.rlo)
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z), Kernel.Invariant (policyKernel E.Q g hg) μ ∧
        E.firm.capDemand E.L E.rhi ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z))) :
    ∃ r : Icc E.rlo E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.firm.capDemand E.L r ∧
      ∫ s, E.e s.2 ∂(π : Measure (E.household.S × Z)) = E.L ∧
      E.firm.α * ((∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) / E.L) ^
        (E.firm.α - 1) = r + E.firm.δ ∧
      E.firm.wage r = (1 - E.firm.α) *
        ((∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) / E.L) ^ E.firm.α ∧
      ∫ s, ((1 + (r : ℝ)) * (s.1 : ℝ) + E.firm.wage r * E.e s.2 - (g s : ℝ))
          ∂(π : Measure (E.household.S × Z)) +
        E.firm.δ * ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) =
        E.firm.output (∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) E.L := by
  have hKd : ContinuousOn (E.firm.capDemand E.L) (Icc E.rlo E.rhi) :=
    (E.firm.continuousOn_capDemand E.L).mono fun r hr => lt_of_lt_of_le E.rlo_gt hr.1
  obtain ⟨r, g, hg, π, hpol, hinv, hK⟩ := ParamSavings.exists_asset_market_clearing E.rlo_le
    E.household (E.firm.capDemand E.L) hKd hlo hhi
  have hr : -E.firm.δ < (r : ℝ) := E.mem_Ioi
  have hL : 0 < E.L := E.labor_pos
  have : CompactSpace E.household.S := isCompact_iff_compactSpace.1 isCompact_Icc
  -- labor market
  have hlab : ∫ s, E.e s.2 ∂(π : Measure (E.household.S × Z)) = E.L := by
    have h1 := E.household.integral_zfun π E.e
    have h2 := E.qbar_unique _ (E.household.marg_isInvariant g hg π hinv)
    simp only [ParamSavings.zfun_apply] at h1
    rw [h1, h2]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  set K := ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))
  have hKL : K / E.L = E.firm.kOfR r := by
    rw [hK, CDFirm.capDemand, mul_div_cancel_left₀ _ hL.ne']
  refine ⟨r, g, hg, π, hpol, hinv, hK, hlab, ?_, ?_, ?_⟩
  · rw [hKL]; exact E.firm.foc_capital hr
  · rw [hKL]; rfl
  · -- goods market: `C = (1 + r) K + w L - K` and zero profit
    have hint1 : Integrable (fun s : E.household.S × Z => (s.1 : ℝ)) (π : Measure _) :=
      E.household.assets.integrable _
    have hint2 : Integrable (fun s : E.household.S × Z => E.e s.2) (π : Measure _) :=
      (E.household.zfun E.e).integrable _
    have hint3 : Integrable (fun s : E.household.S × Z => ((g s : E.household.S) : ℝ))
        (π : Measure _) :=
      integrable_of_bounded (measurable_subtype_coe.comp hg) (fun s => (g s).2.1)
        (fun s => (g s).2.2)
    have hC : ∫ s, ((1 + (r : ℝ)) * (s.1 : ℝ) + E.firm.wage r * E.e s.2 - (g s : ℝ))
        ∂(π : Measure (E.household.S × Z)) = (1 + r) * K + E.firm.wage r * E.L - K := by
      rw [integral_sub (f := fun s : E.household.S × Z =>
          (1 + (r : ℝ)) * (s.1 : ℝ) + E.firm.wage r * E.e s.2)
          ((hint1.const_mul _).add (hint2.const_mul _)) hint3,
        integral_add (f := fun s : E.household.S × Z => (1 + (r : ℝ)) * (s.1 : ℝ))
          (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
        integral_const_mul, hlab, E.household.integral_policy_eq g hg π hinv]
      rfl
    rw [hC]
    simp only [K] at hK ⊢
    rw [hK, ← E.firm.zero_profit hL hr]
    ring

omit [TopologicalSpace Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z] in
theorem household_h (r : Icc E.rlo E.rhi) (a : ℝ) (z : Z) :
    E.household.h r a z = (1 + r) * a + E.firm.wage r * E.e z := rfl

omit [TopologicalSpace Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z] in
theorem household_h_mono (r : Icc E.rlo E.rhi) (z : Z) {a b : ℝ} (hab : a ≤ b) :
    E.household.h r a z ≤ E.household.h r b z := by
  rw [household_h, household_h]
  have : 0 ≤ 1 + (r : ℝ) := by linarith [r.2.1, E.rlo_ge]
  nlinarith

/-- **Upper boundary condition from a savings lower bound.** If at `r_hi`
households always save at least `m ≥ K_d(r_hi)` (for example via
`ParamSavings.le_policy`), then every stationary distribution at `r_hi`
supplies at least `K_d(r_hi)`, so the hypothesis `hhi` of
`exists_stationary_equilibrium` holds. -/
theorem hhi_of_le_policy (m : E.household.S) (hKm : E.firm.capDemand E.L E.rhi ≤ m)
    (hsave : ∀ (g : E.household.S × Z → E.household.S),
      (∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∀ s, (m : ℝ) ≤ g s)
    (g : E.household.S × Z → E.household.S) (hg : Measurable g)
    (hpol : ∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) :
    ∃ μ : ProbabilityMeasure (E.household.S × Z), Kernel.Invariant (policyKernel E.Q g hg) μ ∧
      E.firm.capDemand E.L E.rhi ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)) := by
  obtain ⟨μ, hμ⟩ := E.household.exists_stationary_of_policy _ g hg hpol
  refine ⟨μ, hμ, ?_⟩
  rw [← E.household.integral_policy_eq g hg μ hμ]
  have hint : Integrable (fun s : E.household.S × Z => ((g s : E.household.S) : ℝ))
      (μ : Measure _) :=
    integrable_of_bounded (measurable_subtype_coe.comp hg) (fun s => (g s).2.1)
      (fun s => (g s).2.2)
  calc E.firm.capDemand E.L E.rhi ≤ m := hKm
    _ = ∫ _, (m : ℝ) ∂(μ : Measure (E.household.S × Z)) := by simp
    _ ≤ _ := integral_mono (integrable_const _) hint (hsave g hpol)

end AiyagariEconomy

/-! ### A worked example with positive capital -/

theorem sqrt_sub_le_div {P Q : ℝ} (hQ : 0 < Q) (hPQ : Q ≤ P) :
    Real.sqrt P - Real.sqrt Q ≤ (P - Q) / (2 * Real.sqrt Q) := by
  have hq := Real.sqrt_pos.2 hQ
  have hp2 := Real.sq_sqrt (hQ.le.trans hPQ)
  have hq2 := Real.sq_sqrt hQ.le
  have hpq := Real.sqrt_le_sqrt hPQ
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt P - Real.sqrt Q)]

theorem div_le_sqrt_sub {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) (hA : 0 < A) :
    (A - B) / (2 * Real.sqrt A) ≤ Real.sqrt A - Real.sqrt B := by
  have ha := Real.sqrt_pos.2 hA
  have ha2 := Real.sq_sqrt hA.le
  have hb2 := Real.sq_sqrt hB
  have hab := Real.sqrt_le_sqrt hBA
  have hb0 := Real.sqrt_nonneg B
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]

/-- The Cobb–Douglas firm with `α = 1/2`, `δ = 1/10`. -/
noncomputable def CDFirm.half : CDFirm where
  α := 1 / 2
  δ := 1 / 10
  α_pos := by norm_num
  α_lt_one := by norm_num
  δ_nonneg := by norm_num

theorem CDFirm.half_kOfR (r : ℝ) :
    CDFirm.half.kOfR r = ((1 / 2) / (r + 1 / 10)) ^ 2 := by
  rw [CDFirm.kOfR, show (1 : ℝ) / (1 - CDFirm.half.α) = 2 by norm_num [CDFirm.half]]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rfl

theorem CDFirm.half_wage (r : ℝ) (hr : -(1 / 10 : ℝ) < r) :
    CDFirm.half.wage r = (1 / 2) * ((1 / 2) / (r + 1 / 10)) := by
  have hx : 0 ≤ (1 / 2) / (r + 1 / 10) := div_nonneg (by norm_num) (by linarith)
  rw [CDFirm.wage, CDFirm.half_kOfR r, show CDFirm.half.α = 1 / 2 from rfl,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq hx]
  norm_num

theorem half_isInvariant :
    IsInvariant (fun _ _ => (1 / 2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) (fun _ => 1 / 2) := by
  refine ⟨⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_two]⟩, ?_⟩
  funext z
  norm_num [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- **A capped Aiyagari economy used as a non-vacuity witness**: `u = √c`,
`β = 9/10`, i.i.d. two-state shock with one efficiency unit in each state (so
`L = 1`), asset cap `1`, Cobb–Douglas firm with `α = 1/2`, `δ = 1/10`, and
interest rates `r ∈ [0, 19/10]`. There is no income risk, and every
equilibrium has `β(1 + r) > 1` with the cap binding: this only shows the
hypotheses of `exists_stationary_equilibrium` are jointly satisfiable. -/
noncomputable def AiyagariEconomy.sqrtEconomy : AiyagariEconomy (Fin 2) where
  u := Real.sqrt
  Q := fun _ _ => 1 / 2
  β := 9 / 10
  kbar := 1
  e := fun _ => 1
  firm := CDFirm.half
  rlo := 0
  rhi := 19 / 10
  qbar := fun _ => 1 / 2
  Q_nonneg := fun _ _ => by norm_num
  Q_sum := fun _ => by norm_num [Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  e_nonneg := fun _ => zero_le_one
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

namespace AiyagariEconomy

theorem sqrt_L : AiyagariEconomy.sqrtEconomy.L = 1 := by
  norm_num [L, AiyagariEconomy.sqrtEconomy, Fin.sum_univ_two]

/-- At `r_hi = 19/10`: `k = 1/16`, `w = 1/8`. -/
theorem sqrt_rhi : AiyagariEconomy.sqrtEconomy.firm.capDemand AiyagariEconomy.sqrtEconomy.L
    (19 / 10) = 1 / 16 ∧ AiyagariEconomy.sqrtEconomy.firm.wage (19 / 10) = 1 / 8 := by
  refine ⟨?_, ?_⟩
  · rw [sqrt_L, CDFirm.capDemand, show AiyagariEconomy.sqrtEconomy.firm = CDFirm.half from rfl,
      CDFirm.half_kOfR]
    norm_num
  · rw [show AiyagariEconomy.sqrtEconomy.firm = CDFirm.half from rfl, CDFirm.half_wage _ (by norm_num)]
    norm_num

/-- **In the example, households save at least `1/16` at `r = 19/10`**,
derived from `ParamSavings.le_policy`. -/
theorem sqrt_saving :
    ∀ (g : AiyagariEconomy.sqrtEconomy.household.S × Fin 2 → AiyagariEconomy.sqrtEconomy.household.S),
      (∀ s, (AiyagariEconomy.sqrtEconomy.household.slice
        ⟨19 / 10, AiyagariEconomy.sqrtEconomy.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∀ s, ((⟨1 / 16, by norm_num, by norm_num [AiyagariEconomy.sqrtEconomy, household]⟩ :
        AiyagariEconomy.sqrtEconomy.household.S) : ℝ) ≤ g s := by
  intro g hg
  set E := AiyagariEconomy.sqrtEconomy
  have hw : E.firm.wage (19 / 10) = 1 / 8 := sqrt_rhi.2
  have hh : ∀ (a : ℝ) (z : Fin 2), E.household.h ⟨19 / 10, E.rlo_le, le_rfl⟩ a z =
      29 / 10 * a + 1 / 8 := fun a z => by
    rw [household_h]
    show (1 + 19 / 10) * a + E.firm.wage (19 / 10) * 1 = _
    rw [hw]; ring
  refine E.household.le_policy _ _ (fun s => ?_) (fun z' a b hab => E.household_h_mono _ z' hab)
    (fun s y x hy hx => ?_) hg
  · rw [hh]
    show (1 / 16 : ℝ) ≤ 29 / 10 * s.1 + 1 / 8
    nlinarith [s.1.2.1]
  · simp only [hh] at hx ⊢
    have hy0 : (0 : ℝ) ≤ y := y.2.1
    have ha0 : (0 : ℝ) ≤ s.1 := s.1.2.1
    have hm : ((⟨1 / 16, by norm_num, by show (1 / 16 : ℝ) ≤ 1; norm_num⟩ : E.household.S) : ℝ) = 1 / 16 :=
      rfl
    rw [hm] at hy
    set d := 1 / 16 - (y : ℝ)
    -- today: the cost is at most `2 d`
    have hcost : Real.sqrt (29 / 10 * s.1 + 1 / 8 - y) - Real.sqrt (29 / 10 * s.1 + 1 / 8 - 1 / 16)
        ≤ 2 * d := by
      have hQ : (0 : ℝ) < 29 / 10 * s.1 + 1 / 8 - 1 / 16 := by nlinarith
      refine (sqrt_sub_le_div hQ (by linarith)).trans ?_
      have hs : (1 / 4 : ℝ) ≤ Real.sqrt (29 / 10 * s.1 + 1 / 8 - 1 / 16) := by
        rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
          rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by nlinarith)
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ d := by simp only [d]; linarith
      have he : 29 / 10 * (s.1 : ℝ) + 1 / 8 - y - (29 / 10 * s.1 + 1 / 8 - 1 / 16) = d := by
        simp only [d]; ring
      rw [he]
      nlinarith
    -- tomorrow: each state gains at least `(29/10) d / (2 · 0.56)`
    have hgain : ∀ z', 29 / 10 * d / (2 * (14 / 25)) ≤
        Real.sqrt (29 / 10 * (1 / 16) + 1 / 8 - x z') - Real.sqrt (29 / 10 * y + 1 / 8 - x z') := by
      intro z'
      have hx0 : (0 : ℝ) ≤ x z' := (x z').2.1
      have hxz := hx z'
      have hA : (0 : ℝ) < 29 / 10 * (1 / 16) + 1 / 8 - x z' := by nlinarith
      refine le_trans ?_ (div_le_sqrt_sub (by linarith) (by nlinarith) hA)
      have hsA : Real.sqrt (29 / 10 * (1 / 16) + 1 / 8 - x z') ≤ 14 / 25 := by
        rw [show (14 / 25 : ℝ) = Real.sqrt ((14 / 25) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hd : 0 ≤ d := by simp only [d]; linarith
      have hpos := Real.sqrt_pos.2 hA
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : 29 / 10 * (1 / 16) + 1 / 8 - x z' - (29 / 10 * y + 1 / 8 - x z') = 29 / 10 * d := by
        simp only [d]; ring
      rw [this]
      nlinarith
    have hsum : 29 / 10 * d / (2 * (14 / 25)) ≤ ∑ z', E.household.Q s.2 z' *
        (Real.sqrt (29 / 10 * (1 / 16) + 1 / 8 - x z') - Real.sqrt (29 / 10 * y + 1 / 8 - x z')) := by
      show _ ≤ ∑ z', (1 / 2 : ℝ) * _
      rw [Fin.sum_univ_two]
      linarith [hgain 0, hgain 1]
    have hd : 0 < d := by simp only [d]; linarith
    have hu : E.household.u = Real.sqrt := rfl
    have hβ : E.household.β = 9 / 10 := rfl
    rw [hu, hβ]
    refine lt_of_le_of_lt hcost (lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_left hsum (by norm_num)))
    have e : (9 / 10 : ℝ) * (29 / 10 * d / (2 * (14 / 25))) = 261 / 112 * d := by ring
    rw [e]
    linarith

/-- **The capped example has a stationary general equilibrium** (non-vacuity
of `exists_stationary_equilibrium`; the cap binds, see `sqrtEconomy`): all
hypotheses of `exists_stationary_equilibrium` are derived
(`hlo` from `k(0) = 25 ≥ k̄`, `hhi` from `sqrt_saving`). -/
theorem sqrt_equilibrium :
    ∃ r : Icc AiyagariEconomy.sqrtEconomy.rlo AiyagariEconomy.sqrtEconomy.rhi,
    ∃ (g : AiyagariEconomy.sqrtEconomy.household.S × Fin 2 → AiyagariEconomy.sqrtEconomy.household.S)
      (hg : Measurable g) (π : ProbabilityMeasure (AiyagariEconomy.sqrtEconomy.household.S × Fin 2)),
      (∀ s, (AiyagariEconomy.sqrtEconomy.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel AiyagariEconomy.sqrtEconomy.Q g hg) π ∧
      ∫ s, AiyagariEconomy.sqrtEconomy.household.assets s
        ∂(π : Measure (AiyagariEconomy.sqrtEconomy.household.S × Fin 2)) =
        AiyagariEconomy.sqrtEconomy.firm.capDemand AiyagariEconomy.sqrtEconomy.L r ∧
      0 < ∫ s, AiyagariEconomy.sqrtEconomy.household.assets s
        ∂(π : Measure (AiyagariEconomy.sqrtEconomy.household.S × Fin 2)) := by
  set E := AiyagariEconomy.sqrtEconomy
  have hlo : E.kbar ≤ E.firm.capDemand E.L E.rlo := by
    rw [sqrt_L, CDFirm.capDemand, show E.firm = CDFirm.half from rfl,
      CDFirm.half_kOfR]
    norm_num [E, AiyagariEconomy.sqrtEconomy]
  obtain ⟨r, g, hg, π, hpol, hinv, hK, -⟩ := E.exists_stationary_equilibrium hlo
    (fun g hg hpol => E.hhi_of_le_policy _ (by show E.firm.capDemand E.L (19 / 10) ≤ (1 / 16 : ℝ); rw [sqrt_rhi.1]) (sqrt_saving) g hg hpol)
  refine ⟨r, g, hg, π, hpol, hinv, hK, ?_⟩
  rw [hK, CDFirm.capDemand, sqrt_L, one_mul]
  exact E.firm.kOfR_pos E.mem_Ioi

end AiyagariEconomy

end Econ

