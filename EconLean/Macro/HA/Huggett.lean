/-
# Huggett's endowment economy: existence of a stationary equilibrium

Huggett (1993); Ljungqvist–Sargent ch. 18.

**The economy** (`HuggettEconomy`). A continuum of households receives an
endowment `y(z) ≥ 0`, with `z` a finite Markov chain `Q` that has a unique
invariant distribution `q̄`. The only asset is a one-period bond in **zero net
supply** paying gross return `1 + r`, with borrowing limit `a ≥ -φ`, `φ > 0`.
Households have utility `u` and discount factor `β`.

We measure wealth from the borrowing limit, `b = a + φ ≥ 0`, so the household
problem is a `ParamSavings` problem on `b ∈ [0, k̄]` with cash on hand
`(1 + r) b + y(z) - r φ`. The bond market clears when `∫ a dπ = 0`, that is
`∫ b dπ = φ`. Interest rates range over `[-1, r_hi]`.

**Results.**
* `policy_lo`: at `r = -1` saving earns nothing, so nobody saves
  (`b' = 0`, i.e. everyone borrows to the limit). This **derives** the lower
  boundary condition: supply `∫ b dπ = 0 ≤ φ`.
* `supply_ge_of_save`: if households in some income state `z_h` always save at
  least `m`, every stationary distribution has `∫ b dπ ≥ m q̄(z_h)`. Combined
  with `StochSavings.le_policy_at` (a one-period-deviation bound, state by
  state), this gives the upper boundary condition from precautionary saving.
* `policy_le_max`: for `r_hi < 0` assets are bounded independently of the cap:
  with `A = (ȳ + φ) / (-r_hi)`, `b' ≤ max(A, b)` and `b' < b` above `A`.
* `exists_stationary_equilibrium`: existence of `r ∈ (-1, r_hi]`, the optimal
  policy and a stationary distribution with bond-market clearing.
  `exists_stationary_equilibrium_slack`: if moreover `r_hi < 0` and `A < k̄`,
  the cap does not bind (`b' < k̄` in every state) and the stationary
  distribution lives on `[0, A]`.
* `huggettExample`, `huggett_equilibrium`: a concrete economy with income risk
  (`y ∈ {0, 2}`, i.i.d.), `u = √c`, `β = 9/10`, `φ = 1/10`, `r ∈ [-1, -1/10]`,
  cap `25`, where **every** hypothesis is derived: there is an equilibrium with
  `-1 < r < 0` (so `r < 1/β - 1`, as in Huggett), the cap is slack, and wealth
  stays in `[0, 21]`.

**Conventions and scope.**
* The borrowing limit bounds the amount borrowed, `a ≥ -φ`, with gross return
  `1 + r` (the Ljungqvist–Sargent / Aiyagari timing). Huggett states it in
  face value at bond price `q = 1/(1+r)`; bond-market clearing is the same.
* `exists_stationary_equilibrium` takes the upper boundary condition `hhi` as
  a hypothesis and does not by itself say the cap is slack or that
  `r < 1/β - 1`; `exists_stationary_equilibrium_slack` adds both, but only for
  `r_hi < 0`. The case `0 ≤ r < 1/β - 1` with a slack cap is not covered here
  (`AssetBound.lean` handles the household side for `r > 0`).
* Existence only: Huggett also shows the stationary distribution is unique at
  each `r`; here `π` is some stationary distribution. Interest rates above `r_hi` are not
searched; in the example the bound `A` uses `r_hi < 0`. Utility must be finite
at `0` (bounded DP), which excludes log and CRRA `σ ≥ 1`.
-/
module

public import EconLean.Macro.HA.AssetBound

@[expose] public section

namespace Econ

open Set Filter Topology MeasureTheory ProbabilityTheory BoundedContinuousFunction

namespace StochSavings

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] {M : StochSavings Z}

/-- The value depends on the state only through cash on hand and the shock. -/
theorem value_eq_of_h_eq {s s' : M.S × Z} (hz : s.2 = s'.2)
    (hh : M.h s.1 s.2 = M.h s'.1 s'.2) :
    M.toStochDynProg.value s = M.toStochDynProg.value s' := by
  have key : ∀ {s s' : M.S × Z}, s.2 = s'.2 → M.h s.1 s.2 = M.h s'.1 s'.2 →
      M.toStochDynProg.value s ≤ M.toStochDynProg.value s' := by
    intro s s' hz hh
    obtain ⟨y, hy⟩ := (M.toStochDynProg.policy_nonempty_compact_uhc.1 s).1
    have e : M.obj s y = M.toStochDynProg.value s := M.toStochDynProg.value_eq_of_mem_policy hy
    have l := obj_le (M := M) s' y (by rw [← hh]; exact hy.1)
    have : M.obj s y = M.obj s' y := by unfold obj; rw [hh, hz]
    linarith
  exact le_antisymm (key hz hh) (key hz.symm hh.symm)

/-- The optimal policy is continuous. -/
theorem continuous_of_policy {g : M.S × Z → M.S}
    (hg : ∀ s, M.toStochDynProg.policy s = {g s}) : Continuous g := by
  obtain ⟨g', hg'c, hg'⟩ :=
    M.toStochDynProg.exists_continuous_policy (convex_Icc 0 M.kbar) M.convexTech M.concaveRet
  have : g = g' := funext fun s => Set.singleton_eq_singleton_iff.1 ((hg s).symm.trans (hg' s))
  rwa [this]

/-- **A lower bound on saving in one state, by a one-period deviation.** If
saving `m` is feasible at `s`, cash on hand is monotone in assets, and for every
smaller saving `y < m` and every continuation `x(z')` feasible after `y`, the
utility cost today of saving `m` instead of `y` is below the discounted
expected gain tomorrow (keeping the continuation `x`), then `g(s) ≥ m`. -/
theorem le_policy_at {g : M.S × Z → M.S} (hg : ∀ s, M.toStochDynProg.policy s = {g s})
    (s : M.S × Z) (m : M.S) (hm : (m : ℝ) ≤ M.h s.1 s.2)
    (hmono : ∀ z' (a b : M.S), (a : ℝ) ≤ b → M.h a z' ≤ M.h b z')
    (hgain : ∀ (y : M.S) (x : Z → M.S), (y : ℝ) < m → (∀ z', (x z' : ℝ) ≤ M.h y z') →
      M.u (M.h s.1 s.2 - y) - M.u (M.h s.1 s.2 - m) <
        M.β * ∑ z', M.Q s.2 z' * (M.u (M.h m z' - x z') - M.u (M.h y z' - x z'))) :
    (m : ℝ) ≤ g s := by
  by_contra hlt
  rw [not_le] at hlt
  set y := g s
  let x : Z → M.S := fun z' => g (y, z')
  have hx : ∀ z', (x z' : ℝ) ≤ M.h y z' := fun z' => feasible hg (y, z')
  have e0 := obj_policy hg s
  have g0 := obj_le s m hm
  have e1 : ∀ z', M.obj (y, z') (x z') = M.toStochDynProg.value (y, z') := fun z' =>
    obj_policy hg (y, z')
  have g1 : ∀ z', M.obj (m, z') (x z') ≤ M.toStochDynProg.value (m, z') := fun z' =>
    obj_le (m, z') (x z') ((hx z').trans (hmono z' y m hlt.le))
  unfold obj at e0 g0 e1 g1
  simp only at e1 g1
  have hsum : ∑ z', M.Q s.2 z' * (M.u (M.h m z' - x z') - M.u (M.h y z' - x z')) ≤
      ∑ z', M.Q s.2 z' * M.toStochDynProg.value (m, z') -
        ∑ z', M.Q s.2 z' * M.toStochDynProg.value (y, z') := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun z' _ => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith [e1 z', g1 z']) (M.Q_nonneg _ _)
  have hG := hgain y x hlt hx
  nlinarith [mul_le_mul_of_nonneg_left hsum M.β_pos.le]

end StochSavings

/-- A **Huggett economy**: households (`u`, `β`, endowments `y(z) ≥ 0` driven
by a Markov chain `Q` with unique invariant distribution `q̄`), a bond in zero
net supply with borrowing limit `φ > 0`, interest rates `r ∈ [-1, r_hi]`, and a
cap `k̄` on wealth above the limit. `r_hi φ ≤ y(z)` keeps cash on hand
nonnegative at the borrowing limit. -/
structure HuggettEconomy (Z : Type*) [Fintype Z] where
  u : ℝ → ℝ
  Q : Z → Z → ℝ
  β : ℝ
  kbar : ℝ
  y : Z → ℝ
  φ : ℝ
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
  y_nonneg : ∀ z, 0 ≤ y z
  φ_pos : 0 < φ
  rhi_ge : -1 ≤ rhi
  rhi_le : ∀ z, rhi * φ ≤ y z
  qbar_inv : IsInvariant Q qbar
  qbar_unique : ∀ π, IsInvariant Q π → π = qbar

namespace HuggettEconomy

variable {Z : Type*} [Fintype Z] (E : HuggettEconomy Z)

/-- The households' problem in wealth above the limit, `b = a + φ`: cash on hand
`(1 + r) b + y(z) - r φ`. -/
noncomputable def household : ParamSavings (Icc (-1) E.rhi) Z where
  u := E.u
  h := fun r b z => (1 + r) * b + E.y z - r * E.φ
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
  h_continuous := fun z =>
    (((continuous_const.add (continuous_subtype_val.comp continuous_fst)).mul continuous_snd).add
      continuous_const).sub ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
  h_nonneg := fun r z k hk => by
    have h1 : 0 ≤ (1 + (r : ℝ)) * k := mul_nonneg (by linarith [r.2.1]) hk
    have h2 : (r : ℝ) * E.φ ≤ E.rhi * E.φ := mul_le_mul_of_nonneg_right r.2.2 E.φ_pos.le
    linarith [E.rhi_le z]
  h_concave := fun r z => ⟨convex_Ici 0, fun x _ x' _ a b _ _ hab => by
    simp only [smul_eq_mul]
    exact le_of_eq (by linear_combination (E.y z - r * E.φ) * hab)⟩

/-- The lowest interest rate, `r = -1`. -/
def lo : Icc (-1 : ℝ) E.rhi := ⟨-1, le_rfl, E.rhi_ge⟩

/-- The highest interest rate, `r_hi`. -/
def hi : Icc (-1 : ℝ) E.rhi := ⟨E.rhi, E.rhi_ge, le_rfl⟩

theorem household_h (r : Icc (-1 : ℝ) E.rhi) (b : ℝ) (z : Z) :
    E.household.h r b z = (1 + r) * b + E.y z - r * E.φ := rfl

variable [TopologicalSpace Z] [DiscreteTopology Z]

/-- **At `r = -1` nobody saves**: saving earns nothing, so the policy is
`b' = 0` (every household borrows up to the limit). -/
theorem policy_lo {g : E.household.S × Z → E.household.S}
    (hg : ∀ s, (E.household.slice E.lo).toStochDynProg.policy s = {g s}) (s : E.household.S × Z) :
    (g s : ℝ) = 0 := by
  set M := E.household.slice E.lo
  let zero : M.S := ⟨0, le_rfl, E.kbar_pos.le⟩
  have hh : ∀ (b : ℝ) (z : Z), M.h b z = E.y z + E.φ := fun b z => by
    show (1 + (-1 : ℝ)) * b + E.y z - (-1) * E.φ = _
    ring
  have hmem : zero ∈ M.toStochDynProg.policy s := by
    refine ⟨show (0 : ℝ) ≤ M.h s.1 s.2 by rw [hh]; linarith [E.y_nonneg s.2, E.φ_pos], ?_⟩
    intro y hy
    show M.obj s y ≤ M.obj s zero
    have hV : ∀ z', M.toStochDynProg.value (y, z') = M.toStochDynProg.value (zero, z') :=
      fun z' => StochSavings.value_eq_of_h_eq rfl (by simp only [hh])
    have hy' : (y : ℝ) ≤ M.h s.1 s.2 := hy
    unfold StochSavings.obj
    simp only [hV]
    have := M.u_mono (show M.h s.1 s.2 - y ∈ Ici (0 : ℝ) from sub_nonneg.2 hy')
      (show M.h s.1 s.2 - (zero : ℝ) ∈ Ici (0 : ℝ) by
        show (0 : ℝ) ≤ M.h s.1 s.2 - 0; rw [hh]; linarith [E.y_nonneg s.2, E.φ_pos])
      (show M.h s.1 s.2 - y ≤ M.h s.1 s.2 - (zero : ℝ) by
        show M.h s.1 s.2 - y ≤ M.h s.1 s.2 - 0; linarith [y.2.1])
    linarith
  rw [hg s] at hmem
  exact (congrArg Subtype.val hmem).symm

variable [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]

/-- **The lower boundary condition is derived**: at `r = -1` every stationary
distribution has wealth `∫ b dπ = 0 ≤ φ` (net bond holdings `-φ`). -/
theorem supply_lo (g : E.household.S × Z → E.household.S) (hg : Measurable g)
    (hpol : ∀ s, (E.household.slice E.lo).toStochDynProg.policy s = {g s}) :
    ∃ μ : ProbabilityMeasure (E.household.S × Z),
      Kernel.Invariant (policyKernel E.household.Q g hg) μ ∧
      ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)) ≤ E.φ := by
  obtain ⟨μ, hμ⟩ := E.household.exists_stationary_of_policy _ g hg hpol
  refine ⟨μ, hμ, ?_⟩
  rw [← E.household.integral_policy_eq g hg μ hμ]
  have : (fun s => ((g s : E.household.S) : ℝ)) = fun _ => 0 := funext (E.policy_lo hpol)
  rw [this, integral_zero]
  exact E.φ_pos.le

omit [Nonempty Z] in
/-- **Supply from precautionary saving**: if households in state `z_h` always
save at least `m ≥ 0`, every stationary distribution has
`∫ b dπ ≥ m q̄(z_h)`. -/
theorem supply_ge_of_save [DecidableEq Z] (g : E.household.S × Z → E.household.S)
    (hg : Measurable g) (zh : Z) (m : ℝ) (hsave : ∀ b, m ≤ g (b, zh))
    (μ : ProbabilityMeasure (E.household.S × Z))
    (hμ : Kernel.Invariant (policyKernel E.household.Q g hg) μ) :
    m * E.qbar zh ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)) := by
  have hmarg : E.household.marg μ = E.qbar :=
    E.qbar_unique _ (E.household.marg_isInvariant g hg μ hμ)
  rw [← E.household.integral_policy_eq g hg μ hμ]
  have hint := E.household.integral_zfun μ (fun z => if z = zh then m else 0)
  simp only [hmarg, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hint
  rw [← hint]
  have hgi : Integrable (fun s => ((g s : E.household.S) : ℝ)) (μ : Measure (E.household.S × Z)) :=
    Integrable.mono' (integrable_const E.kbar)
      (continuous_subtype_val.measurable.comp hg).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (g s).2.1]; exact (g s).2.2)
  refine integral_mono ((E.household.zfun _).integrable _) hgi fun s => ?_
  rw [E.household.zfun_apply]
  split_ifs with h
  · obtain ⟨b, z⟩ := s
    simp only at h
    subst h
    exact hsave b
  · exact (g s).2.1

/-- **Existence of a stationary equilibrium in Huggett's model**: given the
upper boundary condition (`hhi`: at `r_hi` some stationary distribution has
`∫ b ≥ φ`), there are an interest rate `r ∈ (-1, r_hi]`, the optimal policy
`g` and a stationary distribution `π` at which the bond market clears:
`∫ b dπ = φ`, i.e. `∫ a dπ = 0`. The lower boundary condition is derived
(`supply_lo`). -/
theorem exists_stationary_equilibrium
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice E.hi).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z),
        Kernel.Invariant (policyKernel E.household.Q g hg) μ ∧
        E.φ ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z))) :
    ∃ r : Icc (-1 : ℝ) E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.household.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.φ ∧ -1 < (r : ℝ) := by
  obtain ⟨r, g, hg, π, hpol, hinv, hclear⟩ :=
    E.household.exists_asset_market_clearing_of_supply E.rhi_ge (fun _ => E.φ) continuousOn_const
      E.supply_lo hhi
  refine ⟨r, g, hg, π, hpol, hinv, hclear, lt_of_le_of_ne r.2.1 fun hr => ?_⟩
  have hrlo : r = E.lo := Subtype.ext hr.symm
  subst hrlo
  rw [← E.household.integral_policy_eq g hg π hinv] at hclear
  have : (fun s => ((g s : E.household.S) : ℝ)) = fun _ => 0 := funext (E.policy_lo hpol)
  rw [this, integral_zero] at hclear
  exact E.φ_pos.ne' hclear.symm

omit [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z] in
/-- **An asset bound for negative interest rates**: if `r_hi < 0` and
`y ≤ ȳ`, then with `A = (ȳ + φ) / (-r_hi)`, at every `r ∈ [-1, r_hi]`,
`b' ≤ max(A, b)`, and `b' < b` whenever `b > A`. The bound does not depend on
the cap `k̄`. -/
theorem policy_le_max (hrhi : E.rhi < 0) {ybar : ℝ} (hyb : ∀ z, E.y z ≤ ybar)
    (r : Icc (-1 : ℝ) E.rhi) {g : E.household.S × Z → E.household.S}
    (hg : ∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) (s : E.household.S × Z) :
    (g s : ℝ) ≤ max ((ybar + E.φ) / (-E.rhi)) s.1 ∧
      ((ybar + E.φ) / (-E.rhi) < s.1 → (g s : ℝ) < s.1) := by
  set A := (ybar + E.φ) / (-E.rhi)
  have hne : E.rhi ≠ 0 := hrhi.ne
  have hA : -E.rhi * A = ybar + E.φ := by simp only [A]; field_simp
  have hfeas := StochSavings.feasible hg s
  have hh : (E.household.slice r).h s.1 s.2 = (1 + r) * s.1 + E.y s.2 - r * E.φ := rfl
  have hb : (0 : ℝ) ≤ s.1 := s.1.2.1
  have h1 : (1 + (r : ℝ)) * s.1 ≤ (1 + E.rhi) * s.1 :=
    mul_le_mul_of_nonneg_right (by linarith [r.2.2]) hb
  have h2 : -(r : ℝ) * E.φ ≤ E.φ := by nlinarith [r.2.1, E.φ_pos]
  have hbound : (g s : ℝ) ≤ s.1 + -E.rhi * (A - s.1) := by
    rw [hh] at hfeas; nlinarith [hyb s.2]
  refine ⟨?_, fun hs => ?_⟩
  · rcases le_total (s.1 : ℝ) A with h | h
    · refine hbound.trans (le_trans ?_ (le_max_left _ _))
      nlinarith [E.rhi_ge]
    · exact hbound.trans ((by nlinarith : (s.1 : ℝ) + -E.rhi * (A - s.1) ≤ s.1).trans
        (le_max_right _ _))
  · nlinarith

/-- **Huggett equilibrium with a slack cap**: if moreover `r_hi < 0`, `y ≤ ȳ`
and `A = (ȳ + φ) / (-r_hi) < k̄`, the equilibrium of
`exists_stationary_equilibrium` has `b' < k̄` in every state (the cap never
binds), its stationary distribution lives on `[0, A]`, and `-1 < r < 0`. -/
theorem exists_stationary_equilibrium_slack
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice E.hi).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z),
        Kernel.Invariant (policyKernel E.household.Q g hg) μ ∧
        E.φ ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)))
    (hrhi : E.rhi < 0) {ybar : ℝ} (hyb : ∀ z, E.y z ≤ ybar)
    (hAk : (ybar + E.φ) / (-E.rhi) < E.kbar) :
    ∃ r : Icc (-1 : ℝ) E.rhi, ∃ (g : E.household.S × Z → E.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (E.household.S × Z)),
      (∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel E.household.Q g hg) π ∧
      ∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z)) = E.φ ∧
      (∀ s, (g s : ℝ) < E.kbar) ∧
      (π : Measure (E.household.S × Z)) {s | (ybar + E.φ) / (-E.rhi) < (s.1 : ℝ)} = 0 ∧
      -1 < (r : ℝ) ∧ (r : ℝ) < 0 := by
  obtain ⟨r, g, hg, π, hpol, hinv, hclear, hr⟩ := E.exists_stationary_equilibrium hhi
  have hb := E.policy_le_max hrhi hyb r hpol
  refine ⟨r, g, hg, π, hpol, hinv, hclear, fun s => ?_, ?_, hr, lt_of_le_of_lt r.2.2 hrhi⟩
  · rcases le_or_gt (s.1 : ℝ) ((ybar + E.φ) / (-E.rhi)) with h | h
    · have := (hb s).1
      rw [max_eq_left h] at this
      linarith
    · exact ((hb s).2 h).trans_le s.1.2.2
  · exact StochSavings.measure_gt_eq_zero_of_bound (M := E.household.slice r)
      (StochSavings.continuous_of_policy hpol) (fun s => (hb s).1) (fun s => (hb s).2) hg _ hinv

/-! ### A fully derived example -/

/-- **A Huggett economy with income risk**: `u = √c`, `β = 9/10`, endowment
`y ∈ {0, 2}` i.i.d. with probability `1/2`, borrowing limit `φ = 1/10`,
interest rates `r ∈ [-1, -1/10]`, cap `k̄ = 25` on wealth above the limit. -/
noncomputable def huggettExample : HuggettEconomy (Fin 2) where
  u := Real.sqrt
  Q := fun _ _ => 1 / 2
  β := 9 / 10
  kbar := 25
  y := ![0, 2]
  φ := 1 / 10
  rhi := -1 / 10
  qbar := fun _ => 1 / 2
  Q_nonneg := fun _ _ => by norm_num
  Q_sum := fun _ => by norm_num [Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  y_nonneg := fun z => by fin_cases z <;> norm_num
  φ_pos := by norm_num
  rhi_ge := by norm_num
  rhi_le := fun z => by fin_cases z <;> norm_num
  qbar_inv := half_isInvariant
  qbar_unique := fun π hπ => by
    have hQ : IsStochastic (fun _ _ => (1 / 2 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨fun _ _ => by norm_num, fun _ => by norm_num [Fin.sum_univ_two]⟩
    obtain ⟨π₀, -, hu, -⟩ := doeblin hQ (ε := 1 / 2) (by norm_num) (fun _ _ => le_rfl)
    rw [hu π hπ, ← hu _ half_isInvariant]

/-- **Precautionary saving at `r_hi = -1/10`**: households with the high
endowment save at least `1/5` above the borrowing limit, whatever their
wealth, although `r < 0` and `β (1 + r) < 1`. (The risk of a zero endowment
tomorrow makes consumption at the limit very valuable.) -/
theorem huggett_saving (g : huggettExample.household.S × Fin 2 → huggettExample.household.S)
    (hg : ∀ s, (huggettExample.household.slice huggettExample.hi).toStochDynProg.policy s = {g s})
    (b : huggettExample.household.S) : (1 / 5 : ℝ) ≤ g (b, 1) := by
  let M := huggettExample.household.slice huggettExample.hi
  have hh : ∀ (a : ℝ) (z : Fin 2), M.h a z = 9 / 10 * a + ![(0 : ℝ), 2] z + 1 / 100 :=
    fun a z => by
      show (1 + (-1 / 10 : ℝ)) * a + ![(0 : ℝ), 2] z - (-1 / 10) * (1 / 10) = _
      ring
  have hy0 : ![(0 : ℝ), 2] 0 = 0 := rfl
  have hy1 : ![(0 : ℝ), 2] 1 = 2 := rfl
  let m : M.S := ⟨1 / 5, by norm_num, by show (1 / 5 : ℝ) ≤ 25; norm_num⟩
  have hb0 : (0 : ℝ) ≤ b := b.2.1
  show ((m : M.S) : ℝ) ≤ g (b, 1)
  refine StochSavings.le_policy_at (M := M) hg (b, 1) m ?_ (fun z' a a' haa => ?_)
    (fun y x hy hx => ?_)
  · show (1 / 5 : ℝ) ≤ M.h b 1
    rw [hh, hy1]; linarith
  · rw [hh, hh]; linarith
  · have hm : ((m : M.S) : ℝ) = 1 / 5 := rfl
    rw [hm] at hy
    have hyy : (0 : ℝ) ≤ y := y.2.1
    simp only [hh, hm, hy1] at hx ⊢
    show _ < (9 / 10 : ℝ) * ∑ z' : Fin 2, (1 / 2 : ℝ) * _
    rw [Fin.sum_univ_two]
    simp only [hy0, hy1]
    set d := 1 / 5 - (y : ℝ)
    have hd : 0 < d := by simp only [d]; linarith
    set H := 9 / 10 * (b : ℝ) + 2 + 1 / 100
    -- cost today `≤ 5 d / 13`
    have hcost : Real.sqrt (H - y) - Real.sqrt (H - 1 / 5) ≤ 5 / 13 * d := by
      have hQ : (0 : ℝ) < H - 1 / 5 := by simp only [H]; linarith
      refine (sqrt_sub_le_div hQ (by linarith)).trans ?_
      have hs : (13 / 10 : ℝ) ≤ Real.sqrt (H - 1 / 5) := by
        rw [show (13 / 10 : ℝ) = Real.sqrt ((13 / 10) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by simp only [H]; nlinarith)
      rw [div_le_iff₀ (by positivity), show H - y - (H - 1 / 5) = d by simp only [d]; ring]
      nlinarith
    -- gain tomorrow in the zero-endowment state `≥ 45 d / 44`
    have hx0 := hx 0
    have hx1 := hx 1
    simp only [hy0, hy1] at hx0 hx1
    have hX0 : (0 : ℝ) ≤ x 0 := (x 0).2.1
    have hgain0 : 45 / 44 * d ≤ Real.sqrt (9 / 10 * (1 / 5) + 0 + 1 / 100 - x 0) -
        Real.sqrt (9 / 10 * y + 0 + 1 / 100 - x 0) := by
      have hP : (0 : ℝ) < 9 / 10 * (1 / 5) + 0 + 1 / 100 - x 0 := by linarith
      refine le_trans ?_ (div_le_sqrt_sub (by linarith) (by linarith) hP)
      have hsP : Real.sqrt (9 / 10 * (1 / 5) + 0 + 1 / 100 - x 0) ≤ 44 / 100 := by
        rw [show (44 / 100 : ℝ) = Real.sqrt ((44 / 100) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hpos := Real.sqrt_pos.2 hP
      rw [show 9 / 10 * (1 / 5) + 0 + 1 / 100 - x 0 - (9 / 10 * y + 0 + 1 / 100 - x 0) =
        9 / 10 * d by simp only [d]; ring]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hgain1 : 0 ≤ Real.sqrt (9 / 10 * (1 / 5) + 2 + 1 / 100 - x 1) -
        Real.sqrt (9 / 10 * y + 2 + 1 / 100 - x 1) :=
      sub_nonneg.2 (Real.sqrt_le_sqrt (by linarith))
    have hu : M.u = Real.sqrt := rfl
    rw [hu]
    nlinarith

/-- **The example has a stationary equilibrium with every hypothesis
derived**: the interest rate satisfies `-1 < r < 0` (below `1/β - 1`), the bond
market clears (`∫ b dπ = φ = 1/10`, i.e. `∫ a dπ = 0`), the cap `k̄ = 25`
never binds, and the stationary distribution of wealth above the limit lives
on `[0, 21]`. -/
theorem huggett_equilibrium :
    ∃ r : Icc (-1 : ℝ) huggettExample.rhi,
    ∃ (g : huggettExample.household.S × Fin 2 → huggettExample.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (huggettExample.household.S × Fin 2)),
      (∀ s, (huggettExample.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel huggettExample.household.Q g hg) π ∧
      ∫ s, huggettExample.household.assets s ∂(π : Measure (huggettExample.household.S × Fin 2)) =
        1 / 10 ∧
      (∀ s, (g s : ℝ) < 25) ∧
      (π : Measure (huggettExample.household.S × Fin 2)) {s | (21 : ℝ) < s.1} = 0 ∧
      -1 < (r : ℝ) ∧ (r : ℝ) < 0 := by
  set E := huggettExample
  have hyb : ∀ z, E.y z ≤ 2 := fun z => by fin_cases z <;> norm_num [E, huggettExample]
  have hhi : ∀ (g : E.household.S × Fin 2 → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice E.hi).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Fin 2),
        Kernel.Invariant (policyKernel E.household.Q g hg) μ ∧
        E.φ ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Fin 2)) :=
    fun g hg hpol => by
      obtain ⟨μ, hμ⟩ := E.household.exists_stationary_of_policy _ g hg hpol
      refine ⟨μ, hμ, ?_⟩
      have := E.supply_ge_of_save g hg 1 (1 / 5) (huggett_saving g hpol) μ hμ
      have hq : E.qbar 1 = 1 / 2 := rfl
      have hφ : E.φ = 1 / 10 := rfl
      rw [hq] at this
      rw [hφ]
      linarith
  obtain ⟨r, g, hg, π, hpol, hinv, hclear, hcap, hsupp, hr1, hr2⟩ :=
    E.exists_stationary_equilibrium_slack hhi (by norm_num [E, huggettExample]) hyb
      (by norm_num [E, huggettExample])
  have hA : (2 + E.φ) / (-E.rhi) = 21 := by norm_num [E, huggettExample]
  rw [hA] at hsupp
  exact ⟨r, g, hg, π, hpol, hinv, hclear, hcap, hsupp, hr1, hr2⟩

end HuggettEconomy

end Econ
