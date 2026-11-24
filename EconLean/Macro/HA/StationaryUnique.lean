/-
# Uniqueness of the stationary wealth distribution

Hopenhayn–Prescott (1992); Stokey–Lucas–Prescott ch. 12.4; Aiyagari (1994);
Ljungqvist–Sargent ch. 18.

The existence results (`StationaryDist`, `AiyagariGE`, `AiyagariSlack`) give
*some* stationary distribution at each interest rate. This file proves that,
for savings problems with i.i.d. income, the stationary distribution is
**unique** under a splitting condition, using the monotone-mixing theorem
`unique_invariant_of_splitting`.

**Monotone transitions** (`isMonotoneKernel_policyKernel`,
`StochSavings.policy_monotone`). Order states `(a, z)` componentwise. If the
shock is i.i.d. (all rows of `Q` equal) and cash on hand is increasing in
`(a, z)`, the optimal policy is increasing in `(a, z)` (the value depends on
the state only through cash on hand), so the transition kernel
`(a, z) ↦ δ_{g(a, z)} ⊗ Q(z, ·)` is monotone.

**Uniqueness for savings problems** (`StochSavings.unique_stationary_of_splitting`).
Under those conditions and a splitting condition at some state `c`, there is
at most one stationary distribution.

**The Aiyagari example** (`slack_stationary_unique`, `slack_equilibrium_unique`).
In the economy `slackEconomy` of `AiyagariSlack`, at *every* interest rate of
the bracket, the stationary distribution is unique. Splitting holds at
`c = (k_h / 100, unemployed)` with `k_h = k(r_hi)`:
* employed households always save at least `k_h / 100` (a one-period
  deviation argument; the risk of unemployment with zero income makes a little
  wealth very valuable), so after two periods the process is above `c` with
  probability at least `1/100`;
* unemployed households have cash `(1 + r) a ≤ (19/20) a`, so after `321`
  periods of unemployment (probability `(9/10)^{321}`) wealth is below
  `k_h / 100`.
So the equilibrium of `slack_equilibrium` comes with the unique stationary
distribution at its interest rate.

**Scope.** Income is i.i.d.; Markov income needs `Q` monotone (first-order
stochastic dominance in `z`) and a policy increasing in `z`, which is not
formalized. Convergence of the distribution from any initial condition (the
other half of Hopenhayn–Prescott) is not formalized. Uniqueness of the
equilibrium *interest rate* is a different (and in general false) claim and is
not addressed.
-/
module

public import EconLean.Macro.HA.AiyagariSlack
public import EconLean.Macro.DP.MonotoneMixing

@[expose] public section

namespace Econ

open Set Filter Topology MeasureTheory ProbabilityTheory BoundedContinuousFunction

section PolicyKernel

variable {X Z : Type*} [MeasurableSpace X] [Fintype Z] [MeasurableSpace Z]
  [MeasurableSingletonClass Z]

/-- `κ((x, z), U) = Σ_{z'} Q(z, z') 1_U(g(x, z), z')`. -/
theorem policyKernel_real_apply {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    (g : X × Z → X) (hg : Measurable g) (s : X × Z) {U : Set (X × Z)} (hU : MeasurableSet U) :
    (policyKernel Q g hg s).real U = ∑ z', Q s.2 z' * U.indicator 1 (g s, z') := by
  have hterm : ∀ z', (ENNReal.ofReal (Q s.2 z') • Measure.dirac (g s, z')) U =
      ENNReal.ofReal (Q s.2 z') * U.indicator 1 (g s, z') := fun z' => by
    rw [smul_apply, Measure.dirac_apply' _ hU, smul_eq_mul]
  rw [measureReal_def, policyKernel_apply, sum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun z' _ => ?_
    rw [hterm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hQ0 _ _)]
    by_cases h : (g s, z') ∈ U <;> simp [h]
  · intro z' _
    rw [hterm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by by_cases h : (g s, z') ∈ U <;> simp [h])

/-- A one-step lower bound: if `(g(s), z₀) ∈ U` then `κ(s, U) ≥ Q(z, z₀)`. -/
theorem le_policyKernel_real {Q : Z → Z → ℝ} (hQ0 : ∀ z z', 0 ≤ Q z z')
    (g : X × Z → X) (hg : Measurable g) (s : X × Z) {U : Set (X × Z)} (hU : MeasurableSet U)
    {z₀ : Z} (hz₀ : (g s, z₀) ∈ U) : Q s.2 z₀ ≤ (policyKernel Q g hg s).real U := by
  rw [policyKernel_real_apply hQ0 g hg s hU]
  have := Finset.single_le_sum (f := fun z' => Q s.2 z' * U.indicator 1 (g s, z'))
    (fun z' _ => mul_nonneg (hQ0 _ _) (indicator_nonneg (fun _ _ => zero_le_one) _))
    (Finset.mem_univ z₀)
  simpa [indicator_of_mem hz₀] using this

/-- **The transition kernel of an increasing policy with i.i.d. shocks is
monotone** (componentwise order on `X × Z`). -/
theorem isMonotoneKernel_policyKernel [Preorder X] [Preorder Z] {Q : Z → Z → ℝ}
    (hQ0 : ∀ z z', 0 ≤ Q z z') (hiid : ∀ z₁ z₂ z', Q z₁ z' = Q z₂ z')
    {g : X × Z → X} (hg : Measurable g) (hmono : Monotone g) :
    IsMonotoneKernel (policyKernel Q g hg) := by
  intro U hU hUm s s' hss
  simp only
  rw [policyKernel_real_apply hQ0 g hg s hUm, policyKernel_real_apply hQ0 g hg s' hUm]
  refine Finset.sum_le_sum fun z' _ => ?_
  rw [hiid s'.2 s.2 z']
  refine mul_le_mul_of_nonneg_left ?_ (hQ0 _ _)
  by_cases h : (g s, z') ∈ U
  · have h' : (g s', z') ∈ U := hU (Prod.mk_le_mk.2 ⟨hmono hss, le_rfl⟩) h
    simp [h, h']
  · rw [indicator_of_notMem h]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

end PolicyKernel

namespace StochSavings

variable {Z : Type*} [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z] {M : StochSavings Z}

/-- **The optimal policy is increasing in `(a, z)`** when the shock is i.i.d.
and cash on hand is increasing in `(a, z)`. -/
theorem policy_monotone [Preorder Z] {g : M.S × Z → M.S}
    (hg : ∀ s, M.toStochDynProg.policy s = {g s}) (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hh : ∀ (a a' : M.S) (z z' : Z), (a : ℝ) ≤ a' → z ≤ z' → M.h a z ≤ M.h a' z') :
    Monotone g :=
  fun _ _ hss => Subtype.coe_le_coe.1 <|
    policy_mono hg (fun z' => hiid _ _ z') (hh _ _ _ _ hss.1 hss.2)

/-- **Uniqueness of the stationary distribution of a savings problem**
(Hopenhayn–Prescott 1992): with i.i.d. shocks, cash on hand increasing in
`(a, z)`, and the splitting condition (from every state, after `N` periods the
state is `≤ c` with probability at least `δ` and `≥ c` with probability at
least `δ`), the policy's transition kernel has at most one invariant
probability measure. -/
theorem unique_stationary_of_splitting [LinearOrder Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] {g : M.S × Z → M.S}
    (hpol : ∀ s, M.toStochDynProg.policy s = {g s}) (hg : Measurable g)
    (hiid : ∀ z₁ z₂ z', M.Q z₁ z' = M.Q z₂ z')
    (hh : ∀ (a a' : M.S) (z z' : Z), (a : ℝ) ≤ a' → z ≤ z' → M.h a z ≤ M.h a' z')
    {N : ℕ} {c : M.S × Z} {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ x, δ ≤ ((policyKernel M.Q g hg ^ N) x).real (Iic c))
    (hup : ∀ x, δ ≤ ((policyKernel M.Q g hg ^ N) x).real (Ici c))
    {π π' : Measure (M.S × Z)} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant (policyKernel M.Q g hg) π)
    (hπ' : Kernel.Invariant (policyKernel M.Q g hg) π') : π' = π := by
  have := isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum g hg
  have hIic : MeasurableSet (Iic c) := by
    have : Iic c = Prod.fst ⁻¹' Iic c.1 ∩ Prod.snd ⁻¹' Iic c.2 := by
      ext p; exact Prod.le_def
    rw [this]
    exact (measurable_fst measurableSet_Iic).inter (measurable_snd (toFinite _).measurableSet)
  exact unique_invariant_of_splitting
    (isMonotoneKernel_policyKernel M.Q_nonneg hiid hg (policy_monotone hpol hiid hh))
    generateFrom_upperSets_prod hδ hIic hlow hup hπ hπ'

end StochSavings

namespace AiyagariEconomy

/-- **Employed households always save a little**: in `slackEconomy`, at every
interest rate of the bracket, employed households save at least
`k(r_hi) / 100`, whatever their wealth. -/
theorem slack_saving_floor (r : Icc slackEconomy.rlo slackEconomy.rhi)
    (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S)
    (hg : ∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s})
    (a : slackEconomy.household.S) : CDFirm.tenth.kOfR (-1 / 20) / 100 ≤ g (a, 1) := by
  let M := slackEconomy.household.slice r
  set k := CDFirm.tenth.kOfR (-1 / 20) with hkdef
  have hk : 0 < k := CDFirm.tenth.kOfR_pos (by norm_num [CDFirm.tenth])
  have hr1 : (-799 / 2000 : ℝ) ≤ r := r.2.1
  have hr2 : (r : ℝ) ≤ -1 / 20 := r.2.2
  set W := CDFirm.tenth.wage r
  have hW : 63 / 20 * k ≤ W := by
    have h1 : CDFirm.tenth.wage (-1 / 20) = 63 / 20 * k := by
      rw [CDFirm.tenth.wage_eq_mul_kOfR (by norm_num [CDFirm.tenth]), ← hkdef]
      norm_num [CDFirm.tenth]
    rw [← h1]
    exact CDFirm.tenth.wage_anti (lt_of_lt_of_le tenth_rlo hr1) hr2
  have hh : ∀ (b : ℝ) (z : Fin 2), M.h b z = (1 + (r : ℝ)) * b + W * ![(0 : ℝ), 1] z :=
    fun b z => rfl
  have he0 : ![(0 : ℝ), 1] 0 = 0 := rfl
  have he1 : ![(0 : ℝ), 1] 1 = 1 := rfl
  have hkb : k / 100 ≤ slackEconomy.kbar := by linarith [slack_kh_le]
  let m : M.S := ⟨k / 100, by positivity, hkb⟩
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  show ((m : M.S) : ℝ) ≤ g (a, 1)
  refine StochSavings.le_policy_at (M := M) hg (a, 1) m ?_ (fun z' b b' hbb => ?_)
    (fun y x hy hx => ?_)
  · show k / 100 ≤ M.h a 1
    rw [hh, he1]; nlinarith
  · rw [hh, hh]; nlinarith
  · have hm : ((m : M.S) : ℝ) = k / 100 := rfl
    rw [hm] at hy
    have hyy : (0 : ℝ) ≤ y := y.2.1
    simp only [hh, hm, he1] at hx ⊢
    show _ < (9 / 10 : ℝ) * ∑ z' : Fin 2, unempQ 1 z' * _
    rw [Fin.sum_univ_two]
    simp only [he0, he1, unempQ]
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one]
    set R := 1 + (r : ℝ)
    have hR1 : R ≤ 1 := by simp only [R]; linarith
    have hR0 : 6 / 10 ≤ R := by simp only [R]; linarith
    set d := k / 100 - (y : ℝ)
    have hd : 0 < d := by simp only [d]; linarith
    set t := Real.sqrt k
    have ht : 0 < t := Real.sqrt_pos.2 hk
    have ht2 : t ^ 2 = k := Real.sq_sqrt hk.le
    set H := R * (a : ℝ) + W * 1
    -- cost today `≤ d / (3.4 t)`
    have hcost : (Real.sqrt (H - y) - Real.sqrt (H - k / 100)) * (34 / 10 * t) ≤ d := by
      have hQ : (0 : ℝ) < H - k / 100 := by simp only [H]; nlinarith
      have h1 := sqrt_sub_le_div (P := H - y) hQ (by linarith)
      have hs : 17 / 10 * t ≤ Real.sqrt (H - k / 100) :=
        (Real.le_sqrt (by positivity) hQ.le).2 (by rw [mul_pow, ht2]; simp only [H]; nlinarith)
      rw [show H - y - (H - k / 100) = d by simp only [d]; ring] at h1
      rw [le_div_iff₀ (by positivity)] at h1
      have hc0 : 0 ≤ Real.sqrt (H - y) - Real.sqrt (H - k / 100) :=
        sub_nonneg.2 (Real.sqrt_le_sqrt (by linarith))
      nlinarith
    -- gain tomorrow when unemployed `≥ 3 d / t`
    have hx0 := hx 0
    have hx1 := hx 1
    simp only [he0, he1] at hx0 hx1
    have hX0 : (0 : ℝ) ≤ x 0 := (x 0).2.1
    have hgain0 : 6 / 10 * d ≤ (Real.sqrt (R * (k / 100) + W * 0 - x 0) -
        Real.sqrt (R * y + W * 0 - x 0)) * (2 / 10 * t) := by
      have hRd : 0 < R * d := by positivity
      have hP : (0 : ℝ) < R * (k / 100) + W * 0 - x 0 := by
        have : R * (k / 100) - R * y = R * d := by simp only [d]; ring
        linarith
      have h1 := div_le_sqrt_sub (B := R * y + W * 0 - x 0) (by linarith) (by nlinarith) hP
      have hsP : Real.sqrt (R * (k / 100) + W * 0 - x 0) ≤ 1 / 10 * t :=
        Real.sqrt_le_iff.2 ⟨by positivity, by rw [mul_pow, ht2]; nlinarith⟩
      have hpos := Real.sqrt_pos.2 hP
      rw [show R * (k / 100) + W * 0 - x 0 - (R * y + W * 0 - x 0) = R * d by
        simp only [d]; ring] at h1
      have hG0 : 0 ≤ Real.sqrt (R * (k / 100) + W * 0 - x 0) - Real.sqrt (R * y + W * 0 - x 0) :=
        sub_nonneg.2 (Real.sqrt_le_sqrt (by nlinarith))
      rw [div_le_iff₀ (by positivity)] at h1
      have h2 := mul_le_mul_of_nonneg_left (by linarith [hsP] :
        2 * Real.sqrt (R * (k / 100) + W * 0 - x 0) ≤ 2 / 10 * t) hG0
      nlinarith
    have hgain1 : 0 ≤ Real.sqrt (R * (k / 100) + W * 1 - x 1) -
        Real.sqrt (R * y + W * 1 - x 1) :=
      sub_nonneg.2 (Real.sqrt_le_sqrt (by nlinarith))
    have hu : M.u = Real.sqrt := rfl
    rw [hu]
    set C := Real.sqrt (H - y) - Real.sqrt (H - k / 100)
    set G0 := Real.sqrt (R * (k / 100) + W * 0 - x 0) - Real.sqrt (R * y + W * 0 - x 0)
    have hpos : 0 < (81 / 100 * G0 - C) * t := by nlinarith
    have := (mul_pos_iff_of_pos_right ht).1 hpos
    nlinarith

/-- Crude numerical bounds: `k̄ ≤ 4000` and `k(r_hi) ≥ 4/49`. -/
theorem slack_bounds : slackEconomy.kbar ≤ 4000 ∧ 4 / 49 ≤ CDFirm.tenth.kOfR (-1 / 20) := by
  have he : 1 / (1 - CDFirm.tenth.α) = 10 / 9 := by norm_num [CDFirm.tenth]
  constructor
  · show 1 / 10 * CDFirm.tenth.kOfR (-799 / 2000) ≤ 4000
    have hb : CDFirm.tenth.α / (-799 / 2000 + CDFirm.tenth.δ) = 200 := by norm_num [CDFirm.tenth]
    rw [CDFirm.kOfR, hb, he]
    have : (200 : ℝ) ^ (10 / 9 : ℝ) ≤ 200 ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_two] at this
    linarith
  · have hb : CDFirm.tenth.α / (-1 / 20 + CDFirm.tenth.δ) = 2 / 7 := by norm_num [CDFirm.tenth]
    rw [CDFirm.kOfR, hb, he]
    have : (2 / 7 : ℝ) ^ (2 : ℝ) ≤ (2 / 7) ^ (10 / 9 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    rw [Real.rpow_two] at this
    linarith

/-- **The stationary distribution is unique at every interest rate** of the
bracket in `slackEconomy`: for every `r ∈ [r_lo, r_hi]`, the optimal policy's
transition kernel has at most one invariant probability measure. -/
theorem slack_stationary_unique (r : Icc slackEconomy.rlo slackEconomy.rhi)
    (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S) (hg : Measurable g)
    (hpol : ∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s})
    (π π' : ProbabilityMeasure (slackEconomy.household.S × Fin 2))
    (hπ : Kernel.Invariant (policyKernel slackEconomy.Q g hg) π)
    (hπ' : Kernel.Invariant (policyKernel slackEconomy.Q g hg) π') : π' = π := by
  let M := slackEconomy.household.slice r
  set K := policyKernel M.Q g hg with hKdef
  have hK : IsMarkovKernel K := isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum g hg
  have hQ0 : ∀ z z', 0 ≤ M.Q z z' := M.Q_nonneg
  have hr1 : (-799 / 2000 : ℝ) ≤ r := r.2.1
  have hr2 : (r : ℝ) ≤ -1 / 20 := r.2.2
  set W := CDFirm.tenth.wage r
  have hW : 0 < W := CDFirm.tenth.wage_pos (lt_of_lt_of_le tenth_rlo hr1)
  have hh : ∀ (b : ℝ) (z : Fin 2), M.h b z = (1 + (r : ℝ)) * b + W * ![(0 : ℝ), 1] z :=
    fun b z => rfl
  obtain ⟨hkb, hk⟩ := slack_bounds
  set k := CDFirm.tenth.kOfR (-1 / 20) with hkdef
  set kb := slackEconomy.kbar
  -- monotone cash on hand
  have hmono : ∀ (a a' : M.S) (z z' : Fin 2), (a : ℝ) ≤ a' → z ≤ z' → M.h a z ≤ M.h a' z' := by
    intro a a' z z' haa hzz
    have he : ![(0 : ℝ), 1] z ≤ ![(0 : ℝ), 1] z' := by
      fin_cases z <;> fin_cases z' <;> simp_all
    rw [hh, hh]
    have := mul_le_mul_of_nonneg_left he hW.le
    nlinarith
  -- unemployed households run down wealth
  have hdown : ∀ y : M.S × Fin 2, y.2 = 0 → (g y : ℝ) ≤ 19 / 20 * y.1 := by
    intro y hy
    have hf := StochSavings.feasible hpol y
    rw [hh, hy] at hf
    have : ![(0 : ℝ), 1] 0 = 0 := rfl
    rw [this, mul_zero, add_zero] at hf
    nlinarith [y.1.2.1]
  -- the low events
  let A : ℕ → Set (M.S × Fin 2) := fun n =>
    {p | (p.1 : ℝ) ≤ (19 / 20) ^ n * kb} ∩ Prod.snd ⁻¹' {0}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_le (continuous_subtype_val.comp continuous_fst).measurable measurable_const).inter
      (measurable_snd (measurableSet_singleton 0))
  have hlowA : ∀ n x, (9 / 10 : ℝ) ^ (n + 1) ≤ ((K ^ (n + 1)) x).real (A n) := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_one]
      have hx : (g x, (0 : Fin 2)) ∈ A 0 :=
        ⟨by simp only [pow_zero, one_mul]; exact (g x).2.2, rfl⟩
      have := le_policyKernel_real hQ0 g hg x (hAm 0) hx
      have hq : M.Q x.2 0 = 9 / 10 := rfl
      rw [hq] at this
      norm_num
      exact this
    | succ n ih =>
      intro x
      have := isMarkovKernel_pow K (n + 1)
      rw [pow_succ' K (n + 1)]
      have h := le_comp_real (η := K) (κ := K ^ (n + 1)) (hAm n) (hAm (n + 1))
        (q := 9 / 10) (by norm_num) ih (fun y hy => by
          have hy0 : y.2 = 0 := hy.2
          have hmem : (g y, (0 : Fin 2)) ∈ A (n + 1) := by
            refine ⟨?_, rfl⟩
            show (g y : ℝ) ≤ (19 / 20) ^ (n + 1) * kb
            have h1 := hdown y hy0
            have h2 : (y.1 : ℝ) ≤ (19 / 20) ^ n * kb := hy.1
            rw [pow_succ]
            nlinarith
          have := le_policyKernel_real hQ0 g hg y (hAm (n + 1)) hmem
          have hq : M.Q y.2 0 = 9 / 10 := rfl
          rwa [hq] at this) x
      rw [pow_succ]
      exact h
  -- the splitting state
  have hkb' : k / 100 ≤ kb := by linarith [slack_kh_le]
  let astar : M.S := ⟨k / 100, by positivity, hkb'⟩
  let c : M.S × Fin 2 := (astar, 0)
  have hδ : (0 : ℝ) < (9 / 10) ^ 321 := by positivity
  refine ProbabilityMeasure.toMeasure_injective (StochSavings.unique_stationary_of_splitting
    (M := M) hpol hg (fun _ _ _ => rfl) hmono (N := 321) (c := c) hδ ?_ ?_ hπ hπ')
  · intro x
    have hsub : A 320 ⊆ Iic c := by
      rintro p ⟨hp1, hp2⟩
      refine Prod.mk_le_mk.2 ⟨?_, le_of_eq hp2⟩
      show (p.1 : ℝ) ≤ k / 100
      have hp1' : (p.1 : ℝ) ≤ (19 / 20) ^ 320 * kb := hp1
      have hnum : (19 / 20 : ℝ) ^ 320 * 4000 ≤ 4 / 49 / 100 := by
        have h20 : (19 / 20 : ℝ) ^ 20 ≤ 9 / 25 := by norm_num
        have h16 : (19 / 20 : ℝ) ^ 320 ≤ (9 / 25) ^ 16 := by
          rw [show (320 : ℕ) = 20 * 16 from rfl, pow_mul]
          exact pow_le_pow_left₀ (by positivity) h20 16
        have h' : (9 / 25 : ℝ) ^ 16 * 4000 ≤ 4 / 49 / 100 := by norm_num
        generalize (19 / 20 : ℝ) ^ 320 = X at h16 ⊢
        linarith
      have : (19 / 20 : ℝ) ^ 320 * kb ≤ (19 / 20) ^ 320 * 4000 :=
        mul_le_mul_of_nonneg_left hkb (by positivity)
      generalize (19 / 20 : ℝ) ^ 320 = X at hp1' this hnum
      linarith
    have := isMarkovKernel_pow K 321
    exact (hlowA 320 x).trans (measureReal_mono hsub (measure_ne_top _ _))
  · intro x
    have h319 := isMarkovKernel_pow K 319
    have h320 := isMarkovKernel_pow K 320
    have hB1 : MeasurableSet (Prod.snd ⁻¹' {(1 : Fin 2)} : Set (M.S × Fin 2)) :=
      measurable_snd (measurableSet_singleton 1)
    have hB2 : MeasurableSet (Prod.fst ⁻¹' Ici astar : Set (M.S × Fin 2)) :=
      measurable_fst measurableSet_Ici
    have step1 : ∀ x, 1 * (1 / 10 : ℝ) ≤ ((K ^ 320) x).real (Prod.snd ⁻¹' {(1 : Fin 2)}) := by
      intro x
      rw [show (320 : ℕ) = 319 + 1 from rfl, pow_succ' K 319]
      exact le_comp_real (η := K) (κ := K ^ 319) MeasurableSet.univ hB1 (by norm_num)
        (fun x => by rw [probReal_univ]) (fun y _ => by
          have := le_policyKernel_real hQ0 g hg y hB1 (z₀ := 1) rfl
          have hq : M.Q y.2 1 = 1 / 10 := rfl
          rwa [hq] at this) x
    have step2 : 1 * (1 / 10 : ℝ) * (1 / 10) ≤ ((K ^ 321) x).real (Prod.fst ⁻¹' Ici astar) := by
      rw [show (321 : ℕ) = 320 + 1 from rfl, pow_succ' K 320]
      exact le_comp_real (η := K) (κ := K ^ 320) hB1 hB2 (by norm_num) step1 (fun y hy => by
        have hy1 : y.2 = 1 := hy
        have hsave : astar ≤ g y := by
          have := slack_saving_floor r g hpol y.1
          obtain ⟨a, z⟩ := y
          simp only at hy1
          subst hy1
          exact this
        have := le_policyKernel_real hQ0 g hg y hB2 (z₀ := 1) hsave
        have hq : M.Q y.2 1 = 1 / 10 := rfl
        rwa [hq] at this) x
    have hsub : (Prod.fst ⁻¹' Ici astar : Set (M.S × Fin 2)) ⊆ Ici c :=
      fun p hp => Prod.mk_le_mk.2 ⟨hp, Fin.zero_le _⟩
    have hnum : (9 / 10 : ℝ) ^ 321 ≤ 1 * (1 / 10) * (1 / 10) :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num : 44 ≤ 321)).trans
        (by norm_num)
    have := isMarkovKernel_pow K 321
    exact hnum.trans (step2.trans (measureReal_mono hsub (measure_ne_top _ _)))

/-- **At its interest rate, the Aiyagari example's equilibrium has a unique
stationary distribution** (uniqueness of the equilibrium rate is not claimed): there are an interest rate `-δ < r < 0`, the optimal policy
`g` and a stationary distribution `π` with capital-market clearing
`∫ a dπ = L k(r)` (the other equilibrium conditions are in
`slack_equilibrium`), a cap that never binds, wealth in `[0, 9 k̄ / 10]`,
and `π` is the only stationary distribution at `r`. -/
theorem slack_equilibrium_unique :
    ∃ r : Icc slackEconomy.rlo slackEconomy.rhi,
    ∃ (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (slackEconomy.household.S × Fin 2)),
      (∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel slackEconomy.Q g hg) π ∧
      (∀ π' : ProbabilityMeasure (slackEconomy.household.S × Fin 2),
        Kernel.Invariant (policyKernel slackEconomy.Q g hg) π' → π' = π) ∧
      ∫ s, slackEconomy.household.assets s ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.firm.capDemand slackEconomy.L r ∧
      (∀ s, (g s : ℝ) < slackEconomy.kbar) ∧
      (π : Measure (slackEconomy.household.S × Fin 2))
        {s | 9 / 10 * slackEconomy.kbar < (s.1 : ℝ)} = 0 ∧
      -slackEconomy.firm.δ < (r : ℝ) ∧ (r : ℝ) < 0 := by
  obtain ⟨r, g, hg, π, hpol, hinv, hK, -, -, -, -, -, hcap, hsupp, hr1, hr2⟩ := slack_equilibrium
  exact ⟨r, g, hg, π, hpol, hinv, fun π' hπ' => slack_stationary_unique r g hg hpol π π' hinv hπ',
    hK, hcap, hsupp, hr1, hr2⟩

end AiyagariEconomy

end Econ
