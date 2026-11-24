/-
# Aiyagari equilibrium with a non-binding asset cap

Aiyagari (1994); Ljungqvist–Sargent ch. 18.2.

`AiyagariGE.exists_stationary_equilibrium` proves existence of a stationary
recursive competitive equilibrium in an economy with an *exogenous* asset cap
`k̄`. This file shows the cap can be made irrelevant, and gives a fully derived
example with income risk in which it is.

**Asset bound for negative rates** (`policy_le_max`). If the top rate
`r_hi < 0`, efficiency units are bounded by `ē`, and the wage is decreasing in
`r` (`CDFirm.wage_anti`), then at every `r ∈ [r_lo, r_hi]` next-period assets
satisfy `a' ≤ max(A, a)` and `a' < a` above `A = w(r_lo) ē / (-r_hi)`.

**Equilibrium with a slack cap** (`exists_stationary_equilibrium_slack`). If
moreover `A < k̄`, the equilibrium of `exists_stationary_equilibrium` has
`a' < k̄` in every state, a stationary distribution on `[0, A]`, and
`-δ < r < 0`, so `β (1 + r) < 1`. (Here `r < 0`, hence the Aiyagari inequality
`r < 1/β - 1`, comes from the choice of the bracket `r_hi < 0`; it is not
derived from the household problem.)

**Supply from precautionary saving** (`supply_ge_of_save`). If households in
state `z_h` always save at least `m`, every stationary distribution has
`∫ a dπ ≥ m q̄(z_h)`. This derives the upper boundary condition.

**A fully derived example** (`slackEconomy`, `slack_equilibrium`). `u = √c`,
`β = 9/10`, i.i.d. employment shock: unemployed (`e = 0`) with probability
`9/10`, employed (`e = 1`) with probability `1/10`, so `L = 1/10`; Cobb–Douglas
firm with `α = 1/10`, `δ = 2/5`; rates `r ∈ [-799/2000, -1/20]`; cap
`k̄ = L k(r_lo)`. Every hypothesis is proved, and the equilibrium has
`-δ < r < 0`, positive capital, a cap that never binds, and wealth in
`[0, 9 k̄ / 10]`.

**Scope.** The cap is still part of the household's problem (needed for the
compact-state DP); the result is that it never binds at the equilibrium. Rates
are confined to `r < 0`, where the asset bound is elementary; the canonical
bound for `0 ≤ r < 1/β - 1` needs the Euler-equation argument of
`AssetBound` with Markov income and is open. The depreciation rate `δ = 2/5`
is high so that the bracket `(-δ, 0)` is wide enough for a crude saving bound.
The borrowing limit is `0`. The example is chosen for provability, not
realism: 90% of households are unemployed (`L = 1/10`), the bracket reaches
down to `r_lo = -0.3995`, and a numerical solve puts the equilibrium rate near
`r ≈ -0.25`.
-/
module

public import EconLean.Macro.HA.Huggett

@[expose] public section

namespace Econ

open Set Filter Topology MeasureTheory ProbabilityTheory BoundedContinuousFunction

namespace CDFirm

variable (F : CDFirm)

/-- The wage in terms of the capital–labor ratio:
`w(r) = (1 - α)(r + δ)/α · k(r)` (from `α k^{α-1} = r + δ`). -/
theorem wage_eq_mul_kOfR {r : ℝ} (hr : -F.δ < r) :
    F.wage r = (1 - F.α) * (r + F.δ) / F.α * F.kOfR r := by
  have hk := F.kOfR_pos hr
  have hα := F.α_pos
  have hf := F.foc_capital hr
  have h1 : F.kOfR r ^ F.α = F.kOfR r ^ (F.α - 1) * F.kOfR r := by
    rw [← Real.rpow_add_one hk.ne', sub_add_cancel]
  have h2 : F.kOfR r ^ (F.α - 1) = (r + F.δ) / F.α := by
    rw [← hf]; field_simp
  rw [CDFirm.wage, h1, h2]
  ring

/-- The wage is decreasing in the interest rate. -/
theorem wage_anti {r r' : ℝ} (hr : -F.δ < r) (hrr : r ≤ r') : F.wage r' ≤ F.wage r := by
  have hr' : -F.δ < r' := lt_of_lt_of_le hr hrr
  have hk : F.kOfR r' ≤ F.kOfR r := F.strictAntiOn_kOfR.antitoneOn hr hr' hrr
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (F.kOfR_pos hr').le hk F.α_pos.le) F.one_sub_α_pos.le

end CDFirm

namespace AiyagariEconomy

variable {Z : Type*} [Fintype Z] (E : AiyagariEconomy Z)

variable [TopologicalSpace Z] [DiscreteTopology Z]

/-- **An asset bound for negative interest rates**: if `r_hi < 0` and
`e ≤ ē`, then with `A = w(r_lo) ē / (-r_hi)`, at every `r ∈ [r_lo, r_hi]`,
`a' ≤ max(A, a)`, and `a' < a` whenever `a > A`. The bound does not depend on
the cap `k̄`. -/
theorem policy_le_max (hrhi : E.rhi < 0) {ebar : ℝ} (heb : ∀ z, E.e z ≤ ebar)
    (r : Icc E.rlo E.rhi) {g : E.household.S × Z → E.household.S}
    (hg : ∀ s, (E.household.slice r).toStochDynProg.policy s = {g s}) (s : E.household.S × Z) :
    (g s : ℝ) ≤ max (E.firm.wage E.rlo * ebar / (-E.rhi)) s.1 ∧
      (E.firm.wage E.rlo * ebar / (-E.rhi) < s.1 → (g s : ℝ) < s.1) := by
  set A := E.firm.wage E.rlo * ebar / (-E.rhi)
  have hne : E.rhi ≠ 0 := hrhi.ne
  have hA : -E.rhi * A = E.firm.wage E.rlo * ebar := by simp only [A]; field_simp
  have hfeas := StochSavings.feasible hg s
  have hh : (E.household.slice r).h s.1 s.2 = (1 + (r : ℝ)) * s.1 + E.firm.wage r * E.e s.2 :=
    rfl
  have hb : (0 : ℝ) ≤ s.1 := s.1.2.1
  have h1 : (1 + (r : ℝ)) * s.1 ≤ (1 + E.rhi) * s.1 :=
    mul_le_mul_of_nonneg_right (by linarith [r.2.2]) hb
  have hw : E.firm.wage r * E.e s.2 ≤ E.firm.wage E.rlo * ebar :=
    (mul_le_mul_of_nonneg_right (E.firm.wage_anti E.rlo_gt r.2.1) (E.e_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (heb _) (E.firm.wage_pos E.rlo_gt).le)
  have hge : -1 ≤ E.rhi := E.rlo_ge.trans E.rlo_le
  have hbound : (g s : ℝ) ≤ s.1 + -E.rhi * (A - s.1) := by
    rw [hh] at hfeas; nlinarith
  refine ⟨?_, fun hs => ?_⟩
  · rcases le_total (s.1 : ℝ) A with h | h
    · refine hbound.trans (le_trans ?_ (le_max_left _ _))
      nlinarith
    · exact hbound.trans ((by nlinarith : (s.1 : ℝ) + -E.rhi * (A - s.1) ≤ s.1).trans
        (le_max_right _ _))
  · nlinarith

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Supply from precautionary saving**: if households in state `z_h` always
save at least `m`, every stationary distribution has `∫ a dπ ≥ m q̄(z_h)`. -/
theorem supply_ge_of_save [DecidableEq Z] (g : E.household.S × Z → E.household.S)
    (hg : Measurable g) (zh : Z) (m : ℝ) (hsave : ∀ a, m ≤ g (a, zh))
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
  · obtain ⟨a, z⟩ := s
    simp only at h
    subst h
    exact hsave a
  · exact (g s).2.1

variable [Nonempty Z]

/-- **Aiyagari equilibrium with a slack cap**: under the boundary conditions of
`exists_stationary_equilibrium`, if moreover `r_hi < 0`, `e ≤ ē` and
`A = w(r_lo) ē / (-r_hi) < k̄`, there is a stationary recursive competitive
equilibrium (all the market-clearing and optimality conditions of
`exists_stationary_equilibrium`) in which the cap never binds (`a' < k̄` in
every state), the stationary distribution of wealth lives on `[0, A]`, and
`-δ < r < 0` (so `β (1 + r) < 1`; `r < 0` comes from the bracket `r_hi < 0`). -/
theorem exists_stationary_equilibrium_slack [DecidableEq Z]
    (hlo : E.kbar ≤ E.firm.capDemand E.L E.rlo)
    (hhi : ∀ (g : E.household.S × Z → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Z), Kernel.Invariant (policyKernel E.Q g hg) μ ∧
        E.firm.capDemand E.L E.rhi ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Z)))
    (hrhi : E.rhi < 0) {ebar : ℝ} (heb : ∀ z, E.e z ≤ ebar)
    (hAk : E.firm.wage E.rlo * ebar / (-E.rhi) < E.kbar) :
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
        E.firm.output (∫ s, E.household.assets s ∂(π : Measure (E.household.S × Z))) E.L ∧
      (∀ s, (g s : ℝ) < E.kbar) ∧
      (π : Measure (E.household.S × Z))
        {s | E.firm.wage E.rlo * ebar / (-E.rhi) < (s.1 : ℝ)} = 0 ∧
      -E.firm.δ < (r : ℝ) ∧ (r : ℝ) < 0 := by
  obtain ⟨r, g, hg, π, hpol, hinv, hK, hlab, hfoc1, hfoc2, hgoods⟩ :=
    E.exists_stationary_equilibrium hlo hhi
  have hb := E.policy_le_max hrhi heb r hpol
  refine ⟨r, g, hg, π, hpol, hinv, hK, hlab, hfoc1, hfoc2, hgoods, fun s => ?_, ?_,
    E.mem_Ioi, lt_of_le_of_lt r.2.2 hrhi⟩
  · rcases le_or_gt (s.1 : ℝ) (E.firm.wage E.rlo * ebar / (-E.rhi)) with h | h
    · have := (hb s).1
      rw [max_eq_left h] at this
      linarith
    · exact ((hb s).2 h).trans_le s.1.2.2
  · exact StochSavings.measure_gt_eq_zero_of_bound (M := E.household.slice r)
      (StochSavings.continuous_of_policy hpol) (fun s => (hb s).1) (fun s => (hb s).2) hg _ hinv

end AiyagariEconomy

/-! ### A fully derived example -/

/-- The Cobb–Douglas firm with `α = 1/10`, `δ = 2/5`. -/
noncomputable def CDFirm.tenth : CDFirm where
  α := 1 / 10
  δ := 2 / 5
  α_pos := by norm_num
  α_lt_one := by norm_num
  δ_nonneg := by norm_num

/-- The i.i.d. employment chain: unemployed with probability `9/10`. -/
noncomputable def unempQ : Fin 2 → Fin 2 → ℝ := fun _ z' => ![9 / 10, 1 / 10] z'

theorem unempQ_isInvariant :
    IsInvariant (unempQ : Matrix (Fin 2) (Fin 2) ℝ) ![9 / 10, 1 / 10] := by
  refine ⟨⟨fun z => by fin_cases z <;> norm_num, by norm_num [Fin.sum_univ_two]⟩, ?_⟩
  funext z
  fin_cases z <;> norm_num [unempQ, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem tenth_rlo : -CDFirm.tenth.δ < -799 / 2000 := by norm_num [CDFirm.tenth]

/-- **An Aiyagari economy with income risk and a slack cap**: `u = √c`,
`β = 9/10`, i.i.d. employment shock (`e = 0` with probability `9/10`, `e = 1`
with probability `1/10`, so `L = 1/10`), Cobb–Douglas firm with `α = 1/10`,
`δ = 2/5`, interest rates `r ∈ [-799/2000, -1/20]`, and cap
`k̄ = k(r_lo)/10 = L k(r_lo)` (capital demand at the lowest rate). -/
noncomputable def AiyagariEconomy.slackEconomy : AiyagariEconomy (Fin 2) where
  u := Real.sqrt
  Q := unempQ
  β := 9 / 10
  kbar := 1 / 10 * CDFirm.tenth.kOfR (-799 / 2000)
  e := ![0, 1]
  firm := CDFirm.tenth
  rlo := -799 / 2000
  rhi := -1 / 20
  qbar := ![9 / 10, 1 / 10]
  Q_nonneg := fun _ z' => by fin_cases z' <;> norm_num [unempQ]
  Q_sum := fun _ => by norm_num [unempQ, Fin.sum_univ_two]
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := mul_pos (by norm_num) (CDFirm.tenth.kOfR_pos tenth_rlo)
  u_continuous := Real.continuous_sqrt
  u_mono := fun _ _ _ _ h => Real.sqrt_le_sqrt h
  u_strictConcave := Real.strictConcaveOn_sqrt
  e_nonneg := fun z => by fin_cases z <;> norm_num
  rlo_gt := tenth_rlo
  rlo_ge := by norm_num
  rlo_le := by norm_num
  qbar_inv := unempQ_isInvariant
  qbar_unique := fun π hπ => by
    have hQ : IsStochastic (unempQ : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨fun _ z' => by fin_cases z' <;> norm_num [unempQ],
        fun _ => by norm_num [unempQ, Fin.sum_univ_two]⟩
    obtain ⟨π₀, -, hu, -⟩ := doeblin hQ (ε := 1 / 10) (by norm_num)
      (fun _ z' => by fin_cases z' <;> norm_num [unempQ])
    rw [hu π hπ, ← hu _ unempQ_isInvariant]
  labor_pos := by norm_num [Fin.sum_univ_two]

namespace AiyagariEconomy

theorem slack_L : slackEconomy.L = 1 / 10 := by
  norm_num [L, slackEconomy, Fin.sum_univ_two]

/-- At `r_hi = -1/20` capital per worker is at most `1`, below the cap
`k̄ ≥ 20`. -/
theorem slack_kh_le : CDFirm.tenth.kOfR (-1 / 20) ≤ slackEconomy.kbar := by
  have h1 : CDFirm.tenth.kOfR (-1 / 20) ≤ 1 := by
    rw [CDFirm.kOfR]
    exact Real.rpow_le_one (by norm_num [CDFirm.tenth]) (by norm_num [CDFirm.tenth])
      (by norm_num [CDFirm.tenth])
  have h2 : 200 ≤ CDFirm.tenth.kOfR (-799 / 2000) := by
    rw [CDFirm.kOfR]
    have hb : CDFirm.tenth.α / (-799 / 2000 + CDFirm.tenth.δ) = 200 := by
      norm_num [CDFirm.tenth]
    have he : (1 : ℝ) ≤ 1 / (1 - CDFirm.tenth.α) := by norm_num [CDFirm.tenth]
    rw [hb]
    calc (200 : ℝ) = 200 ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ 200 ^ (1 / (1 - CDFirm.tenth.α)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  show _ ≤ 1 / 10 * CDFirm.tenth.kOfR (-799 / 2000)
  linarith

/-- **Precautionary saving at `r_hi = -1/20`**: employed households save at
least `k(r_hi)` (the capital per worker demanded at `r_hi`), whatever their
wealth, although `r < 0` and `β (1 + r) < 1`. (The risk of unemployment
tomorrow, with zero labor income, makes wealth very valuable.) -/
theorem slack_saving
    (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S)
    (hg : ∀ s, (slackEconomy.household.slice ⟨slackEconomy.rhi, slackEconomy.rlo_le, le_rfl⟩
      ).toStochDynProg.policy s = {g s})
    (a : slackEconomy.household.S) : CDFirm.tenth.kOfR (-1 / 20) ≤ g (a, 1) := by
  let M := slackEconomy.household.slice ⟨slackEconomy.rhi, slackEconomy.rlo_le, le_rfl⟩
  set k := CDFirm.tenth.kOfR (-1 / 20) with hkdef
  have hk : 0 < k := CDFirm.tenth.kOfR_pos (by norm_num [CDFirm.tenth])
  have hw : CDFirm.tenth.wage (-1 / 20) = 63 / 20 * k := by
    rw [CDFirm.tenth.wage_eq_mul_kOfR (by norm_num [CDFirm.tenth]), ← hkdef]
    norm_num [CDFirm.tenth]
  have hh : ∀ (b : ℝ) (z : Fin 2), M.h b z = 19 / 20 * b + 63 / 20 * k * ![(0 : ℝ), 1] z :=
    fun b z => by
      show (1 + (-1 / 20 : ℝ)) * b + CDFirm.tenth.wage (-1 / 20) * ![(0 : ℝ), 1] z = _
      rw [hw]; ring
  have he0 : ![(0 : ℝ), 1] 0 = 0 := rfl
  have he1 : ![(0 : ℝ), 1] 1 = 1 := rfl
  let m : M.S := ⟨k, hk.le, slack_kh_le⟩
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  show ((m : M.S) : ℝ) ≤ g (a, 1)
  refine StochSavings.le_policy_at (M := M) hg (a, 1) m ?_ (fun z' b b' hbb => ?_)
    (fun y x hy hx => ?_)
  · show k ≤ M.h a 1
    rw [hh, he1]; nlinarith
  · rw [hh, hh]; linarith
  · have hm : ((m : M.S) : ℝ) = k := rfl
    rw [hm] at hy
    have hyy : (0 : ℝ) ≤ y := y.2.1
    simp only [hh, hm, he1] at hx ⊢
    show _ < (9 / 10 : ℝ) * ∑ z' : Fin 2, unempQ 1 z' * _
    rw [Fin.sum_univ_two]
    simp only [he0, he1, unempQ]
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one]
    set d := k - (y : ℝ)
    have hd : 0 < d := by simp only [d]; linarith
    set t := Real.sqrt k
    have ht : 0 < t := Real.sqrt_pos.2 hk
    have ht2 : t ^ 2 = k := Real.sq_sqrt hk.le
    set H := 19 / 20 * (a : ℝ) + 63 / 20 * k * 1
    -- cost today `≤ d / (2.92 t)`
    have hcost : (Real.sqrt (H - y) - Real.sqrt (H - k)) * (292 / 100 * t) ≤ d := by
      have hQ : (0 : ℝ) < H - k := by simp only [H]; nlinarith
      have h1 := sqrt_sub_le_div (P := H - y) hQ (by linarith)
      have hs : 146 / 100 * t ≤ Real.sqrt (H - k) :=
        (Real.le_sqrt (by positivity) hQ.le).2 (by rw [mul_pow, ht2]; simp only [H]; nlinarith)
      rw [show H - y - (H - k) = d by simp only [d]; ring] at h1
      rw [le_div_iff₀ (by positivity)] at h1
      have hc0 : 0 ≤ Real.sqrt (H - y) - Real.sqrt (H - k) :=
        sub_nonneg.2 (Real.sqrt_le_sqrt (by linarith))
      nlinarith
    -- gain tomorrow when unemployed `≥ 0.95 d / (1.95 t)`
    have hx0 := hx 0
    have hx1 := hx 1
    simp only [he0, he1] at hx0 hx1
    have hX0 : (0 : ℝ) ≤ x 0 := (x 0).2.1
    have hgain0 : 95 / 100 * d ≤ (Real.sqrt (19 / 20 * k + 63 / 20 * k * 0 - x 0) -
        Real.sqrt (19 / 20 * y + 63 / 20 * k * 0 - x 0)) * (195 / 100 * t) := by
      have hP : (0 : ℝ) < 19 / 20 * k + 63 / 20 * k * 0 - x 0 := by nlinarith
      have h1 := div_le_sqrt_sub (B := 19 / 20 * y + 63 / 20 * k * 0 - x 0)
        (by linarith) (by nlinarith) hP
      have hsP : Real.sqrt (19 / 20 * k + 63 / 20 * k * 0 - x 0) ≤ 975 / 1000 * t :=
        Real.sqrt_le_iff.2 ⟨by positivity, by rw [mul_pow, ht2]; nlinarith⟩
      have hpos := Real.sqrt_pos.2 hP
      rw [show 19 / 20 * k + 63 / 20 * k * 0 - x 0 - (19 / 20 * y + 63 / 20 * k * 0 - x 0) =
        19 / 20 * d by simp only [d]; ring] at h1
      rw [div_le_iff₀ (by positivity)] at h1
      nlinarith
    have hgain1 : 0 ≤ Real.sqrt (19 / 20 * k + 63 / 20 * k * 1 - x 1) -
        Real.sqrt (19 / 20 * y + 63 / 20 * k * 1 - x 1) :=
      sub_nonneg.2 (Real.sqrt_le_sqrt (by nlinarith))
    have hu : M.u = Real.sqrt := rfl
    rw [hu]
    nlinarith

/-- The asset bound of the example: `A = w(r_lo) · 1 / (1/20) = 9 k̄ / 10`. -/
theorem slack_A :
    slackEconomy.firm.wage slackEconomy.rlo * 1 / (-slackEconomy.rhi) =
      9 / 10 * slackEconomy.kbar := by
  show CDFirm.tenth.wage (-799 / 2000) * 1 / (-(-1 / 20)) =
    9 / 10 * (1 / 10 * CDFirm.tenth.kOfR (-799 / 2000))
  rw [CDFirm.tenth.wage_eq_mul_kOfR tenth_rlo]
  norm_num [CDFirm.tenth]
  ring

/-- **The example has a stationary recursive competitive equilibrium with
every hypothesis derived**: an interest rate `-δ < r < 0` (so `β (1 + r) < 1`),
the optimal policy `g` and a stationary distribution `π` with capital, labor
and goods markets clearing and the firm's first-order conditions holding,
positive capital, a cap `k̄` that never binds, and wealth in `[0, 9 k̄ / 10]`. -/
theorem slack_equilibrium :
    ∃ r : Icc slackEconomy.rlo slackEconomy.rhi,
    ∃ (g : slackEconomy.household.S × Fin 2 → slackEconomy.household.S) (hg : Measurable g)
      (π : ProbabilityMeasure (slackEconomy.household.S × Fin 2)),
      (∀ s, (slackEconomy.household.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel slackEconomy.Q g hg) π ∧
      ∫ s, slackEconomy.household.assets s ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.firm.capDemand slackEconomy.L r ∧
      ∫ s, slackEconomy.e s.2 ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.L ∧
      slackEconomy.firm.α * ((∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2))) / slackEconomy.L) ^
        (slackEconomy.firm.α - 1) = r + slackEconomy.firm.δ ∧
      slackEconomy.firm.wage r = (1 - slackEconomy.firm.α) *
        ((∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2))) / slackEconomy.L) ^
            slackEconomy.firm.α ∧
      ∫ s, ((1 + (r : ℝ)) * (s.1 : ℝ) + slackEconomy.firm.wage r * slackEconomy.e s.2 -
          (g s : ℝ)) ∂(π : Measure (slackEconomy.household.S × Fin 2)) +
        slackEconomy.firm.δ * ∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2)) =
        slackEconomy.firm.output (∫ s, slackEconomy.household.assets s
          ∂(π : Measure (slackEconomy.household.S × Fin 2))) slackEconomy.L ∧
      0 < ∫ s, slackEconomy.household.assets s ∂(π : Measure (slackEconomy.household.S × Fin 2)) ∧
      (∀ s, (g s : ℝ) < slackEconomy.kbar) ∧
      (π : Measure (slackEconomy.household.S × Fin 2))
        {s | 9 / 10 * slackEconomy.kbar < (s.1 : ℝ)} = 0 ∧
      -slackEconomy.firm.δ < (r : ℝ) ∧ (r : ℝ) < 0 := by
  set E := slackEconomy
  have hL : E.L = 1 / 10 := slack_L
  have hlo : E.kbar ≤ E.firm.capDemand E.L E.rlo := by
    rw [CDFirm.capDemand, hL]; exact le_rfl
  have hhi : ∀ (g : E.household.S × Fin 2 → E.household.S) (hg : Measurable g),
      (∀ s, (E.household.slice ⟨E.rhi, E.rlo_le, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (E.household.S × Fin 2),
        Kernel.Invariant (policyKernel E.Q g hg) μ ∧
        E.firm.capDemand E.L E.rhi ≤ ∫ s, E.household.assets s ∂(μ : Measure (E.household.S × Fin 2)) :=
    fun g hg hpol => by
      obtain ⟨μ, hμ⟩ := E.household.exists_stationary_of_policy _ g hg hpol
      refine ⟨μ, hμ, ?_⟩
      have := E.supply_ge_of_save g hg 1 _ (slack_saving g hpol) μ hμ
      have hq : E.qbar 1 = 1 / 10 := rfl
      rw [hq] at this
      rw [CDFirm.capDemand, hL]
      have hk : E.firm.kOfR E.rhi = CDFirm.tenth.kOfR (-1 / 20) := rfl
      rw [hk]
      linarith
  have heb : ∀ z, E.e z ≤ 1 := fun z => by fin_cases z <;> norm_num [E, slackEconomy]
  have hAk : E.firm.wage E.rlo * 1 / (-E.rhi) < E.kbar := by
    rw [slack_A]; linarith [E.kbar_pos]
  obtain ⟨r, g, hg, π, hpol, hinv, hK, hlab, hfoc1, hfoc2, hgoods, hcap, hsupp, hr1, hr2⟩ :=
    E.exists_stationary_equilibrium_slack hlo hhi (by norm_num [E, slackEconomy]) heb hAk
  rw [slack_A] at hsupp
  have hKpos : 0 < E.firm.capDemand E.L r := by
    rw [CDFirm.capDemand, hL]; exact mul_pos (by norm_num) (E.firm.kOfR_pos hr1)
  exact ⟨r, g, hg, π, hpol, hinv, hK, hlab, hfoc1, hfoc2, hgoods, hK ▸ hKpos, hcap, hsupp, hr1, hr2⟩

end AiyagariEconomy

end Econ
