/-
# The BLP contraction mapping

Berry, Levinsohn and Pakes, "Automobile prices in market equilibrium",
*Econometrica* (1995), Appendix I; Berry (1994), §5.

**The algorithm.** To invert mixed-logit shares `σ(δ) = s`, BLP iterate
`T(δ) = δ + log s − log σ(δ)`; the fixed points of `T` are exactly the
solutions (`blpMap_fixed_iff`).

**The results.**

* **Strict contraction in the sup norm** (BLP Appendix I, their key property):
  for `δ ≠ δ'`, `‖T δ − T δ'‖∞ < ‖δ − δ'‖∞` (`blpMap_dist_lt`). The proof is
  direct, without derivatives: if utilities move by at most `c`, each type's
  logit denominator moves by a factor strictly inside `(e^{−c}, e^{c})` (the
  outside good does not move), so `log σⱼ` moves by strictly less than
  `δⱼ − δ'ⱼ ± c`.
* **Global convergence** (`blpMap_iterate_tendsto`): whenever the shares `s` are
  attained by some `δ*`, the iterates `Tⁿ δ⁰` converge to `δ*` from every
  starting point. The proof is Edelstein's argument: the distance to `δ*` is
  nonincreasing, and a limit point at positive distance would contradict the
  strict contraction.

Existence of `δ*` for the mixed logit (that every interior share vector is
attained) is not proved here; for the plain logit it is `BLP.share_surjective`.
-/
module

public import EconLean.Econometrics.Structural.BLP
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace Econ.Structural.BLP

open Real Finset Filter Topology

variable {J : Type*} [Fintype J] {I : Type*} [Fintype I]

/-- The logit denominator `1 + Σₖ exp(δₖ + μₖ)`. -/
noncomputable def denom (δ : J → ℝ) : ℝ := 1 + ∑ k, exp (δ k)

/-- **Denominator bounds**: if `|δₖ − δ'ₖ| ≤ c` for all `k` and `c > 0`, then
`e^{−c} D(δ') < D(δ) < e^{c} D(δ')`. -/
lemma denom_bounds {δ δ' : J → ℝ} {c : ℝ} (hc : 0 < c) (h : ∀ k, |δ k - δ' k| ≤ c) :
    exp (-c) * denom δ' < denom δ ∧ denom δ < exp c * denom δ' := by
  have hup : ∑ k, exp (δ k) ≤ exp c * ∑ k, exp (δ' k) := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [← exp_add]; exact exp_le_exp.mpr (by linarith [(abs_le.mp (h k)).2])
  have hlo : exp (-c) * ∑ k, exp (δ' k) ≤ ∑ k, exp (δ k) := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [← exp_add]; exact exp_le_exp.mpr (by linarith [(abs_le.mp (h k)).1])
  have h1 : 1 < exp c := one_lt_exp_iff.mpr hc
  have h2 : exp (-c) < 1 := by rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  simp only [denom]
  constructor <;> nlinarith

/-- The BLP map `T(δ) = δ + log s − log σ(δ)`. -/
noncomputable def blpMap (w : I → ℝ) (μ : I → J → ℝ) (s : J → ℝ) (δ : J → ℝ) : J → ℝ :=
  fun j => δ j + log (s j) - log (mixedShare w μ δ j)

lemma mixedShare_pos [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i) (μ : I → J → ℝ)
    (δ : J → ℝ) (j : J) : 0 < mixedShare w μ δ j :=
  sum_pos (fun i _ => mul_pos (hw i) (share_pos _ _)) univ_nonempty

/-- **Fixed points are the inverses**: `T δ = δ` iff `σ(δ) = s` (for positive `s`). -/
theorem blpMap_fixed_iff [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i) (μ : I → J → ℝ)
    {s : J → ℝ} (hs : ∀ j, 0 < s j) (δ : J → ℝ) :
    blpMap w μ s δ = δ ↔ mixedShare w μ δ = s := by
  constructor
  · intro h
    funext j
    have := congrFun h j
    simp only [blpMap] at this
    have hl : log (s j) = log (mixedShare w μ δ j) := by linarith
    exact (log_injOn_pos (mixedShare_pos hw μ δ j) (hs j) hl.symm)
  · intro h
    funext j
    simp [blpMap, h]

/-- Per-type share ratio bounds: `e^{dⱼ − c} < σᵢⱼ(δ)/σᵢⱼ(δ') < e^{dⱼ + c}`. -/
lemma share_ratio_bounds {δ δ' : J → ℝ} {c : ℝ} (hc : 0 < c) (h : ∀ k, |δ k - δ' k| ≤ c)
    (j : J) :
    exp (δ j - δ' j - c) * share δ' j < share δ j ∧
      share δ j < exp (δ j - δ' j + c) * share δ' j := by
  obtain ⟨hlo, hhi⟩ := denom_bounds hc h
  have hD : 0 < denom δ := denom_pos δ
  have hD' : 0 < denom δ' := denom_pos δ'
  have hs : share δ j = exp (δ j) / denom δ := rfl
  have hs' : share δ' j = exp (δ' j) / denom δ' := rfl
  have e1 : exp (δ j - δ' j - c) * share δ' j = exp (δ j) / (exp c * denom δ') := by
    rw [hs', exp_sub, exp_sub]; field_simp
  have e2 : exp (δ j - δ' j + c) * share δ' j = exp (δ j) / (exp (-c) * denom δ') := by
    rw [hs', exp_add, exp_sub, exp_neg]; field_simp
  rw [e1, e2, hs]
  have hp : 0 < exp (δ j) := exp_pos _
  exact ⟨div_lt_div_of_pos_left hp hD hhi,
    div_lt_div_of_pos_left hp (mul_pos (exp_pos _) hD') hlo⟩

/-- **The BLP map is a strict contraction in the sup norm** (BLP 1995, Appendix I):
for `δ ≠ δ'`, `‖T δ − T δ'‖ < ‖δ − δ'‖`. -/
theorem blpMap_dist_lt [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i) (μ : I → J → ℝ)
    (s : J → ℝ) {δ δ' : J → ℝ} (hne : δ ≠ δ') :
    dist (blpMap w μ s δ) (blpMap w μ s δ') < dist δ δ' := by
  set c := dist δ δ' with hcdef
  have hc : 0 < c := dist_pos.mpr hne
  -- shifted utilities of type `i`
  have hk : ∀ i k, |(δ + μ i) k - (δ' + μ i) k| ≤ c := by
    intro i k
    have := dist_le_pi_dist δ δ' k
    simpa [Real.dist_eq, Pi.add_apply] using this
  rw [dist_pi_lt_iff hc]
  intro j
  rw [Real.dist_eq]
  have hlo : exp (δ j - δ' j - c) * mixedShare w μ δ' j < mixedShare w μ δ j := by
    simp only [mixedShare, mul_sum]
    refine sum_lt_sum_of_nonempty univ_nonempty fun i _ => ?_
    have := (share_ratio_bounds hc (hk i) j).1
    have hsub : (δ + μ i) j - (δ' + μ i) j = δ j - δ' j := by simp
    rw [hsub] at this
    nlinarith [hw i]
  have hhi : mixedShare w μ δ j < exp (δ j - δ' j + c) * mixedShare w μ δ' j := by
    simp only [mixedShare, mul_sum]
    refine sum_lt_sum_of_nonempty univ_nonempty fun i _ => ?_
    have := (share_ratio_bounds hc (hk i) j).2
    have hsub : (δ + μ i) j - (δ' + μ i) j = δ j - δ' j := by simp
    rw [hsub] at this
    nlinarith [hw i]
  have hp := mixedShare_pos hw μ δ j
  have hp' := mixedShare_pos hw μ δ' j
  have l1 := log_lt_log (mul_pos (exp_pos _) hp') hlo
  have l2 := log_lt_log hp hhi
  rw [log_mul (exp_pos _).ne' hp'.ne', log_exp] at l1
  rw [log_mul (exp_pos _).ne' hp'.ne', log_exp] at l2
  simp only [blpMap]
  rw [abs_lt]
  constructor <;> linarith

/-- The BLP map is continuous (on positive shares). -/
lemma continuous_blpMap [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i) (μ : I → J → ℝ)
    (s : J → ℝ) : Continuous (blpMap w μ s) := by
  refine continuous_pi fun j => ?_
  have hsh : Continuous (fun δ : J → ℝ => mixedShare w μ δ j) := by
    simp only [mixedShare, share]
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine Continuous.div (by fun_prop) (by fun_prop) fun δ => (denom_pos (δ + μ i)).ne'
  exact ((continuous_apply j).add continuous_const).sub
    (hsh.log fun δ => (mixedShare_pos hw μ δ j).ne')

/-- **Global convergence of the BLP contraction** (Edelstein's argument): if
`σ(δ*) = s`, then `Tⁿ δ⁰ → δ*` for every starting point `δ⁰`. -/
theorem blpMap_iterate_tendsto [Nonempty I] {w : I → ℝ} (hw : ∀ i, 0 < w i)
    (μ : I → J → ℝ) {s : J → ℝ} {δstar : J → ℝ}
    (hstar : mixedShare w μ δstar = s) (δ₀ : J → ℝ) :
    Tendsto (fun n => (blpMap w μ s)^[n] δ₀) atTop (𝓝 δstar) := by
  have hs : ∀ j, 0 < s j := fun j => hstar ▸ mixedShare_pos hw μ δstar j
  set T := blpMap w μ s
  have hfix : T δstar = δstar := (blpMap_fixed_iff hw μ hs δstar).mpr hstar
  have hle : ∀ x, dist (T x) δstar ≤ dist x δstar := by
    intro x
    by_cases hx : x = δstar
    · subst hx; rw [hfix]
    · have := blpMap_dist_lt hw μ s hx
      change dist (T x) (T δstar) < _ at this
      rw [hfix] at this; exact this.le
  set d : ℕ → ℝ := fun n => dist (T^[n] δ₀) δstar
  have hd_anti : Antitone d := antitone_nat_of_succ_le fun n => by
    simp only [d, Function.iterate_succ_apply']
    exact hle _
  obtain ⟨r, hr⟩ : ∃ r, Tendsto d atTop (𝓝 r) :=
    ⟨_, tendsto_atTop_ciInf hd_anti ⟨0, fun _ ⟨n, hn⟩ => hn ▸ dist_nonneg⟩⟩
  -- all iterates lie in a closed ball, which is compact
  have hball : ∀ n, T^[n] δ₀ ∈ Metric.closedBall δstar (d 0) := fun n =>
    Metric.mem_closedBall.mpr (hd_anti (Nat.zero_le n))
  obtain ⟨y, -, φ, hφ, hφy⟩ :=
    (isCompact_closedBall δstar (d 0)).tendsto_subseq hball
  have hdy : dist y δstar = r := by
    have h1 : Tendsto (fun k => d (φ k)) atTop (𝓝 (dist y δstar)) :=
      (hφy.dist tendsto_const_nhds)
    exact tendsto_nhds_unique h1 (hr.comp hφ.tendsto_atTop)
  have hTy : dist (T y) δstar = r := by
    have hc := (continuous_blpMap hw μ s).tendsto y
    have h1 : Tendsto (fun k => d (φ k + 1)) atTop (𝓝 (dist (T y) δstar)) := by
      simp only [d, Function.iterate_succ_apply']
      exact (hc.comp hφy).dist tendsto_const_nhds
    exact tendsto_nhds_unique h1
      (hr.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop))
  have hr0 : r = 0 := by
    by_contra hr0
    have hy : y ≠ δstar := by
      intro h; rw [h, dist_self] at hdy; exact hr0 hdy.symm
    have := blpMap_dist_lt hw μ s hy
    change dist (T y) (T δstar) < _ at this
    rw [hfix, hdy, hTy] at this
    exact lt_irrefl _ this
  rw [hr0] at hr
  exact tendsto_iff_dist_tendsto_zero.mpr hr

/-- **Non-vacuity**: in a one-type, two-product logit market with shares
`s = σ(0)`, the BLP iteration started at `δ⁰ = (5, 5)` converges to `0`. -/
theorem blp_contraction_witness :
    Tendsto (fun n => (blpMap (fun _ : Unit => (1 : ℝ)) (fun _ => 0)
      (share (0 : Fin 2 → ℝ)))^[n] (fun _ => 5)) atTop (𝓝 0) :=
  blpMap_iterate_tendsto (fun _ => one_pos) _ (mixedShare_unit 0) _

end Econ.Structural.BLP
