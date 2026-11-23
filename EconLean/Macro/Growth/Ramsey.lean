/-
# The Ramsey–Cass–Koopmans model: optimal growth via dynamic programming

Stokey–Lucas (SL) §2.1, §4.2–4.3, §6.1 (Thms 6.1–6.2); Acemoglu,
*Introduction to Modern Economic Growth*, ch. 6 and 8 (discrete time).

**The model.** A planner chooses consumption and next period's capital,

  `max Σ_t β^t u(c_t)`  s.t.  `c_t + k_{t+1} ≤ f(k_t)`,  `c_t, k_{t+1} ≥ 0`,

where `f(k)` is *total resources* (output plus undepreciated capital, SL's
`f`). In recursive form: state `k`, choice `y = k'` with `0 ≤ y ≤ f(k)`, and
return `F(k, y) = u(f(k) - y)`.

**Assumptions** (SL Assumptions 6.1–6.2 / 4.3–4.8 for this model): `u` and
`f` are continuous, strictly increasing and strictly concave on `[0, ∞)`,
`0 < β < 1`, `f(0) = 0`, and there is a maximal sustainable capital stock
`k̄ > 0` with `f(k) ≤ k̄` on `[0, k̄]`, so the state space is `[0, k̄]`.

**Results.**
* The model is a `DynProg` (SL Assumptions 4.3–4.4 hold), so the value
  function exists, is unique, is strictly increasing and strictly concave, and
  the optimal policy `g` is a continuous function (SL Thms 4.6–4.8).
* `g` is **nondecreasing** (more capital today ⇒ more capital tomorrow), by
  increasing differences of `u(f(k) - y)` (Topkis; SL Thm 6.1).
* **Monotone convergence** (SL Thm 6.2): from any `k₀`, the optimal capital
  path `k_{t+1} = g(k_t)` is monotone and converges to a steady state
  `g(k_∞) = k_∞`; this path is the unique optimal plan.
* **Modified golden rule**: at an interior steady state with positive
  consumption, `β f'(k*) = 1` (via Benveniste–Scheinkman and the first-order
  condition); and at most one `k* > 0` satisfies it.

**Documented deviations.** `u` is assumed continuous on all of `ℝ` (only its
values on `[0, k̄]` matter; any `u` on `[0, ∞)` extends as `u ∘ max(·, 0)`),
because our `DynProg` needs `F` continuous on the whole product. `u` must be
finite and continuous at `c = 0`, so log and CRRA utility with `σ ≥ 1` are
excluded (as in SL's bounded case). Both directions of the modified golden
rule are proved (an interior steady state satisfies `β f'(k*) = 1`, and the
`k*` solving it is a steady state), and the `√` example witnesses an interior
steady state. Still open: with Inada-type conditions, every path from
`k₀ > 0` converges to `k*` (not to the trivial steady state `0`; SL Thm 6.2 /
Acemoglu Prop. 6.3); strict monotonicity of `g` and monotonicity of
consumption (SL ch. 6).
-/
module

public import EconLean.Macro.DP.Concavity
public import EconLean.Macro.DP.Monotone
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace Econ

open Filter Topology Set

/-- Primitives of the Ramsey–Cass–Koopmans (one-sector optimal growth) model. -/
structure RCKModel where
  /-- period utility of consumption -/
  u : ℝ → ℝ
  /-- total resources `f(k)` = output plus undepreciated capital -/
  f : ℝ → ℝ
  /-- discount factor -/
  β : ℝ
  /-- maximal sustainable capital stock -/
  kbar : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  kbar_pos : 0 < kbar
  u_continuous : Continuous u
  u_strictMono : StrictMonoOn u (Ici 0)
  u_strictConcave : StrictConcaveOn ℝ (Ici 0) u
  f_continuous : Continuous f
  f_zero : f 0 = 0
  f_strictMono : StrictMonoOn f (Ici 0)
  f_strictConcave : StrictConcaveOn ℝ (Ici 0) f
  f_le : ∀ k ∈ Icc 0 kbar, f k ≤ kbar

/-! ### Strictly concave functions: two calculus facts -/

/-- **Strictly decreasing increments**: for strictly concave `u` on `[0, ∞)`,
shifting an interval `[p, q]` to the right by `d > 0` strictly lowers the
increment of `u`. This is the increasing-differences property of
`u(f(k) - y)`. -/
theorem StrictConcaveOn.increment_lt {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Ici 0) u)
    {p q d : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hd : 0 < d) :
    u (q + d) - u (p + d) < u q - u p := by
  have hq : (0 : ℝ) ≤ q := by linarith
  have mem : ∀ x : ℝ, 0 ≤ x → x ∈ Ici (0 : ℝ) := fun x hx => hx
  -- secant from `p`: slope to `q + d` is below slope to `q`
  have s1 := hu.secant_strict_mono (mem p hp) (mem q hq) (mem (q + d) (by linarith))
    (by linarith : q ≠ p) (by linarith : q + d ≠ p) (by linarith : q < q + d)
  -- secant from `q + d`: slope to `p + d` is below slope to `p`
  have s2 := hu.secant_strict_mono (mem (q + d) (by linarith)) (mem p hp) (mem (p + d) (by linarith))
    (by linarith : p ≠ q + d) (by linarith : p + d ≠ q + d) (by linarith : p < p + d)
  have L : 0 < q - p := by linarith
  have e1 : (u (p + d) - u (q + d)) / (p + d - (q + d)) = (u (q + d) - u (p + d)) / (q - p) := by
    rw [show p + d - (q + d) = -(q - p) by ring, div_neg, ← neg_div, neg_sub]
  have e2 : (u p - u (q + d)) / (p - (q + d)) = (u (q + d) - u p) / (q + d - p) := by
    rw [show p - (q + d) = -(q + d - p) by ring, div_neg, ← neg_div, neg_sub]
  rw [e1, e2] at s2
  have := lt_trans s2 s1
  exact (div_lt_div_iff_of_pos_right L).1 this

/-- For strictly concave `f` differentiable at `a < b`: `f'(a) > slope(a, b)`. -/
theorem StrictConcaveOn.slope_lt_of_hasDerivAt_left {f : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictConcaveOn ℝ s f) {a b f' : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hd : HasDerivAt f f' a) : (f b - f a) / (b - a) < f' := by
  have hoc := convex_iff_ordConnected.1 hf.1
  set m := (a + b) / 2
  have hm : m ∈ s := hoc.out ha hb ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have h1 := hf.secant_strict_mono ha hm hb (by simp only [m]; linarith)
    (by linarith) (by simp only [m]; linarith)
  have hlim : Tendsto (fun x => (f x - f a) / (x - a)) (𝓝[>] a) (𝓝 f') := by
    have := hasDerivAt_iff_tendsto_slope.1 hd
    rw [slope_fun_def_field] at this
    exact this.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have h2 : (f m - f a) / (m - a) ≤ f' := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show a < m by simp only [m]; linarith)] with x hx
    exact (hf.secant_strict_mono ha (hoc.out ha hm ⟨hx.1.le, hx.2.le⟩) hm (ne_of_gt hx.1)
      (by simp only [m]; linarith) hx.2).le
  linarith

/-- For strictly concave `f` differentiable at `b > a`: `f'(b) < slope(a, b)`. -/
theorem StrictConcaveOn.hasDerivAt_lt_slope_right {f : ℝ → ℝ} {s : Set ℝ}
    (hf : StrictConcaveOn ℝ s f) {a b f' : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hd : HasDerivAt f f' b) : f' < (f b - f a) / (b - a) := by
  have hoc := convex_iff_ordConnected.1 hf.1
  set m := (a + b) / 2
  have hm : m ∈ s := hoc.out ha hb ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  -- secant from `b`: slope to `m` is below slope to `a`
  have h1 := hf.secant_strict_mono hb ha hm (by linarith) (by simp only [m]; linarith)
    (by simp only [m]; linarith)
  have hlim : Tendsto (fun x => (f x - f b) / (x - b)) (𝓝[<] b) (𝓝 f') := by
    have := hasDerivAt_iff_tendsto_slope.1 hd
    rw [slope_fun_def_field] at this
    exact this.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
  have h2 : f' ≤ (f m - f b) / (m - b) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (show m < b by simp only [m]; linarith)] with x hx
    exact (hf.secant_strict_mono hb hm (hoc.out hm hb ⟨hx.1.le, hx.2.le⟩)
      (by simp only [m]; linarith) (ne_of_lt hx.2) hx.1).le
  have e : (f a - f b) / (a - b) = (f b - f a) / (b - a) := by
    rw [← neg_sub (f b), ← neg_sub b, neg_div_neg_eq]
  linarith

/-- **Supergradient inequality**: a strictly concave function lies below its
tangent line, `f(x) ≤ f(a) + f'(a)(x - a)`. -/
theorem StrictConcaveOn.le_add_deriv {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictConcaveOn ℝ s f)
    {a x f' : ℝ} (ha : a ∈ s) (hx : x ∈ s) (hd : HasDerivAt f f' a) :
    f x ≤ f a + f' * (x - a) := by
  rcases lt_trichotomy x a with h | rfl | h
  · have := StrictConcaveOn.hasDerivAt_lt_slope_right hf hx ha h hd
    rw [lt_div_iff₀ (by linarith)] at this
    nlinarith
  · simp
  · have := StrictConcaveOn.slope_lt_of_hasDerivAt_left hf ha hx h hd
    rw [div_lt_iff₀ (by linarith)] at this
    nlinarith

namespace RCKModel

variable (M : RCKModel)

/-- The state space `[0, k̄]`. -/
abbrev S (M : RCKModel) : Set ℝ := Icc 0 M.kbar

theorem f_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ M.f k := by
  have := M.f_strictMono.monotoneOn (show (0 : ℝ) ∈ Ici 0 from le_rfl) hk hk
  rwa [M.f_zero] at this

theorem f_mono {k k' : ℝ} (hk : 0 ≤ k) (hkk' : k ≤ k') : M.f k ≤ M.f k' :=
  M.f_strictMono.monotoneOn hk (le_trans hk hkk') hkk'

/-- Feasible next-period capital: `0 ≤ y ≤ f(k)` (nonnegative consumption). -/
def Γ (k : M.S) : Set M.S := {y | (y : ℝ) ≤ M.f k}

/-- The return: utility of consumption `c = f(k) - y`. -/
def F (k y : M.S) : ℝ := M.u (M.f k - y)

theorem Γ_isClosed_graph : IsClosed (graph M.Γ) :=
  isClosed_le (continuous_subtype_val.comp continuous_snd)
    (M.f_continuous.comp (continuous_subtype_val.comp continuous_fst))

theorem Γ_lhc : LowerHemicontinuous M.Γ := by
  refine fun k => lowerHemicontinuousAt_iff_textbook.2 ?_
  rintro U hU ⟨y, hyΓ, hyU⟩
  -- follow `y` by `min y (f k')`, which is feasible at `k'` and continuous in `k'`
  let h : M.S → M.S := fun k' => ⟨min (y : ℝ) (M.f k'),
    le_min y.2.1 (M.f_nonneg k'.2.1), (min_le_left _ _).trans y.2.2⟩
  have hc : Continuous h :=
    (continuous_const.min (M.f_continuous.comp continuous_subtype_val)).subtype_mk _
  have hk : h k = y := Subtype.ext (min_eq_left hyΓ)
  filter_upwards [(hc.tendsto k).eventually (hU.mem_nhds (hk ▸ hyU))] with k' hk'
  exact ⟨h k', (min_le_right _ _ : min (y : ℝ) (M.f k') ≤ M.f k'), hk'⟩

/-- The RCK model satisfies SL Assumptions 4.3–4.4: it is a `DynProg`. -/
noncomputable def toDynProg : DynProg M.S where
  Γ := M.Γ
  F := M.F
  β := M.β
  β_pos := M.β_pos
  β_lt_one := M.β_lt_one
  Γ_nonempty := fun k => ⟨⟨0, le_rfl, M.kbar_pos.le⟩, M.f_nonneg k.2.1⟩
  Γ_compact := fun k => (isClosed_le continuous_subtype_val continuous_const).isCompact
  Γ_continuous := ⟨upperHemicontinuous_of_isClosed_graph M.Γ_isClosed_graph, M.Γ_lhc⟩
  F_continuous := M.u_continuous.comp
    ((M.f_continuous.comp (continuous_subtype_val.comp continuous_fst)).sub
      (continuous_subtype_val.comp continuous_snd))
  F_bounded := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (M.u_continuous.continuousOn (s := Icc 0 M.kbar))
    refine ⟨C, fun k y hy => ?_⟩
    have h1 : 0 ≤ M.f k - y := sub_nonneg.2 hy
    have h2 : M.f k - y ≤ M.kbar := by linarith [M.f_le k k.2, y.2.1]
    have := hC _ ⟨h1, h2⟩
    simp only [Real.norm_eq_abs] at this
    exact this

/-- **The value function is strictly increasing in capital** (SL Thm 4.7). -/
theorem value_strictMono : StrictMono M.toDynProg.value := by
  refine M.toDynProg.value_strictMono (fun k k' y hkk' hy => ?_) (fun k k' hkk' y hy => ?_)
  · have hf := M.f_strictMono k.2.1 (le_trans k.2.1 hkk'.le) (show (k : ℝ) < k' from hkk')
    have hy' : (y : ℝ) ≤ M.f k := hy
    exact M.u_strictMono (show 0 ≤ M.f k - y by linarith)
      (show 0 ≤ M.f k' - y by linarith) (by linarith)
  · exact le_trans hy (M.f_mono k.2.1 hkk')

theorem convexGraph : ConvexGraph M.toDynProg.Γ := by
  intro k y k' y' z w hy hy' a b ha hb hab hz hw
  simp only [smul_eq_mul] at hz hw
  show (w : ℝ) ≤ M.f z
  have hfc := M.f_strictConcave.concaveOn.2 (show (k : ℝ) ∈ Ici 0 from k.2.1)
    (show (k' : ℝ) ∈ Ici 0 from k'.2.1) ha.le hb.le hab
  simp only [smul_eq_mul] at hfc
  have hy1 : (y : ℝ) ≤ M.f k := hy
  have hy2 : (y' : ℝ) ≤ M.f k' := hy'
  rw [hw, hz]
  nlinarith

theorem strictlyConcaveReturn : StrictlyConcaveReturn M.toDynProg.Γ M.toDynProg.F := by
  intro k y k' y' z w hy hy' a b ha hb hab hz hw
  simp only [smul_eq_mul] at hz hw
  show a * M.u (M.f k - y) + b * M.u (M.f k' - y') ≤ M.u (M.f z - w) ∧
    (k ≠ k' → a * M.u (M.f k - y) + b * M.u (M.f k' - y') < M.u (M.f z - w))
  have hy1 : (y : ℝ) ≤ M.f k := hy
  have hy2 : (y' : ℝ) ≤ M.f k' := hy'
  have hc : (0 : ℝ) ≤ M.f k - y := by linarith
  have hc' : (0 : ℝ) ≤ M.f k' - y' := by linarith
  -- concavity of `u`
  have hu := M.u_strictConcave.concaveOn.2 (show M.f k - y ∈ Ici 0 from hc)
    (show M.f k' - y' ∈ Ici 0 from hc') ha.le hb.le hab
  simp only [smul_eq_mul] at hu
  -- concavity of `f`
  have hfc := M.f_strictConcave.concaveOn.2 (show (k : ℝ) ∈ Ici 0 from k.2.1)
    (show (k' : ℝ) ∈ Ici 0 from k'.2.1) ha.le hb.le hab
  simp only [smul_eq_mul] at hfc
  have hmix : a * (M.f k - y) + b * (M.f k' - y') = a * M.f k + b * M.f k' - w := by
    rw [hw]; ring
  have hnn : 0 ≤ a * (M.f k - y) + b * (M.f k' - y') := by positivity
  rw [← hz] at hfc
  have hzw : 0 ≤ M.f z - w := by linarith
  refine ⟨hu.trans (M.u_strictMono.monotoneOn (show _ ∈ Ici (0 : ℝ) from hnn)
    (show _ ∈ Ici (0 : ℝ) from hzw) (by rw [hmix]; linarith)), fun hne => ?_⟩
  -- with `k ≠ k'`, strict concavity of `f` makes resources strictly larger
  have hne' : (k : ℝ) ≠ k' := fun h => hne (Subtype.ext h)
  have hfs := M.f_strictConcave.2 (show (k : ℝ) ∈ Ici 0 from k.2.1)
    (show (k' : ℝ) ∈ Ici 0 from k'.2.1) hne' ha hb hab
  simp only [smul_eq_mul] at hfs
  rw [← hz] at hfs
  exact hu.trans_lt (M.u_strictMono (show _ ∈ Ici (0 : ℝ) from hnn)
    (show _ ∈ Ici (0 : ℝ) from hzw) (by rw [hmix]; linarith))

/-- **Increasing differences** of `F(k, y) = u(f(k) - y)` and ascending
feasible sets give a **nondecreasing optimal policy** (SL Thm 6.1). Together
with SL Thm 4.8: the policy is a continuous, nondecreasing function. -/
theorem exists_monotone_policy :
    ∃ g : M.S → M.S, (∀ k, M.toDynProg.policy k = {g k}) ∧ Continuous g ∧ Monotone g := by
  obtain ⟨g, hgc, hg⟩ := M.toDynProg.exists_continuous_policy (convex_Icc 0 M.kbar)
    M.convexGraph M.strictlyConcaveReturn
  refine ⟨g, hg, hgc, fun k k' hkk' => ?_⟩
  rcases hkk'.lt_or_eq with hlt | heq
  · refine M.toDynProg.policy_monotone (fun k k' y y' hkk' hy hy' hyy' => ⟨?_, ?_⟩)
      (fun k k' y y' hkk' hyy' hy _ _ hy'' => ?_) hlt (by rw [hg]; rfl) (by rw [hg]; rfl)
    · exact (show (y' : ℝ) ≤ M.f k from le_trans (le_of_lt hyy') hy)
    · exact (show (y : ℝ) ≤ M.f k' from le_trans hy (M.f_mono k.2.1 hkk'.le))
    · -- `u(f k' - y') - u(f k - y') < u(f k' - y) - u(f k - y)`
      show M.u (M.f k' - y') - M.u (M.f k - y') < M.u (M.f k' - y) - M.u (M.f k - y)
      have hyk : (y : ℝ) ≤ M.f k := hy
      have hf := M.f_strictMono k.2.1 (le_trans k.2.1 hkk'.le) (show (k : ℝ) < k' from hkk')
      have h := StrictConcaveOn.increment_lt M.u_strictConcave (p := M.f k - y) (q := M.f k' - y)
        (d := y - y') (by linarith) (by linarith) (by simpa using hyy')
      have e1 : M.f k' - y + (y - y') = M.f k' - y' := by ring
      have e2 : M.f k - y + (y - y') = M.f k - y' := by ring
      rw [e1, e2] at h
      exact h
  · rw [heq]

/-- **Monotone convergence of optimal capital** (SL Thm 6.2). From any initial
capital `k₀`, the optimal plan is `k_{t+1} = g(k_t)` (it attains the value
and is the only plan that does); this capital path is monotone and converges
to a steady state `k_∞ = g(k_∞)`. -/
theorem optimal_capital_converges (k₀ : M.S) :
    ∃ g : M.S → M.S, (∀ k, M.toDynProg.policy k = {g k}) ∧ Continuous g ∧ Monotone g ∧
      M.toDynProg.payoff (planOf g k₀) = M.toDynProg.value k₀ ∧
      (∀ x, IsFeasiblePlan M.toDynProg.Γ k₀ x →
        (M.toDynProg.payoff x = M.toDynProg.value k₀ ↔ x = planOf g k₀)) ∧
      (Monotone (planOf g k₀) ∨ Antitone (planOf g k₀)) ∧
      ∃ kinf : M.S, g kinf = kinf ∧ Tendsto (planOf g k₀) atTop (𝓝 kinf) := by
  obtain ⟨g, hg, hgc, hgm⟩ := M.exists_monotone_policy
  have hpol : ∀ x, IsFeasiblePlan M.toDynProg.Γ k₀ x →
      ((∀ t, x (t + 1) ∈ M.toDynProg.policy (x t)) ↔ x = planOf g k₀) := by
    intro x hx
    constructor
    · intro h
      funext t
      induction t with
      | zero => exact hx.1
      | succ t ih => rw [planOf_succ, ← ih]; simpa [hg] using h t
    · rintro rfl t
      rw [planOf_succ, hg]; rfl
  have hfeas : IsFeasiblePlan M.toDynProg.Γ k₀ (planOf g k₀) :=
    isFeasiblePlan_planOf (fun k => M.toDynProg.policy_subset k (by rw [hg]; rfl)) k₀
  have hopt := M.toDynProg.principle_of_optimality k₀
  refine ⟨g, hg, hgc, hgm, (hopt.2 _ hfeas).2 ((hpol _ hfeas).2 rfl),
    fun x hx => (hopt.2 x hx).trans (hpol x hx), orbit_monotone_or_antitone hgm k₀, ?_⟩
  exact orbit_tendsto_fixedPoint hgm hgc k₀

/-- **Modified golden rule** (Acemoglu Prop. 6.3 / SL §6.1). Let `g` be the
optimal policy and `k*` an *interior* steady state, `g(k*) = k*` with
`k* > 0`, and positive consumption `c* = f(k*) - k* > 0` (so `k* < k̄`). If `u` is
differentiable at `c*` and `f` is differentiable at `k*`, then
`β f'(k*) = 1`: the marginal product of capital (net of depreciation, as `f`
includes undepreciated capital) equals the rate of time preference. -/
theorem modified_golden_rule {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k})
    {k : M.S} (hfix : g k = k) (hk0 : 0 < (k : ℝ))
    (hc : (k : ℝ) < M.f k) {u' f' : ℝ} (hu : HasDerivAt M.u u' (M.f k - k))
    (hf : HasDerivAt M.f f' k) : M.β * f' = 1 := by
  set P := M.toDynProg
  have hint : 0 < (k : ℝ) ∧ (k : ℝ) < M.kbar := ⟨hk0, lt_of_lt_of_le hc (M.f_le k k.2)⟩
  -- `u'(c*) > 0`: strictly increasing and concave
  have hu0 : u' ≠ 0 := by
    have hc0 : 0 < M.f k - k := by linarith
    have h := StrictConcaveOn.slope_lt_of_hasDerivAt_left M.u_strictConcave
      (show M.f k - k ∈ Ici (0 : ℝ) from hc0.le)
      (show M.f k - k + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith) (by linarith) hu
    have h2 := M.u_strictMono (show M.f k - k ∈ Ici (0 : ℝ) from hc0.le)
      (show M.f k - k + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith) (by linarith)
    rw [show M.f k - k + 1 - (M.f k - k) = 1 by ring, div_one] at h
    exact ne_of_gt (by linarith)
  have hkint : (k : ℝ) ∈ interior M.S := by rw [interior_Icc]; exact hint
  have hSn : M.S ∈ 𝓝 (k : ℝ) := mem_interior_iff_mem_nhds.1 hkint
  have hy₀ : k ∈ P.policy k := by rw [hg, hfix]; rfl
  -- near `k`, the steady-state choice `k` stays feasible since `k < f(k)`
  have hnear : ∀ᶠ r in 𝓝 (k : ℝ), (k : ℝ) < M.f r :=
    (M.f_continuous.tendsto _).eventually (lt_mem_nhds hc)
  have hloc : ∀ᶠ r in 𝓝 (k : ℝ), ∀ h : r ∈ M.S, k ∈ P.Γ ⟨r, h⟩ := by
    filter_upwards [hnear] with r hr h using hr.le
  -- derivative of `F(·, k)` at `k`: chain rule `u'(c*) f'(k*)`
  have hFx : HasDerivAt (extendS fun x => P.F x k) (u' * f') k := by
    have hd : HasDerivAt (M.u ∘ fun r => M.f r - (k : ℝ)) (u' * f') k :=
      HasDerivAt.comp (h := fun r => M.f r - (k : ℝ)) (k : ℝ) hu (hf.sub_const (k : ℝ))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hSn] with r hr
    simp only [extendS, hr, dite_true]
    rfl
  -- Benveniste–Scheinkman: `V'(k*) = u'(c*) f'(k*)`
  have hV := P.hasDerivAt_value (convex_Icc 0 M.kbar) M.convexGraph M.strictlyConcaveReturn
    hkint hy₀ hloc hFx
  -- First-order condition: `y ↦ u(f(k*) - y) + β V(y)` has a local max at `y = k*`.
  set φ : ℝ → ℝ := fun r => M.u (M.f k - r) + P.β * extendS (P.value : M.S → ℝ) r
  have hmax : IsLocalMax φ k := by
    have hle : ∀ᶠ r in 𝓝 (k : ℝ), r ≤ M.f k := (eventually_le_nhds hc)
    filter_upwards [hSn, hle] with r hrS hrf
    have h1 := P.bellman_le (x := k) (y := ⟨r, hrS⟩) hrf
    have h2 := (P.mem_policy_iff.1 hy₀).2
    simp only [φ, extendS, hrS, k.2, dite_true]
    exact h1.trans h2.ge
  have hφ : HasDerivAt φ (u' * (-1) + P.β * (u' * f')) k := by
    have h1 : HasDerivAt (M.u ∘ fun r => M.f k - r) (u' * (-1)) k :=
      hu.comp (k : ℝ) ((hasDerivAt_id' (k : ℝ)).const_sub (M.f k))
    exact h1.add (hV.const_mul P.β)
  have h0 := hmax.hasDerivAt_eq_zero hφ
  have : u' * (M.β * f' - 1) = 0 := by
    have hβ : P.β = M.β := rfl
    rw [hβ] at h0; linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hu0
  · linarith

/-- **The modified-golden-rule capital stock is a steady state** (converse of
`modified_golden_rule`). If `β f'(k*) = 1` and `c* = f(k*) - k* > 0` (with `u`
differentiable at `c*` and `f` at `k*`), then the optimal policy keeps capital
at `k*`: `g(k*) = k*`. Proof: the stationary plan `k_t = k*` satisfies the
Euler equation and the transversality condition, hence (SL Thm 4.15) does at
least as well as the optimal plan, so it is optimal and follows the policy. -/
theorem steady_state_of_modified_golden_rule {g : M.S → M.S}
    (hg : ∀ k, M.toDynProg.policy k = {g k}) {k : M.S} (hc : (k : ℝ) < M.f k)
    {u' f' : ℝ} (hu : HasDerivAt M.u u' (M.f k - k)) (hf : HasDerivAt M.f f' k)
    (hmgr : M.β * f' = 1) : g k = k := by
  set P := M.toDynProg
  set c := M.f k - k with hcdef
  have hc0 : 0 < c := by simp only [c]; linarith
  have hβ := M.β_pos
  -- `u'(c*) > 0` (strictly increasing, concave) and `f'(k*) = 1/β > 0`
  have hu'pos : 0 < u' := by
    have h := StrictConcaveOn.slope_lt_of_hasDerivAt_left M.u_strictConcave
      (show c ∈ Ici (0 : ℝ) from hc0.le) (show c + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
      (by linarith) hu
    have h2 := M.u_strictMono (show c ∈ Ici (0 : ℝ) from hc0.le)
      (show c + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith) (by linarith)
    rw [show c + 1 - c = 1 by ring, div_one] at h
    linarith
  have hf'pos : 0 < f' := by
    by_contra h; push Not at h; nlinarith
  -- The sequence problem on `ℝ`: states in `[0, k̄]`, `0 ≤ y ≤ f(x)`.
  let Γ' : ℝ → Set ℝ := fun x => {y | x ∈ M.S ∧ 0 ≤ y ∧ y ≤ M.f x}
  let F' : ℝ → ℝ → ℝ := fun x y => M.u (M.f x - y)
  let xs : ℕ → ℝ := fun _ => (k : ℝ)
  have hxs : IsFeasiblePlan Γ' k xs := ⟨rfl, fun _ => ⟨k.2, k.2.1, hc.le⟩⟩
  have hopt : IsOptimalPlan Γ' F' M.β k xs := by
    refine euler_transversality_along M.β_pos.le (fun _ _ => (u' * f') • LinearMap.id)
      (fun _ _ => (-u') • LinearMap.id) (fun t x' y' hy' => ?_) (fun x y h => h.2.1)
      (fun t z hz => ?_) hxs (fun t => ?_) ?_
    · -- supergradient of `u(f(x) - y)` at `(k*, k*)`
      obtain ⟨hx', hy0, hyf⟩ := hy'
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, F', xs]
      have h1 := StrictConcaveOn.le_add_deriv M.u_strictConcave
        (show c ∈ Ici (0 : ℝ) from hc0.le) (show M.f x' - y' ∈ Ici (0 : ℝ) from sub_nonneg.2 hyf) hu
      have h2 := StrictConcaveOn.le_add_deriv M.f_strictConcave
        (show (k : ℝ) ∈ Ici (0 : ℝ) from k.2.1) (show x' ∈ Ici (0 : ℝ) from hx'.1) hf
      have h3 : u' * (M.f x' - y' - c) ≤ u' * (f' * (x' - k) - (y' - k)) :=
        mul_le_mul_of_nonneg_left (by simp only [c]; linarith) hu'pos.le
      simp only [c] at h1 h3
      linarith
    · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
      positivity
    · -- Euler: `-u'(c*) + β u'(c*) f'(k*) = 0`
      ext
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
        LinearMap.zero_apply]
      have : M.β * (u' * f' * 1) = u' * (M.β * f') := by ring
      rw [this, hmgr]; ring
    · -- transversality: `β^t u' f' k* → 0`
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, xs]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_pos.le M.β_lt_one).mul_const
        (u' * f' * (k : ℝ))
  -- Compare with the optimal (policy) plan in the DP.
  have hsel : ∀ x, g x ∈ P.policy x := fun x => by rw [hg]; rfl
  set xg := planOf g k
  have hxg : IsFeasiblePlan P.Γ k xg :=
    isFeasiblePlan_planOf (fun x => P.policy_subset x (hsel x)) k
  have hxgV : P.payoff xg = P.value k :=
    P.payoff_eq_value_of_policy hxg fun t => by
      simp only [xg]; rw [planOf_succ]; exact hsel _
  set xS : ℕ → M.S := fun _ => k
  have hxS : IsFeasiblePlan P.Γ k xS := ⟨rfl, fun _ => hc.le⟩
  have hxg' : IsFeasiblePlan Γ' k (fun t => (xg t : ℝ)) :=
    ⟨by simp [xg, planOf], fun t => ⟨(xg t).2, (xg (t + 1)).2.1, hxg.2 t⟩⟩
  have hcatch := hopt.2 _ hxg'
  have eq1 : ∀ n, partialPayoff F' M.β (fun t => (xg t : ℝ)) n = partialPayoff P.F P.β xg n :=
    fun n => rfl
  have eq2 : ∀ n, partialPayoff F' M.β xs n = partialPayoff P.F P.β xS n := fun n => rfl
  have hle : P.value k ≤ P.payoff xS := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [← hxgV]
    refine le_of_tendsto_of_tendsto (P.tendsto_partialPayoff hxg)
      ((P.tendsto_partialPayoff hxS).add_const ε) ?_
    filter_upwards [hcatch ε hε] with n hn
    rw [eq1, eq2] at hn
    exact hn
  have heq : P.payoff xS = P.value k := le_antisymm (P.payoff_le_value hxS) hle
  have hpol := ((P.principle_of_optimality k).2 xS hxS).1 heq 0
  rw [hg] at hpol
  exact (Set.mem_singleton_iff.1 hpol).symm

/-- **Uniqueness of the modified-golden-rule capital stock**: since `f` is
strictly concave, `f'` is strictly decreasing, so at most one `k > 0` solves
`β f'(k) = 1`. -/
theorem modified_golden_rule_unique {k₁ k₂ f₁ f₂ : ℝ} (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂)
    (hd₁ : HasDerivAt M.f f₁ k₁) (hd₂ : HasDerivAt M.f f₂ k₂)
    (he₁ : M.β * f₁ = 1) (he₂ : M.β * f₂ = 1) : k₁ = k₂ := by
  have hβ := M.β_pos
  have hf : f₁ = f₂ := by
    have := he₁.trans he₂.symm
    exact mul_left_cancel₀ hβ.ne' this
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have a := StrictConcaveOn.slope_lt_of_hasDerivAt_left M.f_strictConcave h₁ h₂ hlt hd₁
    have b := StrictConcaveOn.hasDerivAt_lt_slope_right M.f_strictConcave h₁ h₂ hlt hd₂
    linarith
  · have a := StrictConcaveOn.slope_lt_of_hasDerivAt_left M.f_strictConcave h₂ h₁ hlt hd₂
    have b := StrictConcaveOn.hasDerivAt_lt_slope_right M.f_strictConcave h₂ h₁ hlt hd₁
    linarith

end RCKModel

/-! ### Non-vacuity: a concrete RCK economy

`u(c) = √c`, `f(k) = √k`, `β = 1/2`, `k̄ = 1` satisfies every assumption, so
the monotone-convergence theorem applies to it. -/

/-- A concrete RCK economy (with `√` extended by `0` to the left by Mathlib). -/
noncomputable def RCKModel.sqrtExample : RCKModel where
  u := Real.sqrt
  f := Real.sqrt
  β := 1 / 2
  kbar := 1
  β_pos := by norm_num
  β_lt_one := by norm_num
  kbar_pos := by norm_num
  u_continuous := Real.continuous_sqrt
  u_strictMono := fun _ hx _ _ hxy => Real.sqrt_lt_sqrt hx hxy
  u_strictConcave := Real.strictConcaveOn_sqrt
  f_continuous := Real.continuous_sqrt
  f_zero := Real.sqrt_zero
  f_strictMono := fun _ hx _ _ hxy => Real.sqrt_lt_sqrt hx hxy
  f_strictConcave := Real.strictConcaveOn_sqrt
  f_le := fun k hk => by
    rw [Real.sqrt_le_left (by norm_num)]
    simpa using hk.2

example (k₀ : RCKModel.sqrtExample.S) :
    ∃ g : RCKModel.sqrtExample.S → RCKModel.sqrtExample.S,
      (∀ k, RCKModel.sqrtExample.toDynProg.policy k = {g k}) ∧ Monotone g ∧
      ∃ kinf, g kinf = kinf ∧ Tendsto (planOf g k₀) atTop (𝓝 kinf) := by
  obtain ⟨g, hg, -, hgm, -, -, -, h⟩ := RCKModel.sqrtExample.optimal_capital_converges k₀
  exact ⟨g, hg, hgm, h⟩

/-- In the `√` economy the modified-golden-rule capital is `k* = 1/16`
(`β f'(k*) = ½ · 1/(2·¼) = 1`, consumption `c* = ¼ - 1/16 > 0`); it is a steady
state of the optimal policy, and it satisfies every hypothesis of
`modified_golden_rule`, which is therefore not vacuous. -/
example : ∃ g : RCKModel.sqrtExample.S → RCKModel.sqrtExample.S,
    (∀ k, RCKModel.sqrtExample.toDynProg.policy k = {g k}) ∧
    ∃ kstar : RCKModel.sqrtExample.S, (kstar : ℝ) = 1 / 16 ∧ g kstar = kstar ∧
      0 < (kstar : ℝ) ∧ (kstar : ℝ) < RCKModel.sqrtExample.kbar ∧
      (kstar : ℝ) < RCKModel.sqrtExample.f kstar := by
  set M := RCKModel.sqrtExample
  obtain ⟨g, hg, -, -⟩ := M.exists_monotone_policy
  set kstar : M.S := ⟨1 / 16, by norm_num, by norm_num [M, RCKModel.sqrtExample]⟩
  have hs : Real.sqrt (1 / 16) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hf : M.f kstar = 1 / 4 := hs
  have hc : (kstar : ℝ) < M.f kstar := by rw [hf]; norm_num
  have hu : HasDerivAt M.u (1 / (2 * Real.sqrt (M.f kstar - kstar))) (M.f kstar - kstar) :=
    Real.hasDerivAt_sqrt (by rw [hf]; norm_num)
  have hfd : HasDerivAt M.f (1 / (2 * Real.sqrt (1 / 16))) kstar :=
    Real.hasDerivAt_sqrt (by norm_num)
  have hmgr : M.β * (1 / (2 * Real.sqrt (1 / 16))) = 1 := by
    rw [hs]; norm_num [M, RCKModel.sqrtExample]
  refine ⟨g, hg, kstar, rfl, M.steady_state_of_modified_golden_rule hg hc hu hfd hmgr,
    by norm_num [kstar], by norm_num [kstar, M, RCKModel.sqrtExample], hc⟩

end Econ
