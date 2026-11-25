/-
# Aumann's core equivalence theorem: core ⊆ Walrasian

**The economics.** In an exchange economy with a nonatomic continuum of traders
(`GE/ContinuumEconomy.lean`) every core allocation is a Walrasian allocation
(Aumann 1964, "Markets with a continuum of traders"). Together with the easy
inclusion `IsWalrasianEquilibrium.inCore` this is **core equivalence**: when
every trader is negligible, the only allocations no coalition can improve upon
are the competitive ones. It is the continuum limit of the Debreu–Scarf replica
theorem and needs **no convexity of preferences**: nonatomicity convexifies
aggregates (Lyapunov).

**Proof** (Aumann 1964; Hildenbrand 1974, Ch. 2). Fix a core allocation `x`.
1. Trader `a`'s *improving net trades* are `G a = {z : e a + z ≥ 0, e a + z ≻ x a} ∪ {0}`.
   The set `∫ G` of integrals of integrable selections is convex by Lyapunov's
   theorem (`convex_selectionIntegral`), whatever the shape of `G a`.
2. `∫ G` misses the open negative orthant (`InCore.not_integral_neg`): if
   `∫ g ≪ 0`, the traders with `g a ≠ 0` form a coalition with a surplus, which
   they spread evenly; by strong monotonicity and transitivity it blocks `x`.
3. Hahn–Banach separates them (`InCore.exists_price`): a price `p ≥ 0`, `p ≠ 0`
   with `p · ∫ g ≥ 0` for every selection `g`.
4. **Price support a.e.** (`ae_price_support`): for almost every `a`, every
   bundle preferred to `x a` costs at least `p · e a`. Rational bundles are
   handled one at a time (countably many null sets); continuity extends this to
   all bundles.
5. Monotonicity and feasibility give `p · x a = p · e a` a.e.; a **cheaper
   point** argument (`not_P_of_cost_le`) gives `p ≫ 0` (using `∫ e ≫ 0`) and
   then demand maximisation for every trader (traders with `p · e a = 0` own
   nothing and can afford only `0`).

**Results.**
* `InCore.isWalrasianEquilibrium`: core ⊆ Walrasian under an
  allocation-specific weakening of continuity and measurability (both depending
  on `x`): the strict upper set of `x a` is relatively open in `ℝ₊^ι`, and
  `{a | y a ≻_a x a}` is null-measurable for every a.e.-measurable `y`.
* `InCore.isWalrasianEquilibrium_of_continuousPref`, `inCore_iff_of_continuousPref`:
  the canonical statement, with continuous preferences (`ContinuousPref`) and a
  jointly measurable strict preference `{(a, u, v) | u ≻_a v}`;
  `eventually_P_of_continuousPref` and `nullMeasurableSet_P` reduce it to the
  general one.
* `linContinuum_inCore_iff`: in the uniform perfect-substitutes continuum, an
  allocation is in the core iff it is Walrasian.
* `bumpContinuum_inCore_iff`, `bumpContinuum_not_convexPref`: the same for an
  economy with **non-convex**, trader-dependent preferences
  `max(z₀, z₁) + (1 + a²)(z₀ + z₁)`; all canonical hypotheses hold.

**Hypotheses vs. the literature.** `μ` finite and nonatomic, at least one good,
`∫ e ≫ 0`; preferences rational, strongly monotone and continuous for almost
every trader. No convexity anywhere. Some are stronger than needed: the price
step uses only transitivity (completeness enters only because `demand` is
phrased via `≿`); `ContinuousPref` also asks for closed upper sets, which are
unused; and strong monotonicity is used to upgrade quasi-equilibrium to
equilibrium with `p ≫ 0`. Hildenbrand's core ⊆ quasi-equilibrium under weak
monotonicity is not formalised. `hR` asks for measurability for every trader,
not just almost every one.
-/
module

public import EconLean.GE.ContinuumEconomy
public import EconLean.Foundations.Measure.LyapunovIntegral
public import Mathlib.Analysis.LocallyConvex.Separation

@[expose] public section

noncomputable section

namespace Econ
namespace Continuum
namespace ContinuumEconomy

open MeasureTheory Set Filter Topology Lyapunov

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

/-- The **improving net trades** of trader `a` against allocation `x`: net
trades `z` with `e a + z ≥ 0` strictly preferred to `x a`, together with the
zero trade. -/
def improve (x : Ω → ι → ℝ) (a : Ω) : Set (ι → ℝ) :=
  {z | z = 0 ∨ (0 ≤ z + E.endow a ∧ P (E.pref a) (z + E.endow a) (x a))}

variable {E}

/-- **No integrable selection of the improving trades has a strictly negative
aggregate** at a core allocation: otherwise the traders making a nonzero trade
could spread the surplus evenly and block. -/
theorem InCore.not_integral_neg [Nonempty ι] {x : Ω → ι → ℝ} (hx : E.InCore x)
    [IsFiniteMeasure E.μ]
    (htrans : ∀ᵐ a ∂E.μ, ∀ {u v w}, E.pref a u v → E.pref a v w → E.pref a u w)
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hmeas : ∀ y : Ω → ι → ℝ, AEStronglyMeasurable y E.μ →
      NullMeasurableSet {a | P (E.pref a) (y a) (x a)} E.μ)
    {g : Ω → ι → ℝ} (hg : Integrable g E.μ) (hgG : ∀ᵐ a ∂E.μ, g a ∈ E.improve x a) :
    ¬ ∀ i, (∫ a, g a ∂E.μ) i < 0 := by
  intro hneg
  set v := ∫ a, g a ∂E.μ with hv
  have hye : AEStronglyMeasurable (fun a => g a + E.endow a) E.μ :=
    hg.aestronglyMeasurable.add E.endow_integrable.aestronglyMeasurable
  set S0 := {a | 0 ≤ g a + E.endow a ∧ P (E.pref a) (g a + E.endow a) (x a)} with hS0def
  have hS0 : NullMeasurableSet S0 E.μ :=
    (AEStronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const hye).inter (hmeas _ hye)
  set S := toMeasurable E.μ S0
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hSS0 : S =ᵐ[E.μ] S0 := hS0.toMeasurable_ae_eq
  have hmemS : ∀ᵐ a ∂E.μ, a ∈ S ↔ a ∈ S0 := hSS0.mem_iff
  -- the integral is carried by `S`
  have hvS : ∫ a in S, g a ∂E.μ = v := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hgG, hmemS] with a ha hmem hnot
    rcases ha with h0 | h1
    · exact h0
    · exact absurd (hmem.2 h1) hnot
  -- `S` has positive measure
  have hSpos : 0 < E.μ S := by
    rw [pos_iff_ne_zero]
    intro h0
    have hv0 : v = 0 := by
      rw [← hvS, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h := hneg i
    rw [hv0] at h
    exact lt_irrefl _ h
  have hm : 0 < E.μ.real S := measureReal_pos_iff.2 hSpos
  set w : ι → ℝ := (-(E.μ.real S)⁻¹) • v with hw
  have hwpos : ∀ i, 0 < w i := fun i => by
    simp only [hw, Pi.smul_apply, smul_eq_mul]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (inv_pos.2 hm)) (hneg i)
  refine hx.2 S ⟨hSm, hSpos, fun a => g a + E.endow a + w, ?_, ?_, ?_⟩
  · exact ((hg.add E.endow_integrable).add (integrable_const w)).integrableOn
  · filter_upwards [hmemS, htrans, hmono] with a hmem htr hmo haS
    obtain ⟨h0, hP⟩ := hmem.1 haS
    have hle : g a + E.endow a ≤ g a + E.endow a + w := fun i => by
      simp only [Pi.add_apply]; linarith [hwpos i]
    have hne : g a + E.endow a ≠ g a + E.endow a + w := by
      obtain ⟨i⟩ := ‹Nonempty ι›
      intro h
      have := congrFun h i
      simp only [Pi.add_apply] at this
      linarith [hwpos i]
    exact ⟨h0.trans hle, P_trans (R := E.pref a) (fun h1 h2 => htr h1 h2) (hmo (g a + E.endow a) (g a + E.endow a + w) h0 hle hne) hP⟩
  · rw [integral_add (f := fun a => g a + E.endow a) (hg.add E.endow_integrable).integrableOn
      (integrable_const w).integrableOn,
      integral_add hg.integrableOn E.endow_integrable.integrableOn, hvS, setIntegral_const, hw,
      smul_smul, mul_neg, mul_inv_cancel₀ hm.ne', neg_one_smul]
    abel

/-- **Supporting prices**: at a core allocation of a nonatomic economy there is a
nonzero price vector `p ≥ 0` under which every integrable selection of improving
net trades has nonnegative aggregate value. Proof: the aggregates form a convex
set (Lyapunov, `convex_selectionIntegral`) disjoint from the open negative
orthant (`InCore.not_integral_neg`); separate them by Hahn–Banach. -/
theorem InCore.exists_price [Nonempty ι] {x : Ω → ι → ℝ} (hx : E.InCore x)
    [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    (htrans : ∀ᵐ a ∂E.μ, ∀ {u v w}, E.pref a u v → E.pref a v w → E.pref a u w)
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hmeas : ∀ y : Ω → ι → ℝ, AEStronglyMeasurable y E.μ →
      NullMeasurableSet {a | P (E.pref a) (y a) (x a)} E.μ) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ 0 < ∑ i, p i ∧
      ∀ g : Ω → ι → ℝ, Integrable g E.μ → (∀ᵐ a ∂E.μ, g a ∈ E.improve x a) →
        0 ≤ cost p (∫ a, g a ∂E.μ) := by
  classical
  set s : Set (ι → ℝ) := {v | ∀ i, v i < 0} with hsdef
  have hsconv : Convex ℝ s := by
    intro v hv w hw a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [hv i, hw i, mul_neg_of_pos_of_neg ha' (hv i), mul_nonpos_of_nonneg_of_nonpos hb (hw i).le]
    · subst ha'
      simp only [zero_add] at hab
      subst hab
      simpa using hw i
  have hsopen : IsOpen s := by
    have : s = ⋂ i, {v : ι → ℝ | v i < 0} := by ext v; simp [hsdef]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hdisj : Disjoint s (selectionIntegral E.μ (E.improve x)) := by
    refine Set.disjoint_left.2 fun v hv ⟨g, hg, hgG, hgv⟩ => ?_
    subst hgv
    exact hx.not_integral_neg htrans hmono hmeas hg hgG hv
  obtain ⟨f, u, hfs, hft⟩ :=
    geometric_hahn_banach_open hsconv hsopen (convex_selectionIntegral hμ _) hdisj
  set p : ι → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hp
  have hf : ∀ v, f v = cost p v := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, cost]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h0t : (0 : ι → ℝ) ∈ selectionIntegral E.μ (E.improve x) :=
    ⟨0, integrable_zero _ _ _, ae_of_all _ fun _ => Or.inl rfl, by simp⟩
  have hu0 : u ≤ 0 := by simpa using hft 0 h0t
  -- `f ≤ 0` on the open orthant (it is a cone)
  have hfs' : ∀ v ∈ s, f v ≤ 0 := by
    intro v hv
    by_contra hpos
    push Not at hpos
    have hsm : ((|u| + 1) / f v) • v ∈ s := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_neg_of_pos_of_neg (div_pos (by positivity) hpos) (hv i)
    have := hfs _ hsm
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith [le_abs_self u]
  have hcost_const : ∀ r : ℝ, cost p (fun _ => r) = r * ∑ i, p i := by
    intro r; simp only [cost, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc : 0 < ∑ i, p i := by
    have := hfs (fun _ => -1) (fun _ => by norm_num)
    rw [hf, hcost_const] at this
    linarith
  have hu : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    have hmem : (fun _ => u / ∑ i, p i) ∈ s := fun _ => div_neg_of_neg_of_pos hneg hc
    have := hfs _ hmem
    rw [hf, hcost_const, div_mul_cancel₀ _ hc.ne'] at this
    exact lt_irrefl _ this
  refine ⟨p, fun i => ?_, hc, fun g hg hgG => ?_⟩
  · by_contra hneg
    push Not at hneg
    set ε := -p i / (2 * ∑ j, p j) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
    set v : ι → ℝ := fun j => -(if i = j then 1 else 0) - ε
    have hvs : v ∈ s := fun j => by
      simp only [v]
      split_ifs <;> linarith
    have := hfs' v hvs
    have hcv : cost p v = -p i - ε * ∑ j, p j := by
      simp only [cost, v, mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.sum_mul, mul_comm]
    have hεc : ε * ∑ j, p j = -p i / 2 := by
      rw [hε, div_mul_eq_mul_div, mul_comm 2, ← div_div, mul_div_assoc, div_self hc.ne', mul_one]
    rw [hf, hcv, hεc] at this
    linarith
  · rw [← hf]
    exact hu.trans (hft _ ⟨g, hg, hgG, rfl⟩)

omit [Fintype ι] in
/-- An integral over a set of positive measure of a function negative almost
everywhere on it is negative. -/
theorem setIntegral_neg_of_ae_neg {μ : Measure Ω} {T : Set Ω} (hT : MeasurableSet T)
    (hpos : 0 < μ T) {h : Ω → ℝ} (hi : IntegrableOn h T μ) (hneg : ∀ᵐ a ∂μ, a ∈ T → h a < 0) :
    ∫ a in T, h a ∂μ < 0 := by
  have hnn : 0 ≤ᵐ[μ.restrict T] fun a => -h a := by
    rw [EventuallyLE, ae_restrict_iff' hT]
    filter_upwards [hneg] with a ha haT
    simpa using (ha haT).le
  have : 0 < ∫ a in T, -h a ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hi.neg]
    refine hpos.trans_le (measure_mono_ae ?_)
    filter_upwards [hneg] with a ha haT
    exact ⟨neg_ne_zero.2 (ha haT).ne, haT⟩
  rw [integral_neg] at this
  linarith

/-- **Almost-everywhere price support**: if every integrable selection of the
improving net trades has nonnegative value at `p`, then for almost every trader
every bundle strictly preferred to `x a` costs at least her endowment. The
countably many rational bundles are handled one at a time (a positive-measure
set of traders preferring a cheaper rational bundle would give a selection of
negative value); continuity of preferences then extends to all bundles. -/
theorem ae_price_support [IsFiniteMeasure E.μ] {x : Ω → ι → ℝ} {p : ι → ℝ}
    (hmeas : ∀ y : Ω → ι → ℝ, AEStronglyMeasurable y E.μ →
      NullMeasurableSet {a | P (E.pref a) (y a) (x a)} E.μ)
    (hcont : ∀ᵐ a ∂E.μ, ∀ z, 0 ≤ z → P (E.pref a) z (x a) →
      ∀ᶠ w in 𝓝 z, 0 ≤ w → P (E.pref a) w (x a))
    (hp : ∀ g : Ω → ι → ℝ, Integrable g E.μ → (∀ᵐ a ∂E.μ, g a ∈ E.improve x a) →
      0 ≤ cost p (∫ a, g a ∂E.μ)) :
    ∀ᵐ a ∂E.μ, ∀ z, 0 ≤ z → P (E.pref a) z (x a) → cost p (E.endow a) ≤ cost p z := by
  classical
  have hce : Integrable (fun a => cost p (E.endow a)) E.μ :=
    ((costCLM p).integrable_comp E.endow_integrable).congr
      (ae_of_all _ fun a => costCLM_apply p _)
  -- a fixed bundle `c` is a cheaper improvement only for a null set of traders
  have hnull : ∀ c : ι → ℝ, 0 ≤ c →
      ∀ᵐ a ∂E.μ, ¬ (P (E.pref a) c (x a) ∧ cost p c < cost p (E.endow a)) := by
    intro c hc0
    set T0 := {a | P (E.pref a) c (x a) ∧ cost p c < cost p (E.endow a)}
    have hT0 : NullMeasurableSet T0 E.μ :=
      (hmeas (fun _ => c) aestronglyMeasurable_const).inter
        (AEStronglyMeasurable.nullMeasurableSet_lt aestronglyMeasurable_const hce.1)
    set T := toMeasurable E.μ T0
    have hT : MeasurableSet T := measurableSet_toMeasurable _ _
    have hmemT : ∀ᵐ a ∂E.μ, a ∈ T ↔ a ∈ T0 := hT0.toMeasurable_ae_eq.mem_iff
    have hgi : Integrable (T.indicator fun a => c - E.endow a) E.μ :=
      ((integrable_const c).sub E.endow_integrable).indicator hT
    have hsel : ∀ᵐ a ∂E.μ, T.indicator (fun a => c - E.endow a) a ∈ E.improve x a := by
      filter_upwards [hmemT] with a hmem
      by_cases haT : a ∈ T
      · rw [indicator_of_mem haT]
        refine Or.inr ⟨by simpa using hc0, by simpa using (hmem.1 haT).1⟩
      · rw [indicator_of_notMem haT]
        exact Or.inl rfl
    have h0 := hp _ hgi hsel
    rw [integral_indicator hT,
      E.cost_setIntegral p (y := fun a => c - E.endow a)
        ((integrable_const c).sub E.endow_integrable).integrableOn] at h0
    simp only [cost_sub_right] at h0
    have hμT : E.μ T = 0 := by
      by_contra hne
      have := setIntegral_neg_of_ae_neg (h := fun a => cost p c - cost p (E.endow a)) hT
        (pos_iff_ne_zero.2 hne) ((integrable_const _).sub hce).integrableOn
        (by filter_upwards [hmemT] with a hmem haT; exact sub_neg.2 (hmem.1 haT).2)
      linarith
    exact measure_eq_zero_iff_ae_notMem.1 (measure_mono_null (subset_toMeasurable _ _) hμT)
  have hall : ∀ᵐ a ∂E.μ, ∀ q : ι → ℚ,
      ¬ (P (E.pref a) (fun i => (q i : ℝ)) (x a) ∧
        cost p (fun i => (q i : ℝ)) < cost p (E.endow a)) ∨ ¬ (0 ≤ fun i => (q i : ℝ)) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 ≤ fun i => (q i : ℝ)
    · filter_upwards [hnull _ hq] with a ha using Or.inl ha
    · exact ae_of_all _ fun _ => Or.inr hq
  filter_upwards [hall, hcont] with a hq hc z hz hzP
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ w in 𝓝 z, (0 ≤ w → P (E.pref a) w (x a)) ∧ cost p w < cost p (E.endow a) := by
    refine (hc z hz hzP).and ?_
    have hcc : Continuous fun w => cost p w := by
      have : (fun w => cost p w) = costCLM p := funext fun w => (costCLM_apply p w).symm
      rw [this]; exact (costCLM p).continuous
    exact hcc.continuousAt.eventually_lt continuousAt_const hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  choose q hq1 hq2 using fun i => exists_rat_btwn (show z i < z i + ε by linarith)
  have hdist : dist (fun i => (q i : ℝ)) z < ε :=
    (dist_pi_lt_iff hε).2 fun i => by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hq1 i, hq2 i]
  have hq0 : 0 ≤ fun i => (q i : ℝ) := fun i => (hz i).trans (hq1 i).le
  obtain ⟨h1, h2⟩ := hball hdist
  rcases hq q with h | h
  · exact h ⟨h1 hq0, h2⟩
  · exact h hq0

omit [Fintype ι] in
theorem cost_const_eq (p : ι → ℝ) [Fintype ι] (r : ℝ) : cost p (fun _ => r) = r * ∑ i, p i := by
  simp only [cost, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fintype ι] in
/-- With strictly positive prices the only nonnegative bundle of nonpositive cost
is `0`. -/
theorem eq_zero_of_cost_nonpos [Fintype ι] {p z : ι → ℝ} (hp : ∀ i, 0 < p i) (hz : 0 ≤ z)
    (hc : cost p z ≤ 0) : z = 0 := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ p i * z i := fun i _ => mul_nonneg (hp i).le (hz i)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
    (le_antisymm hc (Finset.sum_nonneg hnn))
  funext i
  exact (mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hp i).ne'

omit [Fintype ι] in
/-- **Cheaper point**: if every bundle preferred to `xa` costs at least the
wealth `p · e > 0`, and the upper set of `xa` is relatively open, then no
affordable bundle is preferred to `xa` (shrink it slightly towards `0`). -/
theorem not_P_of_cost_le [Fintype ι] {R : (ι → ℝ) → (ι → ℝ) → Prop} {p xa e y : ι → ℝ}
    (hsupp : ∀ z, 0 ≤ z → P R z xa → cost p e ≤ cost p z)
    (hcont : ∀ z, 0 ≤ z → P R z xa → ∀ᶠ w in 𝓝 z, 0 ≤ w → P R w xa)
    (he : 0 < cost p e) (hy : 0 ≤ y) (hyc : cost p y ≤ cost p e) : ¬ P R y xa := by
  intro hP
  have ht : Tendsto (fun s : ℝ => s • y) (𝓝[<] 1) (𝓝 y) := by
    have h : Tendsto (fun s : ℝ => s • y) (𝓝 1) (𝓝 ((1 : ℝ) • y)) :=
      (continuous_id.smul continuous_const : Continuous fun s : ℝ => s • y).tendsto 1
    rw [one_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs1, hs2⟩ :=
    ((ht.eventually (hcont y hy hP)).and (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))).exists
  have hsy : 0 ≤ s • y := fun i => by
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hs2.1.le (hy i)
  have := hsupp _ hsy (hs1 hsy)
  rw [cost_smul_right] at this
  nlinarith [hs2.1, hs2.2]

/-- **Aumann's core equivalence theorem (core ⊆ Walrasian)** (Aumann 1964).
In an exchange economy with a finite nonatomic measure space of traders, positive
aggregate endowment, and preferences that are almost surely rational, strongly
monotone, and continuous (in the form: the strict upper set of `x a` is
relatively open in `ℝ₊^ι`), every core allocation `x` satisfying the
measurability condition `hmeas` is a Walrasian allocation, at strictly positive
prices. -/
theorem InCore.isWalrasianEquilibrium [Nonempty ι] {x : Ω → ι → ℝ} (hx : E.InCore x)
    [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i)
    (hrat : ∀ᵐ a ∂E.μ, Rational (E.pref a))
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hcont : ∀ᵐ a ∂E.μ, ∀ z, 0 ≤ z → P (E.pref a) z (x a) →
      ∀ᶠ w in 𝓝 z, 0 ≤ w → P (E.pref a) w (x a))
    (hmeas : ∀ y : Ω → ι → ℝ, AEStronglyMeasurable y E.μ →
      NullMeasurableSet {a | P (E.pref a) (y a) (x a)} E.μ) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ E.IsWalrasianEquilibrium p x := by
  classical
  have htrans : ∀ᵐ a ∂E.μ, ∀ {u v w}, E.pref a u v → E.pref a v w → E.pref a u w :=
    hrat.mono fun a h => h.trans
  obtain ⟨p, hp0, hc, hp⟩ := hx.exists_price hμ htrans hmono hmeas
  have hsupp := ae_price_support hmeas hcont hp
  have hxnn : ∀ᵐ a ∂E.μ, 0 ≤ x a := hx.1.2.1
  have hxi : Integrable x E.μ := hx.1.1
  -- budget exhaustion from below: `p · e a ≤ p · x a`
  have hge : ∀ᵐ a ∂E.μ, cost p (E.endow a) ≤ cost p (x a) := by
    filter_upwards [hsupp, hmono, hxnn] with a hs hm hx0
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ := ε / ∑ i, p i
    have hδ : 0 < δ := div_pos hε hc
    have hle : x a ≤ x a + fun _ => δ := fun i => by simp only [Pi.add_apply]; linarith
    have hne : x a ≠ x a + fun _ => δ := by
      obtain ⟨i⟩ := ‹Nonempty ι›
      intro h
      have := congrFun h i
      simp only [Pi.add_apply] at this
      linarith
    have := hs _ (hx0.trans hle) (hm _ _ hx0 hle hne)
    rwa [cost_add_right, cost_const_eq, div_mul_cancel₀ _ hc.ne'] at this
  have hcx : Integrable (fun a => cost p (x a)) E.μ :=
    ((costCLM p).integrable_comp hxi).congr (ae_of_all _ fun a => costCLM_apply p _)
  have hce : Integrable (fun a => cost p (E.endow a)) E.μ :=
    ((costCLM p).integrable_comp E.endow_integrable).congr
      (ae_of_all _ fun a => costCLM_apply p _)
  have hint : ∀ {f : Ω → ι → ℝ}, Integrable f E.μ →
      ∫ a, cost p (f a) ∂E.μ = cost p (∫ a, f a ∂E.μ) := by
    intro f hf
    rw [← costCLM_apply, ← (costCLM p).integral_comp_comm hf]
    simp only [costCLM_apply]
  -- hence `p · x a = p · e a` almost everywhere
  have heq : ∀ᵐ a ∂E.μ, cost p (x a) = cost p (E.endow a) := by
    have h0 : ∫ a, (cost p (x a) - cost p (E.endow a)) ∂E.μ = 0 := by
      rw [integral_sub hcx hce, hint hxi, hint E.endow_integrable, hx.1.2.2, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae
      (hge.mono fun a ha => sub_nonneg.2 ha) (hcx.sub hce)).1 h0
    filter_upwards [this] with a ha
    exact sub_eq_zero.1 ha
  have hcheap : ∀ᵐ a ∂E.μ, 0 < cost p (E.endow a) → ∀ y, 0 ≤ y →
      cost p y ≤ cost p (E.endow a) → ¬ P (E.pref a) y (x a) := by
    filter_upwards [hsupp, hcont] with a hs hco hpos y hy hyc
    exact not_P_of_cost_le hs hco hpos hy hyc
  -- prices are strictly positive
  have hpos : ∀ i, 0 < p i := by
    intro i
    by_contra hpi
    have hpi0 : p i = 0 := le_antisymm (not_lt.1 hpi) (hp0 i)
    have hfreq : ∃ᵐ a ∂E.μ, 0 < cost p (E.endow a) := by
      by_contra hnot
      rw [not_frequently] at hnot
      have hle : ∫ a, cost p (E.endow a) ∂E.μ ≤ 0 :=
        integral_nonpos_of_ae (hnot.mono fun a ha => not_lt.1 ha)
      rw [hint E.endow_integrable] at hle
      obtain ⟨j, hj⟩ : ∃ j, 0 < p j := by
        by_contra h
        push Not at h
        exact absurd (Finset.sum_nonpos fun j _ => h j) (not_le.2 hc)
      have : 0 < cost p (∫ a, E.endow a ∂E.μ) :=
        Finset.sum_pos' (fun k _ => mul_nonneg (hp0 k) (he k).le)
          ⟨j, Finset.mem_univ _, mul_pos hj (he j)⟩
      linarith
    obtain ⟨a, ⟨⟨heqa, hx0⟩, hch, hm⟩, hcpos⟩ :=
      (((heq.and hxnn).and (hcheap.and hmono)).and_frequently hfreq).exists
    set y := x a + Pi.single i 1
    have hle : x a ≤ y := fun j => by
      simp only [y, Pi.add_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have hne : x a ≠ y := by
      intro h
      have := congrFun h i
      simp [y] at this
    have hcy : cost p y = cost p (x a) := by
      rw [cost_add_right]
      simp [cost, Pi.single_apply, hpi0]
    exact hch hcpos y (hx0.trans hle) (by rw [hcy, heqa]) (hm _ _ hx0 hle hne)
  refine ⟨p, hpos, hx.1, ?_⟩
  filter_upwards [heq, hxnn, hcheap, hrat] with a heqa hx0 hch hr
  refine ⟨⟨hx0, heqa.le⟩, fun y ⟨hy0, hyc⟩ => ?_⟩
  by_contra hR
  have hP : P (E.pref a) y (x a) := ⟨(hr.complete _ _).resolve_left hR, hR⟩
  rcases lt_or_ge 0 (cost p (E.endow a)) with hcpos | hcnp
  · exact hch hcpos y hy0 hyc hP
  · have hy : y = 0 := eq_zero_of_cost_nonpos hpos hy0 (hyc.trans hcnp)
    have hxa : x a = 0 := eq_zero_of_cost_nonpos hpos hx0 (heqa.le.trans hcnp)
    rw [hy, hxa] at hP
    exact P_irrefl _ _ hP

/-! ### The canonical hypotheses -/

omit [Fintype ι] in
/-- For rational, continuous preferences (closed lower sets in `ℝ₊^ι`) the strict
upper set of a bundle `xa ≥ 0` is relatively open in `ℝ₊^ι`. -/
theorem eventually_P_of_continuousPref [Fintype ι] {R : (ι → ℝ) → (ι → ℝ) → Prop}
    (hr : Rational R) (hc : ContinuousPref R) {xa z : ι → ℝ} (hxa : 0 ≤ xa) (hz : P R z xa) :
    ∀ᶠ w in 𝓝 z, 0 ≤ w → P R w xa := by
  have hz' : z ∉ {y : ι → ℝ | 0 ≤ y ∧ R xa y} := fun h => hz.2 h.2
  filter_upwards [(hc xa hxa).2.isOpen_compl.mem_nhds hz'] with w hw hw0
  exact ⟨(hr.complete w xa).resolve_right fun h => hw ⟨hw0, h⟩, fun h => hw ⟨hw0, h⟩⟩

/-- If the strict preference relation is jointly measurable in
`(trader, bundle, bundle)`, the measurability hypothesis of
`InCore.isWalrasianEquilibrium` holds for every a.e.-measurable `x`. -/
theorem nullMeasurableSet_P {x : Ω → ι → ℝ} (hx : AEMeasurable x E.μ)
    (hR : MeasurableSet {q : Ω × (ι → ℝ) × (ι → ℝ) | P (E.pref q.1) q.2.1 q.2.2})
    (y : Ω → ι → ℝ) (hy : AEStronglyMeasurable y E.μ) :
    NullMeasurableSet {a | P (E.pref a) (y a) (x a)} E.μ :=
  (aemeasurable_id.prodMk (hy.aemeasurable.prodMk hx)).nullMeasurable hR

/-- **Aumann's core equivalence theorem (core ⊆ Walrasian)**, textbook form:
finite nonatomic measure of traders, positive aggregate endowment, and
preferences that are almost surely rational, strongly monotone and continuous,
with jointly measurable strict preference (graph measurability as in
Hildenbrand 1974, Ch. 2; Aumann's own 1964 axiom is the pairwise measurability
of `{a | y a ≻_a x a}`, of which `hmeas` is the special case used).
Then every core allocation is Walrasian at strictly positive prices. -/
theorem InCore.isWalrasianEquilibrium_of_continuousPref [Nonempty ι] {x : Ω → ι → ℝ}
    (hx : E.InCore x) [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i)
    (hrat : ∀ᵐ a ∂E.μ, Rational (E.pref a))
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hcont : ∀ᵐ a ∂E.μ, ContinuousPref (E.pref a))
    (hR : MeasurableSet {q : Ω × (ι → ℝ) × (ι → ℝ) | P (E.pref q.1) q.2.1 q.2.2}) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ E.IsWalrasianEquilibrium p x := by
  refine hx.isWalrasianEquilibrium hμ he hrat hmono ?_ (E.nullMeasurableSet_P hx.1.1.aemeasurable hR)
  filter_upwards [hrat, hcont, hx.1.2.1] with a hr hc hx0 z _ hz
  exact eventually_P_of_continuousPref hr hc hx0 hz

/-- **Aumann's core equivalence theorem** (Aumann 1964): under the canonical
hypotheses the core coincides with the set of Walrasian allocations. Requiring
`p ≫ 0` on the right loses nothing: under strong monotonicity every Walrasian
price is strictly positive (a free good would be demanded without bound). -/
theorem inCore_iff_of_continuousPref [Nonempty ι] [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i)
    (hrat : ∀ᵐ a ∂E.μ, Rational (E.pref a))
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hcont : ∀ᵐ a ∂E.μ, ContinuousPref (E.pref a))
    (hR : MeasurableSet {q : Ω × (ι → ℝ) × (ι → ℝ) | P (E.pref q.1) q.2.1 q.2.2})
    (x : Ω → ι → ℝ) :
    E.InCore x ↔ ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ E.IsWalrasianEquilibrium p x :=
  ⟨fun hx => hx.isWalrasianEquilibrium_of_continuousPref hμ he hrat hmono hcont hR,
    fun ⟨_, _, h⟩ => h.inCore⟩

/-! ### Witness: full core equivalence for `linContinuum` -/

/-- **Core equivalence for `linContinuum`**: an allocation of the uniform
continuum of perfect-substitutes traders is in the core iff it is Walrasian at
some strictly positive prices. The canonical hypotheses hold (hence so do those
of the general theorem `InCore.isWalrasianEquilibrium`). -/
theorem linContinuum_inCore_iff (x : ℝ → Fin 2 → ℝ) :
    linContinuum.InCore x ↔
      ∃ p : Fin 2 → ℝ, (∀ i, 0 < p i) ∧ linContinuum.IsWalrasianEquilibrium p x := by
  constructor
  · intro hx
    have hP : ∀ a z w, P (linContinuum.pref a) z w ↔ GEExamples.uLin w < GEExamples.uLin z :=
      fun _ z w => (represents_prefOf GEExamples.uLin).P_iff z w
    have : IsFiniteMeasure linContinuum.μ := by
      unfold linContinuum; infer_instance
    refine hx.isWalrasianEquilibrium_of_continuousPref nonatomic_volume_Icc ?_
      (ae_of_all _ fun _ => GEExamples.rational_lin 0)
      (ae_of_all _ fun _ => GEExamples.stronglyMonotone_lin 0)
      (ae_of_all _ fun _ => GEExamples.continuousPref_lin 0) ?_
    · intro i
      simp [linContinuum]
    · have hset : {q : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) | P (linContinuum.pref q.1) q.2.1 q.2.2} =
          {q | GEExamples.uLin q.2.2 < GEExamples.uLin q.2.1} := by
        ext q; exact hP _ _ _
      rw [hset]
      exact measurableSet_lt (GEExamples.continuous_uLin.measurable.comp measurable_snd.snd)
        (GEExamples.continuous_uLin.measurable.comp measurable_snd.fst)
  · rintro ⟨p, -, h⟩
    exact h.inCore

/-! ### Witness: a non-convex, trader-dependent economy -/

/-- Trader `a`'s utility `max(z₀, z₁) + (1 + a²)(z₀ + z₁)`: continuous, strongly
monotone, but **not quasi-concave**. -/
def uBump (a : ℝ) (z : Fin 2 → ℝ) : ℝ := max (z 0) (z 1) + (1 + a ^ 2) * (z 0 + z 1)

theorem continuous_uBump_uncurry : Continuous fun q : ℝ × (Fin 2 → ℝ) => uBump q.1 q.2 := by
  unfold uBump; fun_prop

theorem continuous_uBump (a : ℝ) : Continuous (uBump a) :=
  continuous_uBump_uncurry.comp (Continuous.prodMk_right a)

theorem stronglyMonotone_uBump (a : ℝ) : StronglyMonotone (prefOf (uBump a)) := by
  intro x y _ hxy hne
  have hlt : uBump a x < uBump a y := by
    have h0 := hxy 0
    have h1 := hxy 1
    have hs : x 0 + x 1 < y 0 + y 1 := by
      by_contra hle
      apply hne
      funext i
      fin_cases i
      · show x 0 = y 0; linarith
      · show x 1 = y 1; linarith
    have hm : max (x 0) (x 1) ≤ max (y 0) (y 1) := max_le_max h0 h1
    have hc : 0 < 1 + a ^ 2 := by positivity
    unfold uBump
    nlinarith
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- A continuum economy with non-convex, trader-dependent preferences. -/
def bumpContinuum : ContinuumEconomy ℝ (Fin 2) where
  μ := volume.restrict (Icc (0 : ℝ) 1)
  pref a := prefOf (uBump a)
  endow _ := fun _ => 1
  endow_nonneg _ _ := zero_le_one
  endow_integrable := integrable_const _

/-- Traders in `bumpContinuum` have **non-convex** preferences. -/
theorem bumpContinuum_not_convexPref (a : ℝ) : ¬ ConvexPref (bumpContinuum.pref a) := by
  intro h
  have hx : (0 : Fin 2 → ℝ) ≤ ![1, 0] := fun i => by fin_cases i <;> simp
  have hy : (0 : Fin 2 → ℝ) ≤ ![0, 1] := fun i => by fin_cases i <;> simp
  have h1 : ![1, 0] ∈ {y : Fin 2 → ℝ | 0 ≤ y ∧ bumpContinuum.pref a y ![1, 0]} :=
    ⟨hx, show uBump a ![1, 0] ≤ uBump a ![1, 0] from le_rfl⟩
  have h2 : ![0, 1] ∈ {y : Fin 2 → ℝ | 0 ≤ y ∧ bumpContinuum.pref a y ![1, 0]} :=
    ⟨hy, show uBump a ![1, 0] ≤ uBump a ![0, 1] by simp [uBump]⟩
  have hmem := h ![1, 0] hx h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have := hmem.2
  change uBump a ![1, 0] ≤ uBump a _ at this
  simp [uBump] at this
  nlinarith [sq_nonneg a]

/-- **Core equivalence for a non-convex economy**: `bumpContinuum` (uniform
traders on `[0, 1]`, endowment `(1, 1)`, utility `uBump a`) satisfies every
canonical hypothesis, with trader-dependent, non-convex preferences. -/
theorem bumpContinuum_inCore_iff (x : ℝ → Fin 2 → ℝ) :
    bumpContinuum.InCore x ↔
      ∃ p : Fin 2 → ℝ, (∀ i, 0 < p i) ∧ bumpContinuum.IsWalrasianEquilibrium p x := by
  have : IsFiniteMeasure bumpContinuum.μ := by unfold bumpContinuum; infer_instance
  refine inCore_iff_of_continuousPref nonatomic_volume_Icc ?_
    (ae_of_all _ fun a => (represents_prefOf (uBump a)).rational)
    (ae_of_all _ fun a => stronglyMonotone_uBump a)
    (ae_of_all _ fun a => continuousPref_prefOf (continuous_uBump a)) ?_ x
  · intro i; simp [bumpContinuum]
  · have hset : {q : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) | P (bumpContinuum.pref q.1) q.2.1 q.2.2} =
        {q | uBump q.1 q.2.2 < uBump q.1 q.2.1} := by
      ext q; exact (represents_prefOf (uBump q.1)).P_iff _ _
    rw [hset]
    exact measurableSet_lt
      (continuous_uBump_uncurry.comp (continuous_fst.prodMk continuous_snd.snd)).measurable
      (continuous_uBump_uncurry.comp (continuous_fst.prodMk continuous_snd.fst)).measurable

end ContinuumEconomy
end Continuum
end Econ
