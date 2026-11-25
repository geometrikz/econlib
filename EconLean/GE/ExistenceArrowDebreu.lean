/-
# Arrow–Debreu existence with convex production (Kakutani)

PLAN.md §1 (M4). Arrow & Debreu (1954), Theorem I; Debreu (1959) ch. 5;
MWG §17.B and Appendix 17.BB.

A private ownership economy with
* consumers with continuous utilities (stated on all of `ℝᴸ`; any utility
  continuous on `ℝᴸ₊` extends) that are **quasiconcave on `ℝᴸ₊`** (convex
  preferences, not necessarily strictly convex) and strongly monotone, and **strictly positive endowments** `ωₐ ≫ 0` (Arrow–Debreu's
  survival assumption), and
* firms with **closed convex** production sets `Yⱼ ∋ 0`, whose sum `Y = ∑ⱼ Yⱼ`
  has no free lunch (`Y ∩ ℝᴸ₊ ⊆ {0}`) and is irreversible (`Y ∩ (−Y) ⊆ {0}`)

has a Walrasian equilibrium at strictly positive prices
(`exists_walrasianEquilibrium_arrowDebreu_convex`; the strictly quasiconcave case
is `exists_walrasianEquilibrium_arrowDebreu`). Production sets may be unbounded,
have flat faces, show **constant returns to scale**, or allow **free disposal**;
supply and demand may both be set-valued, which is why the proof uses Kakutani's
theorem rather than Brouwer's.

Proof (the classical truncation argument).
1. Attainable production is bounded by some `R` (`exists_bound_attainable`).
   Truncate each `Yⱼ` to `Tⱼ = Yⱼ ∩ B̄(0, R + 1)` and consumption to the box
   `[0, c]ᴸ` with `c > ∑ᵢ ωᵢ + |J| R` (`ω` the total endowment).
2. Truncated demand, `argmax uₐ` over `{x ∈ [0, c]ᴸ | p · x ≤ max w mₐ}` with
   `mₐ = minᵢ ωₐᵢ > 0`, has nonempty convex values (quasiconcavity) and a closed
   graph in `(p, w, x)` by Berge (`truncDemand_props`); the floor `mₐ` keeps a
   strictly cheaper bundle, so the budget is lower hemicontinuous at every
   price. (With strict quasiconcavity it is a continuous function,
   `exists_continuous_truncDemand`.)
3. Kakutani on `Δ × [0, c]^{A×L} × ∏ⱼ Tⱼ`: prices maximize the value of excess
   demand on the simplex, consumers demand at wealth
   `p · ωₐ + ∑ⱼ θₐⱼ max(0, p · yⱼ)`, firms maximize profit on `Tⱼ`.
4. At a fixed point, profits are `≥ 0` (`0 ∈ Tⱼ`), wealth is at least
   `p · ωₐ ≥ mₐ`, summing budgets gives `p · z ≤ 0`, and price maximization gives
   `z ≤ 0`. So production is attainable and lies strictly inside the
   truncation, consumption strictly inside the box, and by convexity firms
   maximize on `Yⱼ`. Consumers maximize on their whole budget sets: given a
   better affordable bundle, shrink it to leave money unspent, mix a little of
   it into `xₐ` (no worse, by quasiconcavity) and add a little of every good
   (strictly better, by strong monotonicity), all inside the box and the
   budget. Strong
   monotonicity then forces `p ≫ 0` and binding budgets, so `p · z = 0` and
   `z = 0`.

Scope. Preferences are convex (quasiconcave utility on `ℝᴸ₊`), continuous and
strongly monotone, with consumption set `ℝᴸ₊`; Arrow–Debreu allow general
consumption sets and mere nonsatiation, and obtain `p ≥ 0` with free goods in excess supply. Here
prices are `≫ 0` and markets clear exactly. Individual endowments
must be strictly positive (the canonical survival assumption), unlike the
compact-production theorems in `GE/ExistenceProduction.lean`.

Witness: `linearEconomy`, one firm with the constant-returns free-disposal
technology `{y | y₀ ≤ 0 ∧ y₀ + y₁ ≤ 0}` (convert good 0 one-for-one into good 1,
and dispose freely), which is a cone, unbounded and not strictly convex
(`linearSet_not_strictConvex`); being unbounded it is not compact either, so
neither earlier theorem applies. Only existence is claimed: with these
symmetric consumers the firm may well be inactive in equilibrium.
`substEconomy` uses the same firm with perfect-substitutes consumers
`x₀ + x₁`, whose preferences are convex but not strictly convex
(`not_strictlyQuasiconcave_of_prefOf_eq_uLin`: no representation of them is
strictly quasiconcave).
-/
module

public import EconLean.GE.ExistenceUnbounded
public import EconLean.GE.ExistenceGeneral
public import Mathlib.Analysis.Convex.Quasiconvex

@[expose] public section

namespace Econ

open Filter Topology Set Finset

variable {ι : Type*} [Fintype ι]

/-! ### Truncated budget sets and truncated demand -/

/-- The **truncated budget set**: bundles in the box `[0, c]ᴸ` costing at most
`max w m` at prices `p`. -/
def truncBudget (c m : ℝ) (pw : (ι → ℝ) × ℝ) : Set (ι → ℝ) :=
  {x | x ∈ Icc (0 : ι → ℝ) (fun _ => c) ∧ cost pw.1 x ≤ max pw.2 m}

theorem continuous_cost_right (p : ι → ℝ) : Continuous fun x : ι → ℝ => cost p x := by
  unfold cost; fun_prop

theorem isClosed_truncBudget (c m : ℝ) (pw : (ι → ℝ) × ℝ) :
    IsClosed (truncBudget (ι := ι) c m pw) :=
  isClosed_Icc.inter (isClosed_le (continuous_cost_right _) continuous_const)

theorem convex_truncBudget (c m : ℝ) (pw : (ι → ℝ) × ℝ) :
    Convex ℝ (truncBudget (ι := ι) c m pw) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc _ _ hx.1 hy.1 ha hb hab, ?_⟩
  show cost pw.1 (a • x + b • y) ≤ max pw.2 m
  rw [cost_add_right, cost_smul_right, cost_smul_right]
  have h1 : cost pw.1 x ≤ max pw.2 m := hx.2
  have h2 : cost pw.1 y ≤ max pw.2 m := hy.2
  have := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  rw [← add_mul, hab, one_mul] at this
  exact this

theorem isClosed_graph_truncBudget (c m : ℝ) :
    IsClosed (graph (truncBudget (ι := ι) c m)) := by
  have h1 : IsClosed {q : ((ι → ℝ) × ℝ) × (ι → ℝ) | q.2 ∈ Icc (0 : ι → ℝ) (fun _ => c)} :=
    isClosed_Icc.preimage continuous_snd
  have h2 : IsClosed {q : ((ι → ℝ) × ℝ) × (ι → ℝ) | cost q.1.1 q.2 ≤ max q.1.2 m} :=
    isClosed_le (by unfold cost; fun_prop) (by fun_prop)
  exact h1.inter h2

/-- **The truncated budget correspondence is continuous** for `m > 0`: upper
hemicontinuous because it is closed and inside a fixed box, lower
hemicontinuous because `0` is strictly cheaper than `max w m`. -/
theorem continuousCorrespondence_truncBudget (c m : ℝ) (hm : 0 < m) :
    ContinuousCorrespondence (truncBudget (ι := ι) c m) := by
  refine ⟨fun pw => upperHemicontinuousAt_of_isClosed_graph (isClosed_graph_truncBudget c m)
    (isCompact_Icc (a := (0 : ι → ℝ)) (b := fun _ => c))
    (Eventually.of_forall fun _ _ hx => hx.1), ?_⟩
  intro pw
  show LowerHemicontinuousAt (truncBudget c m) pw
  refine lowerHemicontinuousAt_iff_textbook.2 ?_
  rintro U hU ⟨y, hyB, hyU⟩
  obtain ⟨p, w⟩ := pw
  have hcont : Continuous fun t : ℝ => t • y := continuous_id.smul continuous_const
  have hev1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t • y ∈ U :=
    nhdsWithin_le_nhds (hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hyU))
  have hev2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  obtain ⟨t, htU, ht0, ht1⟩ := (hev1.and hev2).exists
  have hM : 0 < max w m := lt_max_of_lt_right hm
  have hcw : cost p y ≤ max w m := hyB.2
  have hzc : cost p (t • y) < max w m := by
    rw [cost_smul_right]
    rcases le_or_gt (cost p y) 0 with h | h
    · nlinarith
    · nlinarith
  have hz : t • y ∈ Icc (0 : ι → ℝ) (fun _ => c) := by
    refine ⟨smul_nonneg ht0.le hyB.1.1, fun i => ?_⟩
    have h1 := hyB.1.1 i
    have h2 := hyB.1.2 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
    nlinarith
  have hg : Continuous fun q : (ι → ℝ) × ℝ => max q.2 m - cost q.1 (t • y) := by
    unfold cost; fun_prop
  have hev : ∀ᶠ q in 𝓝 (p, w), 0 < max q.2 m - cost q.1 (t • y) :=
    hg.continuousAt.eventually (lt_mem_nhds (by simpa using hzc))
  filter_upwards [hev] with q hq
  exact ⟨t • y, ⟨hz, by linarith⟩, htU⟩

/-- **Continuous truncated demand.** For continuous strictly quasiconcave `u`,
the maximizer of `u` on the truncated budget set is unique and depends
continuously on `(p, w)` (Berge). -/
theorem exists_continuous_truncDemand {u : (ι → ℝ) → ℝ} (hu : Continuous u)
    (hsq : StrictlyQuasiconcave u) (c m : ℝ) (hc : 0 ≤ c) (hm : 0 < m) :
    ∃ g : (ι → ℝ) × ℝ → (ι → ℝ), Continuous g ∧
      ∀ pw, g pw ∈ truncBudget c m pw ∧ ∀ x ∈ truncBudget c m pw, u x ≤ u (g pw) := by
  have hf : Continuous (Function.uncurry fun (_ : (ι → ℝ) × ℝ) (x : ι → ℝ) => u x) :=
    hu.comp continuous_snd
  have hne : ∀ pw, (truncBudget (ι := ι) c m pw).Nonempty := by
    intro pw
    have h0 : cost pw.1 (0 : ι → ℝ) ≤ max pw.2 m := by
      simp only [cost, Pi.zero_apply, mul_zero, sum_const_zero]
      exact le_max_of_le_right hm.le
    exact ⟨0, ⟨le_rfl, fun _ => hc⟩, h0⟩
  have hK : ∀ pw, IsCompact (truncBudget (ι := ι) c m pw) := fun pw =>
    isCompact_Icc.of_isClosed_subset (isClosed_truncBudget c m pw) fun _ h => h.1
  have hΦ := continuousCorrespondence_truncBudget (ι := ι) c m hm
  choose g hg using fun pw => argmax_nonempty hf (hne pw) (hK pw)
  have hsing : ∀ pw, argmax (fun _ x => u x) (truncBudget c m) pw = {g pw} := by
    intro pw
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hg pw, fun x hx => ?_⟩
    by_contra hxg
    have hmid := hsq x (g pw) hx.1.1.1 (hg pw).1.1.1 hxg (1 / 2) (by norm_num) (by norm_num)
    have hmB : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • g pw ∈ truncBudget c m pw :=
      convex_truncBudget c m pw hx.1 (hg pw).1 (by norm_num) (by norm_num) (by norm_num)
    exact absurd hmid (not_lt.2 (le_min (hx.2 _ hmB) ((hg pw).2 _ hmB)))
  exact ⟨g, continuous_of_argmax_eq_singleton hf hΦ hne hK hsing,
    fun pw => ⟨(hg pw).1, (hg pw).2⟩⟩

/-- Strictly quasiconcave utilities are quasiconcave on `ℝᴸ₊` (convex preferences). -/
theorem StrictlyQuasiconcave.quasiconcaveOn {u : (ι → ℝ) → ℝ} (h : StrictlyQuasiconcave u) :
    QuasiconcaveOn ℝ (Ici 0) u := by
  intro r x hx y hy a b ha hb hab
  refine ⟨(convex_Ici (0 : ι → ℝ)) hx.1 hy.1 ha hb hab, ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simpa using hy.2
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [add_zero] at hab; subst hab; simpa using hx.2
  by_cases hxy : x = y
  · subst hxy; rw [← add_smul, hab, one_smul]; exact hx.2
  have hb1 : b = 1 - a := by linarith
  subst hb1
  exact (le_min hx.2 hy.2).trans (h x y hx.1 hy.1 hxy a ha' (by linarith)).le

/-- **Set-valued truncated demand** for a continuous utility that is
quasiconcave on `ℝᴸ₊`: the maximizers of `u` on the truncated budget set are
nonempty and convex, and they form a closed graph in `(p, w, x)` (Berge). -/
theorem truncDemand_props {u : (ι → ℝ) → ℝ} (hu : Continuous u)
    (hqc : QuasiconcaveOn ℝ (Ici 0) u) (c m : ℝ) (hc : 0 ≤ c) (hm : 0 < m) :
    IsClosed (graph (argmax (fun (_ : (ι → ℝ) × ℝ) x => u x) (truncBudget c m))) ∧
      ∀ pw, (argmax (fun _ x => u x) (truncBudget c m) pw).Nonempty ∧
        Convex ℝ (argmax (fun _ x => u x) (truncBudget c m) pw) := by
  have hf : Continuous (Function.uncurry fun (_ : (ι → ℝ) × ℝ) (x : ι → ℝ) => u x) :=
    hu.comp continuous_snd
  have hne : ∀ pw, (truncBudget (ι := ι) c m pw).Nonempty := by
    intro pw
    have h0 : cost pw.1 (0 : ι → ℝ) ≤ max pw.2 m := by
      simp only [cost, Pi.zero_apply, mul_zero, sum_const_zero]
      exact le_max_of_le_right hm.le
    exact ⟨0, ⟨le_rfl, fun _ => hc⟩, h0⟩
  have hK : ∀ pw, IsCompact (truncBudget (ι := ι) c m pw) := fun pw =>
    isCompact_Icc.of_isClosed_subset (isClosed_truncBudget c m pw) fun _ h => h.1
  have hΦ := continuousCorrespondence_truncBudget (ι := ι) c m hm
  refine ⟨isClosed_graph_of_upperHemicontinuous (upperHemicontinuous_argmax hf hΦ hne hK)
    fun pw => (isCompact_argmax hf (hne pw) (hK pw)).isClosed, fun pw =>
      ⟨argmax_nonempty hf (hne pw) (hK pw), ?_⟩⟩
  intro x hx y hy a b ha hb hab
  refine ⟨convex_truncBudget c m pw hx.1 hy.1 ha hb hab, fun x' hx' => ?_⟩
  have hxy : u x ≤ u y := hy.2 x hx.1
  have hmem := hqc (u x) ⟨hx.1.1.1, le_rfl⟩ ⟨hy.1.1.1, hxy⟩ ha hb hab
  exact (hx.2 x' hx').trans hmem.2

/-! ### The existence theorem -/

namespace ProductionEconomy

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Arrow–Debreu existence theorem with convex production and convex
preferences** (Arrow–Debreu 1954, Theorem I, with consumption set `ℝᴸ₊` and
strongly monotone utilities, so prices are `≫ 0` and markets clear exactly).
Consumers have continuous utilities, quasiconcave on `ℝᴸ₊`, strongly monotone,
and endowments `ωₐ ≫ 0`;
production sets are closed and convex with `0 ∈ Yⱼ`, and their sum has no free
lunch and is irreversible. Production sets may be unbounded, with constant
returns or free disposal. Then a Walrasian equilibrium exists at strictly
positive prices. -/
theorem exists_walrasianEquilibrium_arrowDebreu_convex [Nonempty ι] [Nonempty α]
    (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hqc : ∀ a, QuasiconcaveOn ℝ (Ici 0) (u a)) (hmono : ∀ a, StronglyMonotone (prefOf (u a)))
    (hωa : ∀ a, PositivePrices (E.endow a))
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y := by
  classical
  -- Step 0: bounds and truncations.
  have hω0 : 0 ≤ E.totalEndowment := sum_nonneg fun a _ => E.endow_nonneg a
  obtain ⟨R, hR⟩ := E.exists_bound_attainable hY0 hYcl hYcv hnfl hirr (-E.totalEndowment)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (fun j => hY0 j) (by simpa using hω0))
  set r : ℝ := R + 1 with hr
  set T : β → Set (ι → ℝ) := fun j => E.prod j ∩ Metric.closedBall 0 r with hT
  have hT0 : ∀ j, (0 : ι → ℝ) ∈ T j := fun j =>
    ⟨hY0 j, Metric.mem_closedBall_self (by linarith)⟩
  have hTc : ∀ j, IsCompact (T j) := fun j => (isCompact_closedBall _ _).inter_left (hYcl j)
  have hTcv : ∀ j, Convex ℝ (T j) := fun j => (hYcv j).inter (convex_closedBall _ _)
  set c : ℝ := ∑ i, E.totalEndowment i + Fintype.card β * R + 1 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ∑ i, E.totalEndowment i := sum_nonneg fun i _ => hω0 i
    positivity
  have hm : ∀ a, ∃ m, 0 < m ∧ ∀ i, m ≤ E.endow a i := fun a => by
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image univ (E.endow a) univ_nonempty
    exact ⟨E.endow a i0, hωa a i0, fun i => hi0 i (mem_univ i)⟩
  choose m hm0 hmle using hm
  have hD := fun a => truncDemand_props (hu a) (hqc a) c (m a) hc0 (hm0 a)
  set D : α → (ι → ℝ) × ℝ → Set (ι → ℝ) := fun a =>
    argmax (fun (_ : (ι → ℝ) × ℝ) x => u a x) (truncBudget c (m a)) with hDdef
  set W : α → (ι → ℝ) → (β → ι → ℝ) → ℝ := fun a p y =>
    cost p (E.endow a) + ∑ j, E.share a j * max 0 (cost p (y j)) with hW
  set Δ := priceSimplex ι with hΔ
  set zf : (ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ) → (ι → ℝ) := fun v =>
    ∑ a, v.2.1 a - E.totalEndowment - ∑ j, v.2.2 j with hzf
  set s : Set ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) :=
    Δ ×ˢ (Icc (0 : α → ι → ℝ) (fun _ _ => c) ×ˢ Set.pi univ T) with hs
  set φ : (ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ) → Set ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) :=
    fun v => {v' | (v'.1 ∈ Δ ∧ ∀ q ∈ Δ, cost q (zf v) ≤ cost v'.1 (zf v)) ∧
      ((∀ a, v'.2.1 a ∈ D a (v.1, W a v.1 v.2.2)) ∧ ∀ j, v'.2.2 j ∈ T j ∧ ∀ y' ∈ T j, cost v.1 y' ≤ cost v.1 (v'.2.2 j))}
    with hφ
  -- Continuity facts.
  have hcost : Continuous fun pq : (ι → ℝ) × (ι → ℝ) => cost pq.1 pq.2 := by
    unfold cost; fun_prop
  have hzfc : Continuous zf := by
    simp only [hzf]
    refine (Continuous.sub (continuous_finsetSum _ fun a _ =>
      (continuous_apply a).comp (continuous_fst.comp continuous_snd)) continuous_const).sub
      (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_snd.comp continuous_snd))
  have hWc : ∀ a, Continuous fun v : (ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ) =>
      W a v.1 v.2.2 := fun a => by
    simp only [hW]
    refine (hcost.comp (continuous_fst.prodMk continuous_const)).add
      (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_const.max
        (hcost.comp (continuous_fst.prodMk
          ((continuous_apply j).comp (continuous_snd.comp continuous_snd))))))
  have hΔc : IsClosed Δ := isCompact_priceSimplex.isClosed
  -- Kakutani's hypotheses.
  have hconv : Convex ℝ s :=
    convex_priceSimplex.prod ((convex_Icc _ _).prod (convex_pi fun j _ => hTcv j))
  have hcomp : IsCompact s :=
    isCompact_priceSimplex.prod (isCompact_Icc.prod (isCompact_univ_pi hTc))
  obtain ⟨p0, hp0⟩ := priceSimplex_nonempty (ι := ι)
  have hsne : s.Nonempty :=
    ⟨(p0, 0, 0), hp0, ⟨le_rfl, fun _ _ => hc0⟩, fun j _ => hT0 j⟩
  have hPM : ∀ (p : ι → ℝ) j, ∃ y ∈ T j, ∀ y' ∈ T j, cost p y' ≤ cost p y := fun p j => by
    obtain ⟨y, hy, hmax⟩ := (hTc j).exists_isMaxOn ⟨0, hT0 j⟩
      (continuous_cost_right p).continuousOn
    exact ⟨y, hy, fun y' hy' => hmax hy'⟩
  have hmaps : ∀ v ∈ s, φ v ⊆ s := by
    intro v _ v' hv'
    refine ⟨hv'.1.1, ?_, fun j _ => (hv'.2.2 j).1⟩
    exact ⟨fun a => ((hv'.2.1 a).1.1).1, fun a => ((hv'.2.1 a).1.1).2⟩
  have hφne : ∀ v ∈ s, (φ v).Nonempty := by
    intro v _
    obtain ⟨q, hq, hqmax⟩ := isCompact_priceSimplex.exists_isMaxOn
      (priceSimplex_nonempty (ι := ι))
      ((hcost.comp (continuous_id.prodMk continuous_const)).continuousOn (s := Δ)
        (f := fun q => cost q (zf v)))
    choose y hy hymax using hPM v.1
    choose xa hxa using fun a => ((hD a).2 (v.1, W a v.1 v.2.2)).1
    exact ⟨(q, xa, y), ⟨hq, fun q' hq' => hqmax hq'⟩, hxa, fun j => ⟨hy j, hymax j⟩⟩
  have hφconv : ∀ v ∈ s, Convex ℝ (φ v) := by
    intro v _ v₁ h₁ v₂ h₂ a b ha hb hab
    refine ⟨⟨convex_priceSimplex h₁.1.1 h₂.1.1 ha hb hab, fun q hq => ?_⟩, ?_, fun j => ?_⟩
    · have e1 := h₁.1.2 q hq
      have e2 := h₂.1.2 q hq
      show cost q (zf v) ≤ cost (a • v₁.1 + b • v₂.1) (zf v)
      rw [cost_add_left, cost_smul_left, cost_smul_left]
      have := add_le_add (mul_le_mul_of_nonneg_left e1 ha) (mul_le_mul_of_nonneg_left e2 hb)
      rw [← add_mul, hab, one_mul] at this
      exact this
    · intro i
      exact ((hD i).2 _).2 (h₁.2.1 i) (h₂.2.1 i) ha hb hab
    · refine ⟨hTcv j (h₁.2.2 j).1 (h₂.2.2 j).1 ha hb hab, fun y' hy' => ?_⟩
      have e1 := (h₁.2.2 j).2 y' hy'
      have e2 := (h₂.2.2 j).2 y' hy'
      show cost v.1 y' ≤ cost v.1 (a • v₁.2.2 j + b • v₂.2.2 j)
      rw [cost_add_right, cost_smul_right, cost_smul_right]
      have := add_le_add (mul_le_mul_of_nonneg_left e1 ha) (mul_le_mul_of_nonneg_left e2 hb)
      rw [← add_mul, hab, one_mul] at this
      exact this
  have hgraph : IsClosed {pq : ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) ×
      ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) | pq.1 ∈ s ∧ pq.2 ∈ φ pq.1} := by
    have hsC : IsClosed s :=
      hΔc.prod (isClosed_Icc.prod (isClosed_set_pi fun j _ => (hTc j).isClosed))
    have hA1 : IsClosed {pq : ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) ×
        ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) | pq.2.1 ∈ Δ} :=
      hΔc.preimage (continuous_fst.comp continuous_snd)
    have hA2 : IsClosed {pq : ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) ×
        ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) |
          ∀ q ∈ Δ, cost q (zf pq.1) ≤ cost pq.2.1 (zf pq.1)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun q => isClosed_iInter fun _ =>
        isClosed_le (hcost.comp (continuous_const.prodMk (hzfc.comp continuous_fst)))
          (hcost.comp ((continuous_fst.comp continuous_snd).prodMk (hzfc.comp continuous_fst)))
    have hB : IsClosed {pq : ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) ×
        ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) |
          ∀ a, pq.2.2.1 a ∈ D a (pq.1.1, W a pq.1.1 pq.1.2.2)} := by
      simp only [ofPred_forall]
      refine isClosed_iInter fun a => ?_
      have hcont : Continuous fun pq : ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) ×
          ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) =>
            (((pq.1.1, W a pq.1.1 pq.1.2.2) : (ι → ℝ) × ℝ), pq.2.2.1 a) :=
        ((continuous_fst.comp continuous_fst).prodMk ((hWc a).comp continuous_fst)).prodMk
          ((continuous_apply a).comp ((continuous_fst.comp continuous_snd).comp continuous_snd))
      exact (hD a).1.preimage hcont
    have hC : IsClosed {pq : ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) ×
        ((ι → ℝ) × (α → ι → ℝ) × (β → ι → ℝ)) | ∀ j, pq.2.2.2 j ∈ T j ∧
          ∀ y' ∈ T j, cost pq.1.1 y' ≤ cost pq.1.1 (pq.2.2.2 j)} := by
      simp only [ofPred_forall, ofPred_and]
      refine isClosed_iInter fun j => IsClosed.inter ?_ ?_
      · exact (hTc j).isClosed.preimage ((continuous_apply j).comp
          (continuous_snd.comp (continuous_snd.comp continuous_snd)))
      · exact isClosed_iInter fun y' => isClosed_iInter fun _ =>
          isClosed_le (hcost.comp ((continuous_fst.comp continuous_fst).prodMk continuous_const))
            (hcost.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_apply j).comp
              (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
    exact (hsC.preimage continuous_fst).inter ((hA1.inter hA2).inter (hB.inter hC))
  obtain ⟨⟨p, x, y⟩, hv, hfix⟩ :=
    kakutani_fixedPoint hconv hcomp hsne hmaps hφne hφconv hgraph
  obtain ⟨⟨hpΔ, hpmax⟩, hxX, hyT⟩ := hfix
  have hp0 : 0 ≤ p := hpΔ.1
  have hp1 : ∑ i, p i = 1 := hpΔ.2
  have hx0 : ∀ a, 0 ≤ x a := fun a => hv.2.1.1 a
  -- Step 1: profits are nonnegative, so wealth is the private-ownership wealth.
  have hprof0 : ∀ j, 0 ≤ cost p (y j) := fun j => by
    have := (hyT j).2 0 (hT0 j)
    simpa [cost] using this
  have hWeq : ∀ a, W a p y = E.wealth p y a := fun a => by
    simp only [hW, wealth]
    congr 1
    exact sum_congr rfl fun j _ => by rw [max_eq_right (hprof0 j)]
  -- Step 2: wealth is at least `m a`.
  have hwge : ∀ a, m a ≤ E.wealth p y a := fun a => by
    have h1 : m a ≤ cost p (E.endow a) := by
      calc m a = ∑ i, p i * m a := by rw [← sum_mul, hp1, one_mul]
        _ ≤ ∑ i, p i * E.endow a i :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmle a i) (hp0 i)
    have h2 : 0 ≤ ∑ j, E.share a j * cost p (y j) :=
      sum_nonneg fun j _ => mul_nonneg (E.share_nonneg a j) (hprof0 j)
    simp only [wealth]; linarith
  have hxg : ∀ a, x a ∈ truncBudget c (m a) (p, E.wealth p y a) ∧
      ∀ x' ∈ truncBudget c (m a) (p, E.wealth p y a), u a x' ≤ u a (x a) := fun a => by
    have := hxX a
    rw [hWeq a] at this
    exact this
  have hbud : ∀ a, cost p (x a) ≤ E.wealth p y a := fun a => by
    have := (hxg a).1.2
    simpa [max_eq_left (hwge a)] using this
  -- Step 3: excess demand `z` has nonpositive value, hence `z ≤ 0`.
  set z := ∑ a, x a - E.totalEndowment - ∑ j, y j with hz
  have hzv : zf (p, x, y) = z := rfl
  have hcz : cost p z ≤ 0 := by
    have hsum := E.sum_wealth p y
    have : ∑ a, cost p (x a) ≤ ∑ a, E.wealth p y a := sum_le_sum fun a _ => hbud a
    rw [hz, cost_sub_right, cost_sub_right, cost_sum, cost_sum]
    rw [hsum, cost_add_right, cost_sum] at this
    linarith
  have hzle : z ≤ 0 := by
    intro i
    have hei : (Pi.single i 1 : ι → ℝ) ∈ Δ := by
      refine ⟨fun k => ?_, ?_⟩
      · by_cases h : k = i
        · subst h; simp
        · simp [h]
      · simp
    have := hpmax _ hei
    rw [hzv] at this
    have hc1 : cost (Pi.single i 1) z = z i := by
      simp [cost, Pi.single_apply]
    simp only [Pi.zero_apply]
    linarith
  -- Step 4: production is attainable, hence strictly inside the truncation.
  have hatt : -E.totalEndowment ≤ ∑ j, y j := by
    intro i
    have h1 := hzle i
    have h2 : 0 ≤ ∑ a, x a i := sum_nonneg fun a _ => hx0 a i
    simp only [hz, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] at h1
    simp only [Pi.neg_apply, Finset.sum_apply]
    linarith
  have hyR := hR y (fun j => (hyT j).1.1) hatt
  have hyj : ∀ j, ‖y j‖ < r := fun j => by
    have := (norm_le_pi_norm y j).trans hyR; linarith
  have hxc : ∀ a i, x a i < c := by
    intro a i
    have h1 := hzle i
    simp only [hz, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] at h1
    have h2 : x a i ≤ ∑ a, x a i :=
      single_le_sum (f := fun a => x a i) (fun a _ => hx0 a i) (mem_univ a)
    have h3 : E.totalEndowment i ≤ ∑ k, E.totalEndowment k :=
      single_le_sum (f := fun k => E.totalEndowment k) (fun k _ => hω0 k) (mem_univ i)
    have h4 : ∑ j, y j i ≤ Fintype.card β * R := by
      calc ∑ j, y j i ≤ ∑ _j : β, R := sum_le_sum fun j _ => by
            have := (norm_le_pi_norm (y j) i).trans ((norm_le_pi_norm y j).trans hyR)
            rw [Real.norm_eq_abs] at this
            exact (le_abs_self _).trans this
        _ = Fintype.card β * R := by simp
    rw [hc]; linarith
  -- Step 5: firms maximize profit on the whole `Yⱼ` (convexity).
  have hprofit : ∀ j, ProfitMax p (E.prod j) (y j) := by
    intro j
    refine ⟨(hyT j).1.1, fun z' hz' => ?_⟩
    by_contra hlt
    push Not at hlt
    have hpath : Tendsto (fun t : ℝ => y j + t • (z' - y j)) (𝓝[>] 0) (𝓝 (y j)) := by
      have : Continuous fun t : ℝ => y j + t • (z' - y j) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
    obtain ⟨t, ⟨htB, ht1⟩, ht0⟩ := (((hpath.eventually (Metric.isOpen_ball.mem_nhds
      (mem_ball_zero_iff.2 (hyj j)))).and hlt1).and self_mem_nhdsWithin).exists
    have ht0' : (0 : ℝ) < t := ht0
    have hw : y j + t • (z' - y j) ∈ T j :=
      ⟨(hYcv j).add_smul_sub_mem (hyT j).1.1 hz' ⟨ht0'.le, ht1.le⟩, Metric.ball_subset_closedBall htB⟩
    have := (hyT j).2 _ hw
    rw [cost_add_right, cost_smul_right, cost_sub_right] at this
    have : 0 < t * (cost p z' - cost p (y j)) := mul_pos ht0' (by linarith)
    linarith
  -- Step 6: consumers maximize on their whole budget sets (quasiconcavity and
  -- strong monotonicity).
  have hdem : ∀ a, x a ∈ demand (prefOf (u a)) p (E.wealth p y a) := by
    intro a
    refine ⟨⟨hx0 a, hbud a⟩, fun x' hx' => ?_⟩
    show u a x' ≤ u a (x a)
    by_contra hlt
    push Not at hlt
    set Wa := E.wealth p y a with hWa
    have hWpos : 0 < Wa := (hm0 a).trans_le (hwge a)
    -- A strictly better bundle `x''` that leaves money unspent.
    have hshrink : Tendsto (fun s : ℝ => s • x') (𝓝[<] 1) (𝓝 x') := by
      have : Continuous fun s : ℝ => s • x' := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
    have hev1 : ∀ᶠ s in 𝓝[<] (1 : ℝ), u a (x a) < u a (s • x') :=
      (((hu a).tendsto x').comp hshrink).eventually (lt_mem_nhds hlt)
    obtain ⟨σ, hσu, hσ0, hσ1⟩ := (hev1.and (Ioo_mem_nhdsLT zero_lt_one)).exists
    set x'' := σ • x' with hx''
    have hx''0 : 0 ≤ x'' := smul_nonneg hσ0.le hx'.1
    have hc'' : cost p x'' < Wa := by
      have h1 : cost p x' ≤ Wa := hx'.2
      rw [hx'', cost_smul_right]
      rcases le_or_gt (cost p x') 0 with h | h
      · nlinarith
      · nlinarith
    have hsp : 0 ≤ ∑ i, p i := sum_nonneg fun i _ => hp0 i
    set δ := (Wa - cost p x'') / (∑ i, p i + 1) with hδdef
    have hδ : 0 < δ := div_pos (by linarith) (by linarith)
    have hδ' : δ * ∑ i, p i ≤ Wa - cost p x'' := by
      have h1 : δ * (∑ i, p i + 1) = Wa - cost p x'' := div_mul_cancel₀ _ (by linarith)
      nlinarith
    set one : ι → ℝ := fun _ => 1 with hone
    have hcone : cost p one = ∑ i, p i := by simp [cost, one]
    -- Mix `x''` into `x a` (quasiconcavity: no worse), then add a little of
    -- every good (strong monotonicity: strictly better), staying affordable.
    set v : ℝ → ι → ℝ := fun t => t • x'' + (1 - t) • x a + (t * δ) • one with hv
    have hvc : Continuous v := by fun_prop
    have hpath : Tendsto v (𝓝[>] 0) (𝓝 (x a)) := by
      simpa [v] using (hvc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hopen : IsOpen {w : ι → ℝ | ∀ i, w i < c} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
    have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
    obtain ⟨t, ⟨htc, ht1⟩, ht0⟩ := (((hpath.eventually (hopen.mem_nhds (hxc a))).and hlt1).and
      self_mem_nhdsWithin).exists
    have ht0' : (0 : ℝ) < t := ht0
    have htc' : ∀ i, v t i < c := htc
    set w := t • x'' + (1 - t) • x a with hw
    have hw0 : 0 ≤ w :=
      add_nonneg (smul_nonneg ht0'.le hx''0) (smul_nonneg (by linarith) (hx0 a))
    have huw : u a (x a) ≤ u a w :=
      ((hqc a) (u a (x a)) ⟨hx''0, hσu.le⟩ ⟨hx0 a, le_rfl⟩ ht0'.le (by linarith)
        (by ring)).2
    have hvw : v t = w + (t * δ) • one := rfl
    have hbump : 0 ≤ (t * δ) • one := smul_nonneg (by positivity) fun _ => zero_le_one
    have hwv : w ≤ v t := by rw [hvw]; exact le_add_of_nonneg_right hbump
    have hne : w ≠ v t := by
      intro h
      obtain ⟨i⟩ := ‹Nonempty ι›
      have e := congrFun h i
      rw [hvw] at e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one, mul_one] at e
      have : 0 < t * δ := mul_pos ht0' hδ
      linarith
    have hlt2 : u a w < u a (v t) := lt_of_not_ge (hmono a w (v t) hw0 hwv hne).2
    have hmemT : v t ∈ truncBudget c (m a) (p, Wa) := by
      refine ⟨⟨hw0.trans hwv, fun i => (htc' i).le⟩, ?_⟩
      show cost p (v t) ≤ max Wa (m a)
      rw [max_eq_left (hwge a)]
      simp only [v, cost_add_right, cost_smul_right, hcone]
      have h2 := hbud a
      have k1 : t * (cost p x'' + δ * ∑ i, p i) ≤ t * Wa :=
        mul_le_mul_of_nonneg_left (by linarith) ht0'.le
      have k2 : (1 - t) * cost p (x a) ≤ (1 - t) * Wa :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith
    have hle := (hxg a).2 _ hmemT
    linarith
  -- Step 7: budgets bind and prices are strictly positive (strong monotonicity).
  have hwal : ∀ a, cost p (x a) = E.wealth p y a := fun a =>
    walras_law (hmono a).locallyNonsatiated (hdem a)
  have hpos : PositivePrices p := by
    intro i
    rcases (hp0 i).lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨a⟩ := ‹Nonempty α›
    set x' := x a + Pi.single i 1 with hx'
    have hsingle : (0 : ι → ℝ) ≤ Pi.single i 1 := fun k => by
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    have hle : x a ≤ x' := le_add_of_nonneg_right hsingle
    have hne : x a ≠ x' := fun h' => by
      have := congrFun h' i
      simp [x'] at this
    have hP := hmono a (x a) x' (hx0 a) hle hne
    have hx'B : x' ∈ budgetSet p (E.wealth p y a) := by
      refine ⟨(hx0 a).trans hle, ?_⟩
      have : cost p x' = cost p (x a) := by
        rw [hx', cost_add_right]
        simp [cost, Pi.single_apply, ← h]
      rw [this]; exact hbud a
    exact hP.2 ((hdem a).2 x' hx'B)
  -- Step 8: markets clear.
  have hcz0 : cost p z = 0 := by
    have hsum := E.sum_wealth p y
    have : ∑ a, cost p (x a) = ∑ a, E.wealth p y a := sum_congr rfl fun a _ => hwal a
    rw [hz, cost_sub_right, cost_sub_right, cost_sum, cost_sum]
    rw [hsum, cost_add_right, cost_sum] at this
    linarith
  have hz0 : z = 0 := by
    have hterms : ∀ i ∈ (univ : Finset ι), p i * z i ≤ 0 := fun i _ => by
      have := hzle i
      simp only [Pi.zero_apply] at this
      nlinarith [(hpos i).le]
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hterms).1 hcz0
    funext i
    rcases mul_eq_zero.1 (hall i (mem_univ i)) with h' | h'
    · exact absurd h' (hpos i).ne'
    · exact h'
  refine ⟨p, x, y, hpos, hprofit, fun a => by rw [hpref a]; exact hdem a, ?_⟩
  funext i
  have h := congrFun hz0 i
  simp only [hz, Pi.sub_apply, Pi.zero_apply, Finset.sum_apply] at h
  simp only [Pi.add_apply, Finset.sum_apply]
  linarith

/-- **Arrow–Debreu existence, strictly convex preferences** (the special case
with strictly quasiconcave utilities). -/
theorem exists_walrasianEquilibrium_arrowDebreu [Nonempty ι] [Nonempty α]
    (E : ProductionEconomy α β ι) {u : α → (ι → ℝ) → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u a)) (hu : ∀ a, Continuous (u a))
    (hsq : ∀ a, StrictlyQuasiconcave (u a)) (hmono : ∀ a, StronglyMonotone (prefOf (u a)))
    (hωa : ∀ a, PositivePrices (E.endow a))
    (hY0 : ∀ j, (0 : ι → ℝ) ∈ E.prod j) (hYcl : ∀ j, IsClosed (E.prod j))
    (hYcv : ∀ j, Convex ℝ (E.prod j)) (hnfl : NoFreeLunch E.aggProd)
    (hirr : Irreversible E.aggProd) :
    ∃ p x y, PositivePrices p ∧ E.IsWalrasianEquilibrium p x y :=
  E.exists_walrasianEquilibrium_arrowDebreu_convex hpref hu (fun a => (hsq a).quasiconcaveOn)
    hmono hωa hY0 hYcl hYcv hnfl hirr

end ProductionEconomy

namespace GEExamples

/-- A **constant-returns, free-disposal** technology: good 0 is converted one
for one into good 1, and goods can be thrown away. A closed convex cone. -/
def linearSet : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 0 + y 1 ≤ 0}

theorem zero_mem_linearSet : (0 : Fin 2 → ℝ) ∈ linearSet := by
  simp [linearSet]

theorem isClosed_linearSet : IsClosed linearSet :=
  show IsClosed ({y : Fin 2 → ℝ | y 0 ≤ 0} ∩ {y | y 0 + y 1 ≤ 0}) from
  (isClosed_le (continuous_apply 0) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem convex_linearSet : Convex ℝ linearSet := by
  intro x hx y hy a b ha hb hab
  simp only [linearSet, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

/-- Constant returns: `linearSet` is closed under nonnegative scaling. -/
theorem smul_mem_linearSet {y : Fin 2 → ℝ} (hy : y ∈ linearSet) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ linearSet := by
  simp only [linearSet, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hy ⊢
  constructor <;> nlinarith [hy.1, hy.2]

/-- Free disposal: anything below a feasible plan is feasible. -/
theorem freeDisposal_linearSet : FreeDisposal linearSet := by
  intro y hy y' hle
  simp only [linearSet, mem_ofPred_eq] at hy ⊢
  have h0 := hle 0
  have h1 := hle 1
  constructor <;> linarith [hy.1, hy.2]

theorem noFreeLunch_linearSet {y : Fin 2 → ℝ} (hy : y ∈ linearSet) (h0 : 0 ≤ y) : y = 0 := by
  simp only [linearSet, mem_ofPred_eq] at hy
  have a := h0 0
  have b := h0 1
  simp only [Pi.zero_apply] at a b
  have e0 : y 0 = 0 := by linarith [hy.1]
  have e1 : y 1 = 0 := by linarith [hy.2]
  funext i; fin_cases i <;> simp [e0, e1]

theorem irreversible_linearSet {y : Fin 2 → ℝ} (hy : y ∈ linearSet) (hny : -y ∈ linearSet) :
    y = 0 := by
  simp only [linearSet, mem_ofPred_eq, Pi.neg_apply] at hy hny
  have e0 : y 0 = 0 := by linarith [hy.1, hny.1]
  have e1 : y 1 = 0 := by linarith [hy.2, hny.2]
  funext i; fin_cases i <;> simp [e0, e1]

/-- `linearSet` is **not strictly convex** (it has flat faces), so the
strictly convex theorem of `GE/ExistenceUnbounded.lean` does not apply. -/
theorem linearSet_not_strictConvex : ¬ StrictConvex ℝ linearSet := by
  intro h
  have h1 : (![0, -1] : Fin 2 → ℝ) ∈ linearSet := by simp [linearSet]
  have hne : (0 : Fin 2 → ℝ) ≠ ![0, -1] := fun h' => by
    have := congrFun h' 1; simp at this
  have hm := h zero_mem_linearSet h1 hne (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  set m : Fin 2 → ℝ := (1 / 2 : ℝ) • (0 : Fin 2 → ℝ) + (1 / 2 : ℝ) • ![0, -1]
  have hcont : Continuous fun t : ℝ => m + t • (Pi.single 0 1 : Fin 2 → ℝ) := by fun_prop
  have hpath : Tendsto (fun t : ℝ => m + t • (Pi.single 0 1 : Fin 2 → ℝ)) (𝓝[>] 0) (𝓝 m) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, htY, ht0⟩ := ((hpath.eventually (mem_interior_iff_mem_nhds.1 hm)).and
    self_mem_nhdsWithin).exists
  have ht0' : (0 : ℝ) < t := ht0
  have := htY.1
  simp [m] at this
  linarith

/-- Witness economy: two square-root consumers each owning `(1, 1)`, consumer
`0` owning the one firm, whose technology `linearSet` has constant returns and
free disposal. -/
noncomputable def linearEconomy : ProductionEconomy (Fin 2) (Fin 1) (Fin 2) where
  pref _ := prefOf uSqrt
  endow _ := fun _ => 1
  endow_nonneg _ _ := by norm_num
  prod _ := linearSet
  share a _ := if a = 0 then 1 else 0
  share_nonneg a _ := by split_ifs <;> norm_num
  share_sum _ := by simp

theorem linearEconomy_aggProd : linearEconomy.aggProd = linearSet := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [linearEconomy] using hy 0
  · intro hz
    exact ⟨fun _ => z, fun _ => hz, by simp⟩

/-- **Existence with constant returns and free disposal.** (Only existence is
claimed.) -/
theorem linearEconomy_exists_equilibrium :
    ∃ p x y, PositivePrices p ∧ linearEconomy.IsWalrasianEquilibrium p x y := by
  refine linearEconomy.exists_walrasianEquilibrium_arrowDebreu (u := fun _ => uSqrt)
    (fun _ => rfl) (fun _ => continuous_uSqrt) (fun _ => strictlyQuasiconcave_uSqrt)
    (fun _ => stronglyMonotone_uSqrt) (fun _ _ => by simp [linearEconomy])
    (fun _ => zero_mem_linearSet) (fun _ => isClosed_linearSet) (fun _ => convex_linearSet) ?_ ?_
  · rw [linearEconomy_aggProd]; exact fun y hy h0 => noFreeLunch_linearSet hy h0
  · rw [linearEconomy_aggProd]; exact fun y hy hny => irreversible_linearSet hy hny

/-- **Perfect substitutes** `uLin x = x₀ + x₁` (from `GE/Examples.lean`) are
convex but not strictly convex preferences, so demand is set-valued when
`p₀ = p₁`. -/
theorem quasiconcaveOn_uLin : QuasiconcaveOn ℝ (Ici 0) uLin := by
  intro r x hx y hy a b ha hb hab
  refine ⟨(convex_Ici (0 : Fin 2 → ℝ)) hx.1 hy.1 ha hb hab, ?_⟩
  have h1 : r ≤ uLin x := hx.2
  have h2 : r ≤ uLin y := hy.2
  have k := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  rw [← add_mul, hab, one_mul] at k
  show r ≤ uLin (a • x + b • y)
  simp only [uLin, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at k ⊢
  linarith

theorem not_strictlyQuasiconcave_uLin : ¬ StrictlyQuasiconcave uLin := by
  intro h
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := fun h' => by
    have := congrFun h' 0; simp at this
  have := h ![1, 0] ![0, 1] (fun i => by fin_cases i <;> simp)
    (fun i => by fin_cases i <;> simp) hne (1 / 2) (by norm_num) (by norm_num)
  simp [uLin] at this

/-- No utility representing perfect-substitutes preferences is strictly
quasiconcave, so the strictly convex theorem cannot be applied to `substEconomy`
by changing the utility representation. -/
theorem not_strictlyQuasiconcave_of_prefOf_eq_uLin (v : (Fin 2 → ℝ) → ℝ)
    (hv : prefOf v = prefOf uLin) : ¬ StrictlyQuasiconcave v := by
  intro h
  have key : ∀ x y, v y ≤ v x ↔ uLin y ≤ uLin x := fun x y => by
    have := congrFun (congrFun hv x) y
    exact Iff.of_eq this
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := fun h' => by
    have := congrFun h' 0; simp at this
  have hs := h ![1, 0] ![0, 1] (fun i => by fin_cases i <;> simp)
    (fun i => by fin_cases i <;> simp) hne (1 / 2) (by norm_num) (by norm_num)
  set mid : Fin 2 → ℝ := (1 / 2 : ℝ) • ![1, 0] + (1 - 1 / 2 : ℝ) • ![0, 1]
  have h1 : v mid ≤ v ![1, 0] := (key _ _).2 (by simp [mid, uLin])
  have h2 : v mid ≤ v ![0, 1] := (key _ _).2 (by simp [mid, uLin])
  exact absurd hs (not_lt.2 (le_min h1 h2))

theorem stronglyMonotone_uLin : StronglyMonotone (prefOf uLin) := by
  intro x y _ hxy hne
  have hlt : uLin x < uLin y := by
    simp only [uLin]
    by_cases h0 : x 0 = y 0
    · have h1 : x 1 < y 1 := lt_of_le_of_ne (hxy 1) fun h1 => hne (by
        funext i; fin_cases i
        · exact h0
        · exact h1)
      linarith [hxy 0]
    · linarith [lt_of_le_of_ne (hxy 0) h0, hxy 1]
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- Witness economy with **convex, not strictly convex** preferences: two
perfect-substitutes consumers each owning `(1, 1)`, consumer `0` owning the
constant-returns, free-disposal firm `linearSet`. -/
noncomputable def substEconomy : ProductionEconomy (Fin 2) (Fin 1) (Fin 2) where
  pref _ := prefOf uLin
  endow _ := fun _ => 1
  endow_nonneg _ _ := by norm_num
  prod _ := linearSet
  share a _ := if a = 0 then 1 else 0
  share_nonneg a _ := by split_ifs <;> norm_num
  share_sum _ := by simp

theorem substEconomy_aggProd : substEconomy.aggProd = linearSet := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [substEconomy] using hy 0
  · intro hz
    exact ⟨fun _ => z, fun _ => hz, by simp⟩

/-- **Existence with perfect substitutes and constant returns.** (Only
existence is claimed.) -/
theorem substEconomy_exists_equilibrium :
    ∃ p x y, PositivePrices p ∧ substEconomy.IsWalrasianEquilibrium p x y := by
  refine substEconomy.exists_walrasianEquilibrium_arrowDebreu_convex (u := fun _ => uLin)
    (fun _ => rfl) (fun _ => continuous_uLin) (fun _ => quasiconcaveOn_uLin)
    (fun _ => stronglyMonotone_uLin) (fun _ _ => by simp [substEconomy])
    (fun _ => zero_mem_linearSet) (fun _ => isClosed_linearSet) (fun _ => convex_linearSet) ?_ ?_
  · rw [substEconomy_aggProd]; exact fun y hy h0 => noFreeLunch_linearSet hy h0
  · rw [substEconomy_aggProd]; exact fun y hy hny => irreversible_linearSet hy hny

end GEExamples

end Econ
