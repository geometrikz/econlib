/-
# Aiyagari: savings policies and stationary wealth continuous in the interest rate; equilibrium existence

Aiyagari (1994); Ljungqvist–Sargent (LS) ch. 18; Stokey–Lucas (SL) Thm 12.13;
Açıkgöz (2018) for the existence argument.

**Parametrized savings problem** (`ParamSavings`). A household holds assets
`a ∈ [0, k̄]` and has an exogenous Markov state `z` (income). Cash on hand is
`h(θ, a, z)`, where the parameter `θ` collects the prices the household takes
as given. In Aiyagari's model `θ = r` and `h(r, a, z) = (1 + r) a + w(r) e(z)`.
It solves

  `v_θ(a, z) = max_{0 ≤ a' ≤ min(k̄, h(θ, a, z))} u(h(θ, a, z) - a') + β Σ_{z'} Q(z, z') v_θ(a', z')`.

For each fixed `θ` this is a `StochSavings` problem (`slice θ`).

**Results.**
* `exists_joint_policy`: the optimal savings rule `a' = g(θ, a, z)` is unique
  and **jointly continuous in the price and the state**. The proof treats `θ`
  as a frozen state variable: the augmented problem on `(θ, a)` with feasible
  set `{θ} × [0, h]` is an ordinary stochastic DP. Its value and policy restrict
  to those of each slice (uniqueness of the Bellman solution), and Berge's
  theorem gives joint continuity.
* `isJointlyFeller_policyKernel`: the induced Markov kernels on `(a, z)` form
  a jointly Feller family.
* `continuous_aggregate`: if each price gives a **unique** stationary
  distribution `π_θ` (for example under Doeblin's condition,
  `Econ.unique_invariant_of_pow`), then `θ ↦ π_θ` is weakly continuous and
  **aggregate asset supply** `K_s(θ) = ∫ a dπ_θ` is continuous (SL 12.13).
* `exists_asset_market_clearing`: **asset-market clearing** on a price interval
  `[r_lo, r_hi]`, *without* assuming uniqueness (as in Açıkgöz 2018). Take a
  continuous capital-demand curve `K_d` with `K_d(r_lo) ≥ k̄` (true for
  Cobb–Douglas demand `K_d(r) = L (α / (r + δ))^{1/(1-α)}` as `r ↓ -δ`) and
  `K_d(r_hi) ≤ ∫ a dμ` for some stationary `μ` at `r_hi`. Then some `r` and
  some stationary `π` at `r` clear the market: `∫ a dπ = K_d(r)`. The proof
  uses the closed graph of the stationary-distribution correspondence and
  mixes two stationary distributions.

**What is and is not formalized (documented gaps).**
* *Partial equilibrium in the asset market.* `K_d` is any continuous demand
  curve; the firm's problem, the wage `w(r)` and labor-market clearing are not
  linked to `h`. A full Aiyagari general equilibrium would derive `K_d` and
  `w` from a production function.
* *Uniqueness of the stationary distribution* is needed only for continuity of
  `θ ↦ π_θ` (`continuous_aggregate`, hypothesis `huniq`). From primitives it
  follows from monotone mixing (Hopenhayn–Prescott 1992) or an `N`-step
  Doeblin minorization; deriving either from `u`, `Q`, `h` is not done.
* *The upper boundary condition* `K_d(r_hi) ≤ K_s(r_hi)`. In Aiyagari it holds
  as `r ↑ 1/β - 1`, because asset supply diverges there (Chamberlain–Wilson);
  that limit argument is not formalized.
* *The exogenous asset cap* `k̄`. It is imposed, not derived. The endogenous
  bound (`a' < a` for large `a` when `β(1 + r) < 1`) is not formalized. If the
  cap binds, an equilibrium of the capped economy need not be one of the
  uncapped economy (for instance at an `r` with `β(1 + r) ≥ 1`).

**Non-vacuity.** `aiyagariFamily` (saving earns `r`) satisfies the hypotheses
of `exists_joint_policy` and `exists_asset_market_clearing`. `noReturn` (saving earns
nothing) is a model where uniqueness holds: the optimal policy is `a' = 0`, the
kernel is constant, and Doeblin holds with `ε = 1`. Its stationary
distribution puts all assets at `0`.
-/
module

public import EconLean.Macro.HA.StochSavings
public import EconLean.Macro.DP.ParamInvariant
public import EconLean.Macro.DP.Doeblin

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

/-- A **savings problem parametrized by prices** `θ` (e.g. the interest rate):
`StochSavings` with cash on hand `h θ a z` jointly continuous in `(θ, a)`. -/
structure ParamSavings (Θ Z : Type*) [TopologicalSpace Θ] [Fintype Z] where
  u : ℝ → ℝ
  h : Θ → ℝ → Z → ℝ
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
  h_continuous : ∀ z, Continuous fun p : Θ × ℝ => h p.1 p.2 z
  h_nonneg : ∀ θ z k, 0 ≤ k → 0 ≤ h θ k z
  h_concave : ∀ θ z, ConcaveOn ℝ (Ici 0) fun k => h θ k z

namespace ParamSavings

variable {Θ Z : Type*} [TopologicalSpace Θ] [Fintype Z] [TopologicalSpace Z] [DiscreteTopology Z]
  (M : ParamSavings Θ Z)

/-- The savings problem at the fixed price `θ`. -/
abbrev slice (θ : Θ) : StochSavings Z where
  u := M.u
  h := M.h θ
  Q := M.Q
  β := M.β
  kbar := M.kbar
  Q_nonneg := M.Q_nonneg
  Q_sum := M.Q_sum
  β_pos := M.β_pos
  β_lt_one := M.β_lt_one
  kbar_pos := M.kbar_pos
  u_continuous := M.u_continuous
  u_mono := M.u_mono
  u_strictConcave := M.u_strictConcave
  h_continuous := fun z => (M.h_continuous z).comp (continuous_const.prodMk continuous_id)
  h_nonneg := M.h_nonneg θ
  h_concave := M.h_concave θ

/-- The asset space `[0, k̄]`, common to all prices. -/
abbrev S : Set ℝ := Icc 0 M.kbar

theorem continuous_hS : Continuous fun s : (Θ × M.S) × Z => M.h s.1.1 s.1.2 s.2 :=
  continuous_prod_of_discrete_right.2 fun z =>
    (M.h_continuous z).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Feasible choices in the augmented problem: the price is frozen,
`θ' = θ`, and `0 ≤ a' ≤ min(k̄, h(θ, a, z))`. -/
def augΓ (s : (Θ × M.S) × Z) : Set (Θ × M.S) := {p | p.1 = s.1.1 ∧ (p.2 : ℝ) ≤ M.h s.1.1 s.1.2 s.2}

/-- Return in the augmented problem. -/
def augF (s : (Θ × M.S) × Z) (p : Θ × M.S) : ℝ := M.u (M.h s.1.1 s.1.2 s.2 - p.2)

theorem augΓ_isClosed_graph [T2Space Θ] : IsClosed (graph M.augΓ) :=
  (isClosed_eq (continuous_fst.comp continuous_snd)
    (continuous_fst.comp (continuous_fst.comp continuous_fst))).inter
    (isClosed_le (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
      (M.continuous_hS.comp continuous_fst))

theorem augΓ_lhc : LowerHemicontinuous M.augΓ := by
  refine fun s => lowerHemicontinuousAt_iff_textbook.2 ?_
  rintro U hU ⟨y, hyΓ, hyU⟩
  let g : (Θ × M.S) × Z → Θ × M.S := fun s' => (s'.1.1, ⟨min (y.2 : ℝ) (M.h s'.1.1 s'.1.2 s'.2),
    le_min y.2.2.1 (M.h_nonneg _ _ _ s'.1.2.2.1), (min_le_left _ _).trans y.2.2.2⟩)
  have hc : Continuous g :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_const.min M.continuous_hS).subtype_mk _)
  have hs : g s = y := Prod.ext hyΓ.1.symm (Subtype.ext (min_eq_left hyΓ.2))
  filter_upwards [(hc.tendsto s).eventually (hU.mem_nhds (hs ▸ hyU))] with s' hs'
  exact ⟨g s', ⟨rfl, min_le_right _ _⟩, hs'⟩

variable [CompactSpace Θ] [T2Space Θ]

/-- The **augmented problem**: the price is a state variable that never
changes. It is an ordinary stochastic dynamic program on `(θ, a)`. -/
noncomputable def aug : StochDynProg (Θ × M.S) Z where
  Γ := M.augΓ
  F := M.augF
  Q := M.Q
  β := M.β
  Q_nonneg := M.Q_nonneg
  Q_sum := M.Q_sum
  β_pos := M.β_pos
  β_lt_one := M.β_lt_one
  Γ_nonempty := fun s => ⟨(s.1.1, ⟨0, le_rfl, M.kbar_pos.le⟩), rfl, M.h_nonneg _ _ _ s.1.2.2.1⟩
  Γ_compact := fun s => (isClosed_of_isClosed_graph M.augΓ_isClosed_graph s).isCompact
  Γ_continuous := ⟨upperHemicontinuous_of_isClosed_graph M.augΓ_isClosed_graph, M.augΓ_lhc⟩
  F_continuous := M.u_continuous.comp
    ((M.continuous_hS.comp continuous_fst).sub
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  F_bounded := by
    obtain ⟨H, hH⟩ := (isCompact_univ.image M.continuous_hS).isBounded.subset_closedBall 0
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (M.u_continuous.continuousOn (s := Icc 0 H))
    refine ⟨C, fun s y hy => ?_⟩
    have hy' : (y.2 : ℝ) ≤ M.h s.1.1 s.1.2 s.2 := hy.2
    have hHs : M.h s.1.1 s.1.2 s.2 ≤ H := by
      have := hH ⟨s, trivial, rfl⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans this
    have := hC (M.h s.1.1 s.1.2 s.2 - y.2) ⟨sub_nonneg.2 hy', by linarith [y.2.2.1]⟩
    rw [Real.norm_eq_abs] at this
    exact this

/-- **The augmented value restricts to each slice's value** (uniqueness of the
bounded continuous Bellman solution). -/
theorem value_slice (θ : Θ) (k : M.S) (z : Z) :
    M.aug.value ((θ, k), z) = (M.slice θ).toStochDynProg.value (k, z) := by
  let e : C(M.S × Z, (Θ × M.S) × Z) :=
    ⟨fun s => ((θ, s.1), s.2), (continuous_const.prodMk continuous_fst).prodMk continuous_snd⟩
  let w : M.S × Z →ᵇ ℝ := M.aug.value.compContinuous e
  have hw : w = (M.slice θ).toStochDynProg.value := by
    refine (M.slice θ).toStochDynProg.value_unique w fun s => ?_
    have hb := M.aug.bellman_equation ((θ, s.1), s.2)
    have hset : (fun y => (M.slice θ).toStochDynProg.F s y + (M.slice θ).toStochDynProg.β *
        ∑ z', (M.slice θ).toStochDynProg.Q s.2 z' * w (y, z')) '' (M.slice θ).toStochDynProg.Γ s =
        (fun p => M.aug.F ((θ, s.1), s.2) p + M.aug.β *
          ∑ z', M.aug.Q (((θ, s.1), s.2) : (Θ × M.S) × Z).2 z' * M.aug.value (p, z')) ''
          M.aug.Γ ((θ, s.1), s.2) := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(θ, y), ⟨rfl, hy⟩, rfl⟩
      · rintro ⟨⟨θ', y⟩, ⟨h1, h2⟩, rfl⟩
        obtain rfl : θ' = θ := h1
        exact ⟨y, h2, rfl⟩
    rw [hset]
    exact hb
  rw [← hw]
  rfl

theorem objective_slice (θ : Θ) (k y : M.S) (z : Z) :
    M.aug.objective M.aug.value ((θ, k), z) (θ, y) =
      (M.slice θ).toStochDynProg.objective (M.slice θ).toStochDynProg.value (k, z) y := by
  simp only [StochDynProg.objective, StochDynProg.expect]
  congr 2
  refine Finset.sum_congr rfl fun z' _ => ?_
  rw [M.value_slice]
  rfl

/-- **The augmented policy restricts to each slice's policy.** -/
theorem policy_slice (θ : Θ) (k : M.S) (z : Z) :
    M.aug.policy ((θ, k), z) = (fun y => (θ, y)) '' (M.slice θ).toStochDynProg.policy (k, z) := by
  ext ⟨θ', y⟩
  constructor
  · rintro ⟨⟨h1, h2⟩, hopt⟩
    obtain rfl : θ' = θ := h1
    refine ⟨y, ⟨h2, fun y' hy' => ?_⟩, rfl⟩
    have := hopt (θ', y') ⟨rfl, hy'⟩
    rwa [M.objective_slice, M.objective_slice] at this
  · rintro ⟨y', ⟨hy'Γ, hopt⟩, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨⟨rfl, hy'Γ⟩, fun ⟨θ'', y''⟩ ⟨h1, h2⟩ => ?_⟩
    obtain rfl : θ'' = θ := h1
    rw [M.objective_slice, M.objective_slice]
    exact hopt y'' h2

/-- **Savings policies are jointly continuous in prices and the state.** For
each price `θ` the optimal savings rule `g θ` is unique (`StochSavings`), and
`(θ, a, z) ↦ g θ (a, z)` is jointly continuous. -/
theorem exists_joint_policy :
    ∃ g : Θ → M.S × Z → M.S, Continuous (fun p : (Θ × M.S) × Z => g p.1.1 (p.1.2, p.2)) ∧
      ∀ θ s, (M.slice θ).toStochDynProg.policy s = {g θ s} := by
  have hpol := fun θ : Θ => (M.slice θ).toStochDynProg.exists_continuous_policy
    (convex_Icc 0 M.kbar) (M.slice θ).convexTech (M.slice θ).concaveRet
  choose g _ hg using hpol
  refine ⟨g, ?_, hg⟩
  have hG : ∀ s : (Θ × M.S) × Z, argmax (M.aug.objective M.aug.value) M.aug.Γ s =
      {(s.1.1, g s.1.1 (s.1.2, s.2))} := by
    rintro ⟨⟨θ, k⟩, z⟩
    show M.aug.policy ((θ, k), z) = _
    rw [M.policy_slice, hg, image_singleton]
  have := continuous_of_argmax_eq_singleton (M.aug.continuous_objective _) M.aug.Γ_continuous
    M.aug.Γ_nonempty M.aug.Γ_compact hG
  exact continuous_snd.comp this

variable [MeasurableSpace Z] [BorelSpace Z]

omit [CompactSpace Θ] [T2Space Θ] in
/-- The policy kernels `κ_θ((a, z), ·) = Σ_{z'} Q(z, z') δ_{(g(θ, a, z), z')}` of a
jointly continuous policy form a **jointly Feller** family. -/
theorem isJointlyFeller_policyKernel (g : Θ → M.S × Z → M.S)
    (hgc : Continuous (fun p : (Θ × M.S) × Z => g p.1.1 (p.1.2, p.2)))
    (hgm : ∀ θ, Measurable (g θ)) :
    IsJointlyFeller fun θ => policyKernel M.Q (g θ) (hgm θ) := by
  intro f
  simp_rw [integral_policyKernel M.Q_nonneg]
  have hg' : Continuous fun p : Θ × (M.S × Z) => g p.1 p.2 :=
    hgc.comp ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))
  exact continuous_finsetSum _ fun z' _ =>
    ((continuous_of_discreteTopology (f := fun z => M.Q z z')).comp
      (continuous_snd.comp continuous_snd)).mul
      (f.continuous.comp (hg'.prodMk continuous_const))

/-- Assets held, as a bounded continuous function on `[0, k̄] × Z`. -/
noncomputable def assets : M.S × Z →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun s => (s.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩

omit [CompactSpace Θ] [T2Space Θ] in
/-- At every price the optimal policy's chain has a stationary distribution. -/
theorem exists_stationary_of_policy [Nonempty Z] (θ : Θ) (g : M.S × Z → M.S) (hg : Measurable g)
    (hpol : ∀ s, (M.slice θ).toStochDynProg.policy s = {g s}) :
    ∃ μ : ProbabilityMeasure (M.S × Z), Kernel.Invariant (policyKernel M.Q g hg) μ := by
  obtain ⟨g', hg'c, hg', -⟩ := (M.slice θ).exists_stationary
  have : g = g' := funext fun s => Set.singleton_eq_singleton_iff.1 ((hpol s).symm.trans (hg' s))
  subst this
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  have : Nonempty M.S := ⟨⟨0, le_rfl, M.kbar_pos.le⟩⟩
  have := isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum g hg
  obtain ⟨μ, hμ, hinv⟩ := exists_invariant_of_feller (policyKernel M.Q g hg)
    (isFeller_policyKernel M.Q_nonneg hg'c hg)
  exact ⟨⟨μ, hμ⟩, hinv⟩

/-- The **uniqueness hypothesis**: at price `θ`, the optimal policy's Markov
chain on `(a, z)` has at most one stationary distribution. -/
def UniqueStationary (θ : Θ) : Prop :=
  ∀ (g : M.S × Z → M.S) (hg : Measurable g), (∀ s, (M.slice θ).toStochDynProg.policy s = {g s}) →
    ∀ μ ν : ProbabilityMeasure (M.S × Z), Kernel.Invariant (policyKernel M.Q g hg) μ →
      Kernel.Invariant (policyKernel M.Q g hg) ν → μ = ν

/-- **Aggregate asset supply is continuous in prices** (SL Thm 12.13 applied to
Aiyagari). If the stationary distribution is unique at every price, then the
stationary distribution `π_θ` and aggregate assets `K_s(θ) = ∫ a dπ_θ` are
continuous in `θ`. -/
theorem continuous_aggregate [Nonempty Z] (huniq : ∀ θ, M.UniqueStationary θ) :
    ∃ (g : Θ → M.S × Z → M.S) (hgm : ∀ θ, Measurable (g θ)) (π : Θ → ProbabilityMeasure (M.S × Z)),
      Continuous (fun p : (Θ × M.S) × Z => g p.1.1 (p.1.2, p.2)) ∧
      (∀ θ s, (M.slice θ).toStochDynProg.policy s = {g θ s}) ∧
      (∀ θ, Kernel.Invariant (policyKernel M.Q (g θ) (hgm θ)) (π θ)) ∧
      Continuous π ∧ Continuous fun θ => ∫ s, M.assets s ∂(π θ : Measure (M.S × Z)) := by
  obtain ⟨g, hgc, hg⟩ := M.exists_joint_policy
  have hgc' : ∀ θ, Continuous (g θ) := fun θ =>
    hgc.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hgm : ∀ θ, Measurable (g θ) := fun θ => (hgc' θ).measurable
  have : Nonempty M.S := ⟨⟨0, le_rfl, M.kbar_pos.le⟩⟩
  have hmk : ∀ θ, IsMarkovKernel (policyKernel M.Q (g θ) (hgm θ)) := fun θ =>
    isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum _ _
  have hex : ∀ θ, ∃ μ : ProbabilityMeasure (M.S × Z),
      Kernel.Invariant (policyKernel M.Q (g θ) (hgm θ)) μ := fun θ => by
    obtain ⟨μ, hμ, hinv⟩ := exists_invariant_of_feller (policyKernel M.Q (g θ) (hgm θ))
      (isFeller_policyKernel M.Q_nonneg (hgc' θ) (hgm θ))
    exact ⟨⟨μ, hμ⟩, hinv⟩
  choose π hπ using hex
  have hJF := M.isJointlyFeller_policyKernel g hgc hgm
  have hu : ∀ θ, ∀ μ ν : ProbabilityMeasure (M.S × Z),
      Kernel.Invariant (policyKernel M.Q (g θ) (hgm θ)) μ →
      Kernel.Invariant (policyKernel M.Q (g θ) (hgm θ)) ν → μ = ν :=
    fun θ => huniq θ (g θ) (hgm θ) (hg θ)
  exact ⟨g, hgm, π, hgc, hg, hπ, continuous_invariant_of_unique _ hJF hu π hπ,
    continuous_integral_invariant _ hJF hu π hπ M.assets⟩

omit [CompactSpace Θ] [T2Space Θ] [MeasurableSpace Z] [BorelSpace Z] [DiscreteTopology Z] in
theorem assets_le (s : M.S × Z) : M.assets s ≤ M.kbar := s.1.2.2

omit [CompactSpace Θ] [T2Space Θ] in
theorem integral_assets_le [Nonempty Z] (μ : ProbabilityMeasure (M.S × Z)) :
    ∫ s, M.assets s ∂(μ : Measure (M.S × Z)) ≤ M.kbar := by
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  calc ∫ s, M.assets s ∂(μ : Measure (M.S × Z)) ≤ ∫ _, M.kbar ∂(μ : Measure (M.S × Z)) :=
        integral_mono (M.assets.integrable _) (integrable_const _) M.assets_le
    _ = M.kbar := by simp

end ParamSavings

/-- **Asset-market clearing in Aiyagari's model** (Aiyagari 1994; LS ch. 18;
existence without uniqueness as in Açıkgöz 2018). Prices range over
`[r_lo, r_hi]`, and `K_d` is a continuous capital-demand curve. Suppose demand
exceeds any feasible supply at the low price (`K_d(r_lo) ≥ k̄`), and at `r_hi`
some stationary distribution supplies at least `K_d(r_hi)`. Then there is a
price `r` and a stationary distribution `π` of the optimal policy at `r` at
which the asset market clears: `∫ a dπ = K_d(r)`.

No uniqueness of the stationary distribution is assumed. The set of stationary
distributions has a closed graph in the price (`isClosed_invariant_graph`) and
is convex, so the set of aggregate supplies is an interval-valued correspondence
with closed graph. A connectedness argument on `[r_lo, r_hi]` then finds a price
at which `K_d(r)` lies between two stationary supplies, and a mixture of the two
distributions clears the market. -/
theorem ParamSavings.exists_asset_market_clearing {Z : Type*} [Fintype Z] [TopologicalSpace Z]
    [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z] {rlo rhi : ℝ}
    (hr : rlo ≤ rhi) (M : ParamSavings (Icc rlo rhi) Z)
    (Kd : ℝ → ℝ) (hKd : ContinuousOn Kd (Icc rlo rhi))
    (hlo : M.kbar ≤ Kd rlo)
    (hhi : ∀ (g : M.S × Z → M.S) (hg : Measurable g),
      (∀ s, (M.slice ⟨rhi, hr, le_rfl⟩).toStochDynProg.policy s = {g s}) →
      ∃ μ : ProbabilityMeasure (M.S × Z), Kernel.Invariant (policyKernel M.Q g hg) μ ∧
        Kd rhi ≤ ∫ s, M.assets s ∂(μ : Measure (M.S × Z))) :
    ∃ r : Icc rlo rhi, ∃ (g : M.S × Z → M.S) (hg : Measurable g) (π : ProbabilityMeasure (M.S × Z)),
      (∀ s, (M.slice r).toStochDynProg.policy s = {g s}) ∧
      Kernel.Invariant (policyKernel M.Q g hg) π ∧
      ∫ s, M.assets s ∂(π : Measure (M.S × Z)) = Kd r := by
  have : CompactSpace (Icc rlo rhi) := isCompact_iff_compactSpace.1 isCompact_Icc
  have : CompactSpace M.S := isCompact_iff_compactSpace.1 isCompact_Icc
  have : Nonempty M.S := ⟨⟨0, le_rfl, M.kbar_pos.le⟩⟩
  obtain ⟨g, hgc, hg⟩ := M.exists_joint_policy
  have hgc' : ∀ θ, Continuous (g θ) := fun θ =>
    hgc.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hgm : ∀ θ, Measurable (g θ) := fun θ => (hgc' θ).measurable
  have hmk : ∀ θ, IsMarkovKernel (policyKernel M.Q (g θ) (hgm θ)) := fun θ =>
    isMarkovKernel_policyKernel M.Q_nonneg M.Q_sum _ _
  have hJF := M.isJointlyFeller_policyKernel g hgc hgm
  set κ := fun θ => policyKernel M.Q (g θ) (hgm θ)
  have hex : ∀ θ, ∃ μ : ProbabilityMeasure (M.S × Z), Kernel.Invariant (κ θ) μ := fun θ => by
    obtain ⟨μ, hμ, hinv⟩ := exists_invariant_of_feller (κ θ)
      (isFeller_policyKernel M.Q_nonneg (hgc' θ) (hgm θ))
    exact ⟨⟨μ, hμ⟩, hinv⟩
  set C := {p : Icc rlo rhi × ProbabilityMeasure (M.S × Z) | Kernel.Invariant (κ p.1) p.2}
  have hC : IsClosed C := isClosed_invariant_graph κ hJF
  have hKs : Continuous fun p : Icc rlo rhi × ProbabilityMeasure (M.S × Z) =>
      ∫ s, M.assets s ∂(p.2 : Measure (M.S × Z)) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction M.assets).comp continuous_snd
  have hKd' : Continuous fun p : Icc rlo rhi × ProbabilityMeasure (M.S × Z) => Kd p.1 :=
    hKd.domRestrict.comp continuous_fst
  -- prices at which some stationary supply is `≤ K_d`, resp. `≥ K_d`
  set A := Prod.fst '' (C ∩ {p | ∫ s, M.assets s ∂(p.2 : Measure (M.S × Z)) ≤ Kd p.1})
  set B := Prod.fst '' (C ∩ {p | Kd p.1 ≤ ∫ s, M.assets s ∂(p.2 : Measure (M.S × Z))})
  have hA : IsClosed A := isClosedMap_fst_of_compactSpace _ (hC.inter (isClosed_le hKs hKd'))
  have hB : IsClosed B := isClosedMap_fst_of_compactSpace _ (hC.inter (isClosed_le hKd' hKs))
  have hAB : (univ : Set (Icc rlo rhi)) ⊆ A ∪ B := fun θ _ => by
    obtain ⟨μ, hμ⟩ := hex θ
    rcases le_total (∫ s, M.assets s ∂(μ : Measure (M.S × Z))) (Kd θ) with h | h
    · exact Or.inl ⟨(θ, μ), ⟨hμ, h⟩, rfl⟩
    · exact Or.inr ⟨(θ, μ), ⟨hμ, h⟩, rfl⟩
  let lo : Icc rlo rhi := ⟨rlo, le_rfl, hr⟩
  let hi : Icc rlo rhi := ⟨rhi, hr, le_rfl⟩
  have hloA : lo ∈ A := by
    obtain ⟨μ, hμ⟩ := hex lo
    exact ⟨(lo, μ), ⟨hμ, (M.integral_assets_le μ).trans hlo⟩, rfl⟩
  have hhiB : hi ∈ B := by
    obtain ⟨μ, hμ, hle⟩ := hhi _ (hgm hi) (hg hi)
    exact ⟨(hi, μ), ⟨hμ, hle⟩, rfl⟩
  obtain ⟨r, -, hrA, hrB⟩ := (isPreconnected_closed_iff.1
    (Subtype.preconnectedSpace isPreconnected_Icc).isPreconnected_univ) A B hA hB hAB
    ⟨lo, trivial, hloA⟩ ⟨hi, trivial, hhiB⟩
  obtain ⟨⟨r1, μ1⟩, ⟨hμ1, h1⟩, rfl⟩ := hrA
  obtain ⟨⟨r2, μ2⟩, ⟨hμ2, h2⟩, hr2⟩ := hrB
  obtain rfl : r2 = r1 := hr2

  -- mix the two stationary distributions
  set k1 := ∫ s, M.assets s ∂(μ1 : Measure (M.S × Z))
  set k2 := ∫ s, M.assets s ∂(μ2 : Measure (M.S × Z))
  have h1' : k1 ≤ Kd r2 := h1
  have h2' : Kd r2 ≤ k2 := h2
  have hμ1' : policyKernel M.Q (g r2) (hgm r2) ∘ₘ (μ1 : Measure (M.S × Z)) = μ1 := hμ1
  have hμ2' : policyKernel M.Q (g r2) (hgm r2) ∘ₘ (μ2 : Measure (M.S × Z)) = μ2 := hμ2
  by_cases hk : k1 = k2
  · exact ⟨r2, g r2, hgm r2, μ1, hg r2, hμ1, le_antisymm h1' (show Kd r2 ≤ k1 by rw [hk]; exact h2')⟩
  have hk' : k1 < k2 := lt_of_le_of_ne (h1'.trans h2') hk
  set t := (k2 - Kd r2) / (k2 - k1)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
  have ht1 : t ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  let ν : Measure (M.S × Z) :=
    ENNReal.ofReal t • (μ1 : Measure (M.S × Z)) + ENNReal.ofReal (1 - t) • (μ2 : Measure (M.S × Z))
  have hν : IsProbabilityMeasure ν := ⟨by
    simp only [ν, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ht0 (by linarith), add_sub_cancel, ENNReal.ofReal_one]⟩
  refine ⟨r2, g r2, hgm r2, ⟨ν, hν⟩, hg r2, ?_, ?_⟩
  · show policyKernel M.Q (g r2) (hgm r2) ∘ₘ ν = ν
    simp only [ν, Measure.comp_add, Measure.comp_smul]
    rw [hμ1', hμ2']
  · show ∫ s, M.assets s ∂ν = Kd r2
    rw [integral_add_measure ((M.assets.integrable _).smul_measure ENNReal.ofReal_ne_top)
      ((M.assets.integrable _).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ht0,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]
    change t * k1 + (1 - t) * k2 = Kd r2
    have : t * (k2 - k1) = k2 - Kd r2 := div_mul_cancel₀ _ (by linarith)
    linarith

/-! ### Non-vacuity -/

/-- **An Aiyagari household family**: `u = √c`, interest rate
`r ∈ [0, 1/20]`, cash on hand `(1 + r) a + y(z)` with income
`y ∈ {1/4, 1/2}` i.i.d., `β = 9/10` (so `β(1 + r) < 1`), asset cap `1`. -/
noncomputable def ParamSavings.aiyagariFamily : ParamSavings (Icc (0 : ℝ) (1 / 20)) (Fin 2) where
  u := Real.sqrt
  h := fun r a z => (1 + r) * a + ![1 / 4, 1 / 2] z
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
  h_continuous := fun z => ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).mul
    continuous_snd).add continuous_const
  h_nonneg := fun r z k hk => add_nonneg (mul_nonneg (by linarith [r.2.1]) hk)
    (by fin_cases z <;> norm_num)
  h_concave := fun r z => ⟨convex_Ici 0, fun x _ y _ a b _ _ hab => by
    simp only [smul_eq_mul]
    exact le_of_eq (by linear_combination (![(1 : ℝ) / 4, 1 / 2] z) * hab)⟩

/-- In the Aiyagari family the savings rule is unique and jointly continuous
in the interest rate and the state. -/
example : ∃ g : Icc (0 : ℝ) (1 / 20) → ParamSavings.aiyagariFamily.S × Fin 2 →
    ParamSavings.aiyagariFamily.S,
    Continuous (fun p : (Icc (0 : ℝ) (1 / 20) × ParamSavings.aiyagariFamily.S) × Fin 2 =>
      g p.1.1 (p.1.2, p.2)) ∧
    ∀ r s, (ParamSavings.aiyagariFamily.slice r).toStochDynProg.policy s = {g r s} := by
  have : CompactSpace (Icc (0 : ℝ) (1 / 20)) := isCompact_iff_compactSpace.1 isCompact_Icc
  exact ParamSavings.aiyagariFamily.exists_joint_policy

/-- **Market clearing in the Aiyagari family**: with the demand curve
`K_d(r) = 1 - 20 r` on `[0, 1/20]`, `exists_asset_market_clearing` applies to the model
where saving earns the return `r`. **Existence check only**: the boundary
conditions here are cheap (`K_d(0) = k̄`, `K_d(1/20) = 0`), so they hold for
reasons unrelated to the household; this shows the theorem applies, not that
the equilibrium is economically interesting. -/
example : ∃ r : Icc (0 : ℝ) (1 / 20), ∃ (g : ParamSavings.aiyagariFamily.S × Fin 2 →
    ParamSavings.aiyagariFamily.S) (hg : Measurable g)
    (π : ProbabilityMeasure (ParamSavings.aiyagariFamily.S × Fin 2)),
    (∀ s, (ParamSavings.aiyagariFamily.slice r).toStochDynProg.policy s = {g s}) ∧
    Kernel.Invariant (policyKernel ParamSavings.aiyagariFamily.Q g hg) π ∧
    ∫ s, ParamSavings.aiyagariFamily.assets s
      ∂(π : Measure (ParamSavings.aiyagariFamily.S × Fin 2)) = 1 - 20 * r :=
  ParamSavings.exists_asset_market_clearing (by norm_num) ParamSavings.aiyagariFamily (fun r => 1 - 20 * r)
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
    (by norm_num [ParamSavings.aiyagariFamily])
    (fun g hg hpol => by
      obtain ⟨μ, hμ⟩ := ParamSavings.aiyagariFamily.exists_stationary_of_policy _ g hg hpol
      refine ⟨μ, hμ, ?_⟩
      norm_num
      exact integral_nonneg fun s => (s.1.2.1 : (0 : ℝ) ≤ s.1))

/-- **A model where saving earns nothing**: cash on hand `y(z)` does not depend
on assets. The optimal policy is `a' = 0`, so the policy kernel is the same
from every state, and the stationary distribution is unique. It witnesses that
the uniqueness and boundary hypotheses of `exists_asset_market_clearing` can hold
together. Its stationary distribution is degenerate in assets. -/
noncomputable def ParamSavings.noReturn : ParamSavings (Icc (0 : ℝ) 1) (Fin 2) where
  u := Real.sqrt
  h := fun _ _ z => ![1 / 4, 1 / 2] z
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
  h_continuous := fun _ => continuous_const
  h_nonneg := fun _ z _ _ => by fin_cases z <;> norm_num
  h_concave := fun _ _ => concaveOn_const _ (convex_Ici 0)

namespace ParamSavings

theorem noReturn_value (θ : Icc (0 : ℝ) 1) (k : noReturn.S) (z : Fin 2) :
    (noReturn.slice θ).toStochDynProg.value (k, z) =
      (noReturn.slice θ).toStochDynProg.value (⟨0, le_rfl, zero_le_one⟩, z) :=
  ((noReturn.slice θ).toStochDynProg.bellman_equation (k, z)).unique
    ((noReturn.slice θ).toStochDynProg.bellman_equation (⟨0, le_rfl, zero_le_one⟩, z))

theorem noReturn_policy (θ : Icc (0 : ℝ) 1) {g : noReturn.S × Fin 2 → noReturn.S}
    (hg : ∀ s, (noReturn.slice θ).toStochDynProg.policy s = {g s}) (s : noReturn.S × Fin 2) :
    g s = ⟨0, le_rfl, zero_le_one⟩ := by
  have hmem : (⟨0, le_rfl, zero_le_one⟩ : noReturn.S) ∈
      (noReturn.slice θ).toStochDynProg.policy s := by
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ ![1 / 4, 1 / 2] s.2
      obtain ⟨k, z⟩ := s
      fin_cases z <;> norm_num
    · intro y hy
      simp only [StochDynProg.objective, StochDynProg.expect]
      have hcont : ∀ z', (noReturn.slice θ).toStochDynProg.value (y, z') =
          (noReturn.slice θ).toStochDynProg.value (⟨0, le_rfl, zero_le_one⟩, z') :=
        fun z' => noReturn_value θ y z'
      simp only [hcont]
      have : (noReturn.slice θ).toStochDynProg.F s y ≤
          (noReturn.slice θ).toStochDynProg.F s ⟨0, le_rfl, zero_le_one⟩ :=
        Real.sqrt_le_sqrt (by linarith [y.2.1])
      linarith
  rw [hg s] at hmem
  exact hmem.symm

theorem noReturn_uniqueStationary (θ : Icc (0 : ℝ) 1) : noReturn.UniqueStationary θ := by
  intro g hg hpol μ ν hμ hν
  have hK : ∀ x, policyKernel noReturn.Q g hg x =
      policyKernel noReturn.Q g hg (⟨0, le_rfl, zero_le_one⟩, 0) := fun x => by
    rw [policyKernel_apply, policyKernel_apply, noReturn_policy θ hpol x,
      noReturn_policy θ hpol (⟨0, le_rfl, zero_le_one⟩, 0)]
    rfl
  have := isMarkovKernel_policyKernel noReturn.Q_nonneg noReturn.Q_sum g hg
  have hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal 1 *
      policyKernel noReturn.Q g hg (⟨0, le_rfl, zero_le_one⟩, 0) A ≤
      policyKernel noReturn.Q g hg x A := fun x A _ => by
    rw [ENNReal.ofReal_one, one_mul, hK x]
  have := doeblin_unique (π := (μ : Measure _)) (π' := (ν : Measure _)) one_pos le_rfl hmin hμ hν
  exact (Subtype.ext this).symm

/-- **The equilibrium hypotheses can all hold**: in `noReturn` with demand
`K_d(r) = 1 - r` on `[0, 1]`, `exists_asset_market_clearing` applies. -/
example : ∃ r : Icc (0 : ℝ) 1, ∃ (g : noReturn.S × Fin 2 → noReturn.S) (hg : Measurable g)
    (π : ProbabilityMeasure (noReturn.S × Fin 2)),
    (∀ s, (noReturn.slice r).toStochDynProg.policy s = {g s}) ∧
    Kernel.Invariant (policyKernel noReturn.Q g hg) π ∧
    ∫ s, noReturn.assets s ∂(π : Measure (noReturn.S × Fin 2)) = 1 - r :=
  exists_asset_market_clearing zero_le_one noReturn (fun r => 1 - r)
    (continuousOn_const.sub continuousOn_id) (by norm_num [noReturn])
    (fun g hg hpol => by
      obtain ⟨μ, hμ⟩ := noReturn.exists_stationary_of_policy _ g hg hpol
      refine ⟨μ, hμ, ?_⟩
      simp only [sub_self]
      exact integral_nonneg fun s => (s.1.2.1 : (0 : ℝ) ≤ s.1))

end ParamSavings

end Econ
