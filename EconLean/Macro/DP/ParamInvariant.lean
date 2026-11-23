/-
# Continuity of the invariant distribution in a parameter

Stokey–Lucas (SL) Thm 12.13. Let `κ θ` be a family of Markov kernels on a
compact metric state space `X`, indexed by a parameter `θ` (for Aiyagari, the
interest rate `r`). Suppose the family is **jointly Feller**: for every bounded
continuous `f`, the map `(θ, x) ↦ ∫ f d(κ θ x)` is jointly continuous. If the
kernel at `θ₀` has a **unique** invariant distribution, then every selection
`θ ↦ π θ` of invariant distributions is continuous at `θ₀` in the weak
topology.

Consequently, if every `κ θ` has a unique invariant distribution (for example
by Doeblin's theorem, `Econ.unique_invariant_of_pow`), the map `θ ↦ π θ` is
continuous. In Aiyagari's model this makes aggregate saving a continuous
function of the interest rate, the input to an intermediate-value existence
argument.

**Proof.** Weak convergence on a compact space: the space of probability
measures is compact (Prokhorov), so it suffices to show every cluster point `μ`
of `π θ` as `θ → θ₀` is `κ θ₀`-invariant, and then uniqueness forces
`μ = π θ₀`. For a bounded continuous `f`, `∫ f dπ_θ = ∫ G_θ dπ_θ` with
`G_θ(x) = ∫ f d(κ θ x)`. Joint continuity and compactness of `X` give
`G_θ → G_θ₀` uniformly, and weak convergence gives `∫ G_θ₀ dπ_θ → ∫ G_θ₀ dμ`.
So `∫ f dμ = ∫ G_θ₀ dμ`, which is invariance. The same argument
(`invariant_of_tendsto`) shows the graph `{(θ, μ) | μ is κ θ-invariant}` is
closed (`isClosed_invariant_graph`), which gives existence results without
uniqueness.
-/
module

public import EconLean.Macro.DP.InvariantMeasure
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [CompactSpace X]
  {Θ : Type*} [TopologicalSpace Θ]

/-- A parametrized family of kernels is **jointly Feller** if integrating any
bounded continuous function gives a jointly continuous function of the
parameter and the state. -/
def IsJointlyFeller (κ : Θ → Kernel X X) : Prop :=
  ∀ f : X →ᵇ ℝ, Continuous fun p : Θ × X => ∫ y, f y ∂(κ p.1 p.2)

omit [T2Space X] in
/-- **Limits of invariant distributions are invariant.** Along any nontrivial
filter, if `θ_i → θ₀`, `μ_i → μ₀` weakly and eventually `μ_i` is
`κ θ_i`-invariant, then `μ₀` is `κ θ₀`-invariant. This is the closed-graph
property of the invariant-distribution correspondence (SL Thm 12.13, first
step). -/
theorem invariant_of_tendsto (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ) {ι : Type*} {l : Filter ι} [l.NeBot] {θ : ι → Θ} {θ₀ : Θ}
    (hθ : Tendsto θ l (𝓝 θ₀)) {μ : ι → ProbabilityMeasure X} {μ₀ : ProbabilityMeasure X}
    (hμ : Tendsto μ l (𝓝 μ₀)) (hinv : ∀ᶠ i in l, Kernel.Invariant (κ (θ i)) (μ i)) :
    Kernel.Invariant (κ θ₀) μ₀ := by
  show κ θ₀ ∘ₘ (μ₀ : Measure X) = μ₀
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_comp_measure (f.integrable _)]
  -- `G θ x = ∫ f d(κ θ x)`, curried into `Θ → C(X, ℝ)`.
  let H : C(Θ × X, ℝ) := ⟨fun p => ∫ y, f y ∂(κ p.1 p.2), hκ f⟩
  let G : C(Θ, C(X, ℝ)) := H.curry
  have hunif : TendstoUniformly (fun θ x => G θ x) (G θ₀) (𝓝 θ₀) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mp (G.continuous.tendsto θ₀)
  let g : Θ → X →ᵇ ℝ := fun θ => BoundedContinuousFunction.mkOfCompact (G θ)
  -- `∫ f dμ_i = ∫ G_{θ_i} dμ_i` by invariance.
  have hfG : ∀ᶠ i in l, ∫ y, f y ∂(μ i : Measure X) = ∫ x, g (θ i) x ∂(μ i : Measure X) := by
    filter_upwards [hinv] with i hi
    have h' : κ (θ i) ∘ₘ (μ i : Measure X) = μ i := hi
    conv_lhs => rw [← h']
    rw [integral_comp_measure (f.integrable _)]
    rfl
  -- The uniform error `∫ (G_{θ_i} - G_θ₀) dμ_i` vanishes.
  have h3 : Tendsto (fun i => ∫ x, g (θ i) x ∂(μ i : Measure X) - ∫ x, g θ₀ x ∂(μ i : Measure X))
      l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hθ.eventually (Metric.tendstoUniformly_iff.mp hunif (ε / 2) (by linarith))]
      with i hi
    rw [dist_zero_right, ← integral_sub ((g (θ i)).integrable _) ((g θ₀).integrable _)]
    have hb := norm_integral_le_of_norm_le_const (μ := (μ i : Measure X))
      (f := fun x => g (θ i) x - g θ₀ x) (C := ε / 2) (ae_of_all _ fun x => by
        have := (hi x).le
        rw [dist_comm, Real.dist_eq] at this
        simpa [g, Real.norm_eq_abs] using this)
    rw [probReal_univ, mul_one] at hb
    linarith
  have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (g θ₀)
  have h2 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have h4 : Tendsto (fun i => ∫ y, f y ∂(μ i : Measure X)) l
      (𝓝 (∫ x, g θ₀ x ∂(μ₀ : Measure X))) := by
    have := h3.add h1
    simp only [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hfG] with i hi
    rw [hi]
    exact sub_add_cancel _ _
  have := tendsto_nhds_unique h4 h2
  rw [← this]
  rfl

omit [T2Space X] in
/-- **The graph of the invariant-distribution correspondence is closed** in
`Θ × P(X)`. -/
theorem isClosed_invariant_graph (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ) :
    IsClosed {p : Θ × ProbabilityMeasure X | Kernel.Invariant (κ p.1) p.2} := by
  rw [isClosed_iff_ultrafilter]
  intro x u hu hs
  have hθ : Tendsto Prod.fst (u : Filter (Θ × ProbabilityMeasure X)) (𝓝 x.1) :=
    (continuous_fst.tendsto x).mono_left hu
  have hμ : Tendsto Prod.snd (u : Filter (Θ × ProbabilityMeasure X)) (𝓝 x.2) :=
    (continuous_snd.tendsto x).mono_left hu
  exact invariant_of_tendsto κ hκ hθ hμ hs

/-- **SL Thm 12.13: the invariant distribution is continuous in the parameter
where it is unique.** -/
theorem tendsto_invariant_of_unique (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ) (θ₀ : Θ)
    (huniq : ∀ μ ν : ProbabilityMeasure X, Kernel.Invariant (κ θ₀) μ →
      Kernel.Invariant (κ θ₀) ν → μ = ν)
    (π : Θ → ProbabilityMeasure X) (hπ : ∀ θ, Kernel.Invariant (κ θ) (π θ)) :
    Tendsto π (𝓝 θ₀) (𝓝 (π θ₀)) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  refine huniq μ (π θ₀) ?_ (hπ θ₀)
  rcases mapClusterPt_iff_ultrafilter.mp hμ with ⟨U, hUl, hUμ⟩
  exact invariant_of_tendsto κ hκ (l := (U : Filter Θ)) (θ := id) hUl hUμ
    (Eventually.of_forall hπ)

/-- **Continuity of the invariant distribution.** If every kernel in a jointly
Feller family has a unique invariant distribution `π θ`, then `θ ↦ π θ` is
continuous in the weak topology. -/
theorem continuous_invariant_of_unique (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ)
    (huniq : ∀ θ, ∀ μ ν : ProbabilityMeasure X, Kernel.Invariant (κ θ) μ →
      Kernel.Invariant (κ θ) ν → μ = ν)
    (π : Θ → ProbabilityMeasure X) (hπ : ∀ θ, Kernel.Invariant (κ θ) (π θ)) :
    Continuous π :=
  continuous_iff_continuousAt.2 fun θ₀ => tendsto_invariant_of_unique κ hκ θ₀ (huniq θ₀) π hπ

/-- **Integrals against the invariant distribution are continuous** (for
example aggregate saving `∫ a dπ_r` as a function of `r`). -/
theorem continuous_integral_invariant (κ : Θ → Kernel X X) [∀ θ, IsMarkovKernel (κ θ)]
    (hκ : IsJointlyFeller κ)
    (huniq : ∀ θ, ∀ μ ν : ProbabilityMeasure X, Kernel.Invariant (κ θ) μ →
      Kernel.Invariant (κ θ) ν → μ = ν)
    (π : Θ → ProbabilityMeasure X) (hπ : ∀ θ, Kernel.Invariant (κ θ) (π θ)) (f : X →ᵇ ℝ) :
    Continuous fun θ => ∫ x, f x ∂(π θ : Measure X) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    (continuous_invariant_of_unique κ hκ huniq π hπ)

end Econ
