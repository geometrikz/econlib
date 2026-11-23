/-
# Correspondences: upper and lower hemicontinuity

Aliprantis–Border, *Infinite Dimensional Analysis* (3rd ed.), §17.1–17.3;
Stokey–Lucas §3.3; MWG Mathematical Appendix M.H.

**The economics.** A *correspondence* `Φ : X ↠ Y` assigns to each point
`x` a *set* `Φ x ⊆ Y`. Budget sets `B(p, w)`, demand `x(p, w)`, best
responses, and the policy correspondence of a dynamic program are all
correspondences. Mathlib has no theory of their continuity, so we build the
standard one here. In Lean a correspondence is just a function
`Φ : X → Set Y`.

Continuity comes in two halves:

* **Upper hemicontinuity (UHC)** at `x`: the set cannot suddenly *explode*.
  For every open `U ⊇ Φ x`, `Φ x' ⊆ U` for all `x'` near `x`.
* **Lower hemicontinuity (LHC)** at `x`: the set cannot suddenly *implode*.
  For every open `U` meeting `Φ x`, `Φ x'` meets `U` for all `x'` near `x`.

"For all `x'` near `x`" is written `∀ᶠ x' in 𝓝 x, …` ("eventually in the
neighbourhood filter of `x`"); it means there is a neighbourhood of `x` on
which the property holds.

Mathlib already supplies the definitions, the singleton characterization
(AB 17.6) and the sequential tests for LHC/UHC (AB 17.20–17.21, "if"
directions). This file adds (AB = Aliprantis–Border numbering):
1. Closed graph ⇒ closed values; UHC + closed values + regular `Y` ⇒
   closed graph (AB 17.10).
2. UHC compact-valued `Φ` ∩ closed-graph `Ψ` is UHC (AB 17.25).
3. **Closed graph + locally compact range ⇒ UHC** (AB 17.11).
4. UHC compact-valued correspondences map compact sets to compact sets
   (AB 17.8).
5. Sequential facts: the sequential form of "closed graph" (AB 17.16), and
   for metric `Y`, UHC + compact values ⇒ every `yₙ ∈ Φ xₙ` with `xₙ → x`
   has a subsequence converging in `Φ x` (AB 17.20, "only if").

No Hausdorff or metric assumptions are used unless stated. All
correspondences may take empty values unless a hypothesis says otherwise.
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Separation.Regular

@[expose] public section

namespace Econ

open Filter Topology Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Definitions

Mathlib (`Mathlib.Topology.Semicontinuity.Defs`) already defines
`UpperHemicontinuousAt`, `LowerHemicontinuousAt`, `UpperHemicontinuous`,
`LowerHemicontinuous` (in the root namespace) and proves the singleton and
sequential characterizations (`upperHemicontinuous_singleton_iff`,
`LowerHemicontinuousAt.of_sequences`, `UpperHemicontinuousAt.of_sequences`,
`LowerHemicontinuousAt.exists_seq_tendsto`, …). We reuse those definitions,
so everything here is compatible with Mathlib. Mathlib's UHC is phrased with
neighbourhoods of the set `Φ x`; the next two lemmas restate both notions in
the textbook "open set" form (AB Def. 17.2). -/

/-- **Textbook definition of UHC** (AB Def. 17.2): every open set containing
`Φ x` contains `Φ x'` for all `x'` near `x`. -/
theorem upperHemicontinuousAt_iff_textbook {Φ : X → Set Y} {x : X} :
    UpperHemicontinuousAt Φ x ↔ ∀ U : Set Y, IsOpen U → Φ x ⊆ U → ∀ᶠ x' in 𝓝 x, Φ x' ⊆ U :=
  upperHemicontinuousAt_iff_forall_isOpen

/-- **Textbook definition of LHC** (AB Def. 17.2): every open set meeting
`Φ x` meets `Φ x'` for all `x'` near `x`. -/
theorem lowerHemicontinuousAt_iff_textbook {Φ : X → Set Y} {x : X} :
    LowerHemicontinuousAt Φ x ↔
      ∀ U : Set Y, IsOpen U → (Φ x ∩ U).Nonempty → ∀ᶠ x' in 𝓝 x, (Φ x' ∩ U).Nonempty :=
  lowerHemicontinuousAt_iff

/-- A correspondence is **continuous** if it is both UHC and LHC. -/
def ContinuousCorrespondence (Φ : X → Set Y) : Prop :=
  UpperHemicontinuous Φ ∧ LowerHemicontinuous Φ

/-- The **graph** of `Φ`: all pairs `(x, y)` with `y ∈ Φ x`. -/
def graph (Φ : X → Set Y) : Set (X × Y) := {q | q.2 ∈ Φ q.1}

omit [TopologicalSpace X] [TopologicalSpace Y] in
@[simp] theorem mem_graph {Φ : X → Set Y} {q : X × Y} : q ∈ graph Φ ↔ q.2 ∈ Φ q.1 :=
  Iff.rfl

/-! ### Basic facts -/

/-- UHC at `x` only depends on `Φ` near `x` (including at `x` itself). -/
theorem UpperHemicontinuousAt.congr' {Φ Ψ : X → Set Y} {x : X}
    (h : UpperHemicontinuousAt Φ x) (hΦΨ : ∀ᶠ x' in 𝓝 x, Φ x' = Ψ x') :
    UpperHemicontinuousAt Ψ x := by
  rw [upperHemicontinuousAt_iff_textbook] at h ⊢
  intro U hU hxU
  rw [← hΦΨ.self_of_nhds] at hxU
  filter_upwards [h U hU hxU, hΦΨ] with x' h1 h2
  rwa [← h2]

/-! ### 1. Closed graphs -/

/-- A closed graph has closed values. -/
theorem isClosed_of_isClosed_graph {Φ : X → Set Y} (h : IsClosed (graph Φ)) (x : X) :
    IsClosed (Φ x) := by
  -- `Φ x` is the preimage of the graph under the continuous map `y ↦ (x, y)`.
  have : Φ x = (fun y => (x, y)) ⁻¹' graph Φ := rfl
  rw [this]
  exact h.preimage (Continuous.prodMk_right x)

/-- **AB Thm 17.10.** In a regular space `Y`, a UHC correspondence with closed
values has a closed graph. -/
theorem isClosed_graph_of_upperHemicontinuous [RegularSpace Y] {Φ : X → Set Y}
    (hΦ : UpperHemicontinuous Φ) (hcl : ∀ x, IsClosed (Φ x)) :
    IsClosed (graph Φ) := by
  -- We show the complement is open: every `(x, y)` with `y ∉ Φ x` has a
  -- neighbourhood disjoint from the graph.
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨x, y⟩ hxy
  have hy : y ∉ Φ x := hxy
  -- Regularity separates the closed set `Φ x` from the point `y`:
  -- an open `W' ⊇ Φ x` and a neighbourhood `V` of `y` that don't meet.
  have hdis : Disjoint (𝓝ˢ (Φ x)) (𝓝 y) :=
    disjoint_nhdsSet_nhds.2 (by rwa [(hcl x).closure_eq])
  obtain ⟨W, hW, V, hV, hWV⟩ := Filter.disjoint_iff.1 hdis
  obtain ⟨W', hW'o, hsub, hW'W⟩ := mem_nhdsSet_iff_exists.1 hW
  -- Near `x`, `Φ x' ⊆ W'` by UHC; so near `(x, y)` no point is in the graph.
  rw [nhds_prod_eq]
  apply mem_of_superset (prod_mem_prod (upperHemicontinuousAt_iff_textbook.1 (hΦ x) W' hW'o hsub) hV)
  rintro ⟨x', y'⟩ ⟨h1, h2⟩ hmem
  have h1' : Φ x' ⊆ W' := h1
  exact Set.disjoint_left.1 hWV (hW'W (h1' hmem)) h2

/-! ### 2. Intersections (AB Thm 17.25) -/

/-- **AB Thm 17.25 (pointwise).** If `Φ` is UHC at `x` with `Φ x` compact
and `Ψ` has a closed graph, then `x ↦ Φ x ∩ Ψ x` is UHC at `x`.
This is how one shows the *argmax* correspondence is UHC in Berge's
theorem, and that budget-type sets cut out of a compact box are UHC. -/
theorem UpperHemicontinuousAt.inter_of_isClosed_graph {Φ Ψ : X → Set Y} {x : X}
    (hΦ : UpperHemicontinuousAt Φ x) (hK : IsCompact (Φ x))
    (hΨ : IsClosed (graph Ψ)) :
    UpperHemicontinuousAt (fun x => Φ x ∩ Ψ x) x := by
  rw [upperHemicontinuousAt_iff_textbook]
  intro U hU hsub
  -- The part of `Φ x` outside `U` is compact and lies outside `Ψ x`.
  have hC : IsCompact (Φ x \ U) := hK.diff hU
  have hCsub : ({x} : Set X) ×ˢ (Φ x \ U) ⊆ (graph Ψ)ᶜ := by
    rintro ⟨x', y⟩ ⟨hx', hyΦ, hyU⟩ hyΨ
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hyU (hsub ⟨hyΦ, hyΨ⟩)
  -- Tube lemma: a box `u × v` around `{x} × (Φ x \ U)` misses the graph of `Ψ`.
  obtain ⟨u, v, huo, hvo, hxu, hCv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hC hΨ.isOpen_compl hCsub
  have hxu' : x ∈ u := hxu rfl
  -- `Φ x ⊆ U ∪ v`, so near `x`, `Φ x' ⊆ U ∪ v`; points in `v` are not in `Ψ x'`.
  have hsub' : Φ x ⊆ U ∪ v := fun y hy => by
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · exact Or.inr (hCv ⟨hy, hyU⟩)
  filter_upwards [upperHemicontinuousAt_iff_textbook.1 hΦ _ (hU.union hvo) hsub',
    huo.mem_nhds hxu'] with x' h1 h2
  rintro y ⟨hyΦ, hyΨ⟩
  rcases h1 hyΦ with hyU | hyv
  · exact hyU
  · exact (huv (mk_mem_prod h2 hyv) (show (x', y) ∈ graph Ψ from hyΨ)).elim

/-! ### 3. Closed graph ⇒ UHC (AB Thm 17.11) -/

/-- **AB Thm 17.11 (local form).** A correspondence with a closed graph whose
values near `x` all lie in one compact set `K` is UHC at `x`. -/
theorem upperHemicontinuousAt_of_isClosed_graph {Φ : X → Set Y} {x : X} {K : Set Y}
    (hΦ : IsClosed (graph Φ)) (hK : IsCompact K) (hbdd : ∀ᶠ x' in 𝓝 x, Φ x' ⊆ K) :
    UpperHemicontinuousAt Φ x := by
  -- `Φ = K ∩ Φ` near `x`, and `K ∩ Φ` is UHC by the intersection theorem.
  have h := UpperHemicontinuousAt.inter_of_isClosed_graph (Φ := fun _ => K) (x := x)
    UpperHemicontinuousAt.const hK hΦ
  refine UpperHemicontinuousAt.congr' h ?_
  filter_upwards [hbdd] with x' hx'
  exact inter_eq_right.2 hx'

/-- **AB Thm 17.11.** If `Y` is compact, a closed graph implies UHC. -/
theorem upperHemicontinuous_of_isClosed_graph [CompactSpace Y] {Φ : X → Set Y}
    (hΦ : IsClosed (graph Φ)) : UpperHemicontinuous Φ := fun _ =>
  upperHemicontinuousAt_of_isClosed_graph hΦ isCompact_univ
    (Eventually.of_forall fun _ => subset_univ _)

/-! ### 4. Compact images (AB Lemma 17.8) -/

/-- **AB Lemma 17.8.** A correspondence that is UHC with compact values on a
compact set `K` maps it to a compact set `⋃ x ∈ K, Φ x`. -/
theorem IsCompact.biUnion_of_upperHemicontinuous {Φ : X → Set Y} {K : Set X}
    (hK : IsCompact K) (hΦ : ∀ x ∈ K, UpperHemicontinuousAt Φ x)
    (hc : ∀ x ∈ K, IsCompact (Φ x)) : IsCompact (⋃ x ∈ K, Φ x) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hUo hcover
  -- For each `x ∈ K`, finitely many `U i` cover the compact set `Φ x`.
  have hfin : ∀ x, ∃ t : Finset ι, x ∈ K → Φ x ⊆ ⋃ i ∈ t, U i := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨t, ht⟩ := (hc x hx).elim_finite_subcover U hUo
        (fun y hy => hcover (mem_biUnion hx hy))
      exact ⟨t, fun _ => ht⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose t ht using hfin
  -- By UHC, `Φ x' ⊆ ⋃ i ∈ t x, U i` for all `x'` near `x`.
  obtain ⟨s, hsK, hs⟩ := hK.elim_nhds_subcover (fun x => {x' | Φ x' ⊆ ⋃ i ∈ t x, U i})
    (fun x hx => upperHemicontinuousAt_iff_textbook.1 (hΦ x hx) _ (isOpen_biUnion fun i _ => hUo i) (ht x hx))
  -- Finitely many points of `K` suffice, so finitely many `U i` in total.
  refine ⟨s.biUnion t, ?_⟩
  intro y hy
  simp only [mem_iUnion] at hy
  obtain ⟨x', hx'K, hy⟩ := hy
  have := hs hx'K
  simp only [mem_iUnion] at this
  obtain ⟨x, hxs, hx'⟩ := this
  have hy' := hx' hy
  simp only [mem_iUnion] at hy' ⊢
  obtain ⟨i, hi, hyi⟩ := hy'
  exact ⟨i, Finset.mem_biUnion.2 ⟨x, hxs, hi⟩, hyi⟩

/-! ### 6. Sequential characterizations

Economists usually check hemicontinuity with sequences. These are valid
when the spaces are first countable (e.g. metric spaces such as `ℝⁿ`). -/

/-- **Closed graph, sequential form** (AB 17.16 in metric spaces): the graph
is closed iff whenever `xₙ → x`, `yₙ → y` and `yₙ ∈ Φ xₙ`, then `y ∈ Φ x`. -/
theorem isClosed_graph_iff_seq [FirstCountableTopology X] [FirstCountableTopology Y]
    {Φ : X → Set Y} :
    IsClosed (graph Φ) ↔ ∀ (u : ℕ → X) (v : ℕ → Y) (x : X) (y : Y),
      (∀ n, v n ∈ Φ (u n)) → Tendsto u atTop (𝓝 x) → Tendsto v atTop (𝓝 y) → y ∈ Φ x := by
  constructor
  · intro h u v x y hmem hu hv
    exact h.mem_of_tendsto (hu.prodMk_nhds hv) (Eventually.of_forall hmem)
  · intro h
    rw [← isSeqClosed_iff_isClosed]
    intro q p hq hqp
    exact h (fun n => (q n).1) (fun n => (q n).2) p.1 p.2 hq
      ((continuous_fst.tendsto p).comp hqp) ((continuous_snd.tendsto p).comp hqp)

/-- **Sequential consequence of UHC** (AB 17.20, "only if" direction) for
metric `Y`: if `Φ` is UHC at `x` and `Φ x` is compact, then for every
`xₙ → x` and `yₙ ∈ Φ xₙ`, some subsequence of `yₙ` converges to a point of
`Φ x`. -/
theorem UpperHemicontinuousAt.exists_tendsto_subseq {Y : Type*} [PseudoMetricSpace Y]
    {Φ : X → Set Y} {x : X} (hΦ : UpperHemicontinuousAt Φ x) (hK : IsCompact (Φ x))
    {u : ℕ → X} {v : ℕ → Y} (hu : Tendsto u atTop (𝓝 x)) (hv : ∀ n, v n ∈ Φ (u n)) :
    ∃ y ∈ Φ x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (v ∘ φ) atTop (𝓝 y) := by
  -- `Φ x` is nonempty: otherwise UHC with `U = ∅` forces `Φ (u n) = ∅`.
  have hne : (Φ x).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    have := hu.eventually (upperHemicontinuousAt_iff_textbook.1 hΦ ∅ isOpen_empty hempty.subset)
    obtain ⟨n, hn⟩ := this.exists
    exact hn (hv n)
  -- The distance from `yₙ` to `Φ x` tends to zero, by UHC applied to the open
  -- sets `{y | infDist y (Φ x) < ε}`.
  have hdist : Tendsto (fun n => Metric.infDist (v n) (Φ x)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hopen : IsOpen {y | Metric.infDist y (Φ x) < ε} :=
      isOpen_lt (Metric.continuous_infDist_pt _) continuous_const
    have hsub : Φ x ⊆ {y | Metric.infDist y (Φ x) < ε} := fun y hy => by
      simp [Metric.infDist_zero_of_mem hy, hε]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually (upperHemicontinuousAt_iff_textbook.1 hΦ _ hopen hsub))
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn (hv n)
    simp only [mem_ofPred_eq] at this
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    exact this
  -- Pick nearest points `zₙ ∈ Φ x`; a subsequence converges by compactness.
  have hz : ∀ n, ∃ z ∈ Φ x, Metric.infDist (v n) (Φ x) = dist (v n) z :=
    fun n => hK.exists_infDist_eq_dist hne (v n)
  choose z hzΦ hzd using hz
  obtain ⟨y, hy, φ, hφ, hzφ⟩ := hK.tendsto_subseq hzΦ
  refine ⟨y, hy, φ, hφ, ?_⟩
  -- `d(y_{φ n}, y) ≤ d(y_{φ n}, z_{φ n}) + d(z_{φ n}, y) → 0`.
  rw [tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun n => dist (v (φ n)) (z (φ n))) atTop (𝓝 0) := by
    simp only [← hzd]
    exact hdist.comp hφ.tendsto_atTop
  have h2 : Tendsto (fun n => dist (z (φ n)) y) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.1 hzφ)
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => dist_triangle _ _ _) h3

end Econ
