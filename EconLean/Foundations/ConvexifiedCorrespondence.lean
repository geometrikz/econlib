/-
# Convexified correspondences

**The mathematics.** Fixed-point theorems of Kakutani type need convex values.
A correspondence with arbitrary (e.g. non-convex) values can be replaced by its
**convexification** `x ↦ conv (Φ x)`, and in economics this is exactly what a
continuum of agents does to aggregate demand (Aumann 1966): averaging over a
nonatomic population convexifies.

The point of this file is that convexification preserves the hypotheses of
Kakutani's theorem: it obviously gives convex values, it preserves nonemptiness,
and — the nontrivial part — it preserves a **closed graph**, provided all values
lie in one fixed compact set. The proof is Carathéodory's theorem with a fixed
number `N = dim V + 1` of weights, which turns a convex combination into a point
of the compact set `Δ_N × K^N`, where a convergent subsequence can be extracted.

**Results.**
* `exists_fin_convexComb`: Carathéodory with a fixed index type `Fin (dim V + 1)`
  (weights allowed to vanish, so the index type does not depend on the point).
* `isClosed_graph_convexHull`: the convexification of a closed-graph
  correspondence with values in a fixed compact set has a closed graph.
* `isClosed_graph_convexHull_on`: the same, relativised to a domain `s`, in the
  exact form required by `Econ.kakutani_fixedPoint`.
* `convexHull_nonempty_iff` (with Mathlib's `convex_convexHull`): the other two
  Kakutani hypotheses.
-/
module

public import EconLean.Foundations.Correspondence
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

namespace Econ

open Set Module Function Filter Topology

/-- Summing a function extended by zero along an injection. -/
theorem sum_extend_of_injective {κ N M : Type*} [Fintype κ] [Fintype N] [AddCommMonoid M]
    {e : κ → N} (he : Injective e) (f : κ → M) :
    ∑ i, Function.extend e f 0 i = ∑ k, f k := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) ?_,
    Finset.sum_image (fun a _ b _ h => he h)]
  · exact Finset.sum_congr rfl fun k _ => he.extend_apply f (0 : N → M) k
  · intro i _ hi
    refine extend_apply' _ _ _ fun ⟨k, hk⟩ => hi ?_
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Carathéodory's theorem with a fixed index type**: every point of the convex
hull of a nonempty `s` is a convex combination of `dim V + 1` points of `s`
(weights may be zero, so the index type is the same for every point). -/
theorem exists_fin_convexComb {s : Set V} (hs : s.Nonempty) {v : V}
    (hv : v ∈ convexHull ℝ s) :
    ∃ (w : Fin (finrank ℝ V + 1) → ℝ) (z : Fin (finrank ℝ V + 1) → V),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = v := by
  classical
  obtain ⟨κ, hκ, z', w', hzs, hai, hw', hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hv
  have hcard : Fintype.card κ ≤ finrank ℝ V + 1 :=
    hai.card_le_finrank_succ.trans (by gcongr; exact Submodule.finrank_le _)
  obtain ⟨v0, hv0⟩ := hs
  obtain ⟨e, he⟩ : ∃ e : κ → Fin (finrank ℝ V + 1), Injective e := by
    obtain ⟨e⟩ : Nonempty (κ ↪ Fin (finrank ℝ V + 1)) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    exact ⟨e, e.injective⟩
  refine ⟨Function.extend e w' 0, fun i => if h : ∃ k, e k = i then z' h.choose else v0,
    fun i => ?_, ?_, fun i => ?_, ?_⟩
  · by_cases h : ∃ k, e k = i
    · obtain ⟨k, rfl⟩ := h
      rw [he.extend_apply w' 0]
      exact (hw' k).le
    · rw [extend_apply' _ _ _ h]; exact le_rfl
  · rw [sum_extend_of_injective he, hw1]
  · dsimp only; split_ifs with h
    · exact hzs (mem_range_self _)
    · exact hv0
  · rw [← hwz]
    have : ∀ i, Function.extend e w' 0 i •
        (if h : ∃ k, e k = i then z' h.choose else v0) =
        Function.extend e (fun k => w' k • z' k) 0 i := by
      intro i
      by_cases h : ∃ k, e k = i
      · obtain ⟨k, rfl⟩ := h
        have hk : (⟨k, rfl⟩ : ∃ k', e k' = e k).choose = k :=
          he (Exists.choose_spec (⟨k, rfl⟩ : ∃ k', e k' = e k))
        rw [he.extend_apply w' 0, he.extend_apply (fun k => w' k • z' k) 0]
        simp only [dite_eq_left_of_eq_true (eq_true (⟨k, rfl⟩ : ∃ k', e k' = e k)), hk]
      · rw [extend_apply' _ _ _ h, extend_apply' _ _ _ h, dite_eq_right h]
        simp
    rw [Finset.sum_congr rfl fun i _ => this i, sum_extend_of_injective he]

variable {X : Type*} [TopologicalSpace X]

omit [FiniteDimensional ℝ V] [TopologicalSpace X] in
/-- The convexification of a correspondence is nonempty exactly where the
correspondence is. -/
theorem convexHull_nonempty_iff {Φ : X → Set V} (x : X) :
    (convexHull ℝ (Φ x)).Nonempty ↔ (Φ x).Nonempty := by
  refine ⟨fun h => ?_, fun h => h.mono (subset_convexHull _ _)⟩
  rw [nonempty_iff_ne_empty] at h ⊢
  exact fun he => h (by rw [he, convexHull_empty])

/-- **Convexification preserves a closed graph** when all values lie in one
compact set `K`. -/
theorem isClosed_graph_convexHull [FirstCountableTopology X] {Φ : X → Set V} {K : Set V}
    (hK : IsCompact K) (hsub : ∀ x, Φ x ⊆ K) (h : IsClosed (graph Φ)) :
    IsClosed (graph fun x => convexHull ℝ (Φ x)) := by
  classical
  set N := finrank ℝ V + 1
  rw [isClosed_graph_iff_seq]
  intro u v x y hmem hu hv
  -- Carathéodory representations of `v n`
  have hne : ∀ n, (Φ (u n)).Nonempty := fun n =>
    (convexHull_nonempty_iff (Φ := Φ) (u n)).1 ⟨v n, hmem n⟩
  choose w z hw0 hw1 hzmem hwz using fun n => exists_fin_convexComb (hne n) (hmem n)
  -- extract a convergent subsequence in the compact set `Δ × K^N`
  set W : Set (Fin N → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} with hW
  have hWcomp : IsCompact W := by
    refine (isCompact_Icc (a := (0 : Fin N → ℝ)) (b := fun _ => 1)).of_isClosed_subset ?_ ?_
    · have h1 : IsClosed {w : Fin N → ℝ | ∀ i, 0 ≤ w i} := by
        rw [Set.ofPred_forall]
        exact isClosed_iInter fun i =>
          isClosed_le continuous_const ((continuous_apply i : Continuous fun w : Fin N → ℝ => w i))
      have h2 : IsClosed {w : Fin N → ℝ | ∑ i, w i = 1} :=
        isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
      exact h1.inter h2
    · rintro w ⟨hw0, hw1⟩
      refine ⟨hw0, fun i => ?_⟩
      have : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
      rw [hw1] at this
      exact this
  set S : Set ((Fin N → ℝ) × (Fin N → V)) := W ×ˢ (univ : Set (Fin N)).pi fun _ => K with hS
  have hScomp : IsCompact S := hWcomp.prod (isCompact_univ_pi fun _ => hK)
  have hmemS : ∀ n, (w n, z n) ∈ S :=
    fun n => ⟨⟨fun i => hw0 n i, hw1 n⟩, fun i _ => hsub _ (hzmem n i)⟩
  obtain ⟨⟨w', z'⟩, hS', φ, hφ, hlim⟩ := hScomp.tendsto_subseq hmemS
  have hwlim : Tendsto (fun n => w (φ n)) atTop (𝓝 w') := (continuous_fst.tendsto _).comp hlim
  have hzlim : Tendsto (fun n => z (φ n)) atTop (𝓝 z') := (continuous_snd.tendsto _).comp hlim
  -- the limit points belong to `Φ x`
  have hz'mem : ∀ i, z' i ∈ Φ x := by
    intro i
    refine (isClosed_graph_iff_seq.1 h) (fun n => u (φ n)) (fun n => z (φ n) i) x (z' i)
      (fun n => hzmem _ i) (hu.comp hφ.tendsto_atTop) ?_
    exact ((continuous_apply i).tendsto _).comp hzlim
  -- pass to the limit in the convex combination
  have hsum : Tendsto (fun n => ∑ i, w (φ n) i • z (φ n) i) atTop (𝓝 (∑ i, w' i • z' i)) := by
    have hc : Continuous fun q : (Fin N → ℝ) × (Fin N → V) => ∑ i, q.1 i • q.2 i := by
      refine continuous_finsetSum _ fun i _ => Continuous.smul ?_ ?_
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_snd
    exact (hc.tendsto _).comp hlim
  have hy : y = ∑ i, w' i • z' i := by
    refine tendsto_nhds_unique ((hv.comp hφ.tendsto_atTop).congr fun n => ?_) hsum
    exact (hwz (φ n)).symm
  rw [hy]
  exact (convex_convexHull ℝ (Φ x)).sum_mem (fun i _ => hS'.1.1 i) hS'.1.2
    fun i _ => subset_convexHull _ _ (hz'mem i)

/-- **Relativised form, as Kakutani's theorem uses it** (`Econ.kakutani_fixedPoint`):
if `Φ` has a closed graph over `s` and maps `s` into a compact `K`, so does its
convexification. -/
theorem isClosed_graph_convexHull_on [FirstCountableTopology X] {Φ : X → Set V} {s : Set X}
    {K : Set V} (hK : IsCompact K) (hsub : ∀ x ∈ s, Φ x ⊆ K)
    (h : IsClosed {q : X × V | q.1 ∈ s ∧ q.2 ∈ Φ q.1}) :
    IsClosed {q : X × V | q.1 ∈ s ∧ q.2 ∈ convexHull ℝ (Φ q.1)} := by
  classical
  set Ψ : X → Set V := fun x => if x ∈ s then Φ x else ∅ with hΨ
  have hgraph : graph Ψ = {q : X × V | q.1 ∈ s ∧ q.2 ∈ Φ q.1} := by
    ext q
    simp only [graph, hΨ, mem_ofPred_eq]
    split_ifs with hq <;> simp [hq]
  have hsub' : ∀ x, Ψ x ⊆ K := fun x => by
    simp only [hΨ]
    split_ifs with hx
    · exact hsub x hx
    · exact empty_subset _
  have := isClosed_graph_convexHull hK hsub' (hgraph ▸ h)
  convert this using 1
  ext q
  simp only [graph, hΨ, mem_ofPred_eq]
  split_ifs with hq <;> simp [hq]

end Econ
