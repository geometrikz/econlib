/-
# Lyapunov's convexity theorem (finite-dimensional, nonatomic)

Lyapunov (1940): the range of a finite-dimensional vector measure whose
components are finite and nonatomic is convex. This is the mathematical engine
of Aumann's (1964) core equivalence theorem for economies with a continuum of
traders, and of the "convexifying effect of large numbers" in general.

**Statement.** For finitely many finite nonatomic (nonnegative) measures
`(μᵢ)_{i ∈ η}` on `Ω`, a measurable
set `A` and `t ∈ [0, 1]`, there is a measurable `B ⊆ A` with `μᵢ(B) = t μᵢ(A)`
for every `i` (`exists_subset_measureReal_eq_smul`). Consequently the range
`{(μᵢ(B))ᵢ : B measurable}` is convex (`convex_range`).

**Proof (rounding).** Work with fractional "sets": a measurable set `B` plus
finitely many disjoint pieces `Qₗ` carrying weights `dₗ ∈ [0, 1]`, with
`μ(B) + ∑ₗ dₗ μ(Qₗ) = t μ(A)`. Start from `B = ∅`, one piece `A` with weight
`t`. In each round, cut every piece into pieces of `ν`-measure at most `δ`
(`ν = ∑ᵢ μᵢ`, nonatomic by `nonatomic_sum`; Sierpiński), then move the weights
to a point of the polytope `{e ∈ [0,1]^K : ∑ eₖ μ(Rₖ) = const}` with at most
`|η|` fractional coordinates (`exists_few_fractional`, linear algebra in `ℝ^η`).
Pieces with weight `1` join `B`. After round `k` the fractional part has
`ν`-measure at most `|η| / (k + 1)`, so the increasing sets `B` converge to a set
with exactly the right measures.

Not included here: compactness of the range, the signed-density version
(`B ↦ ∫_B f dλ` with `f` of any sign), and the monotone-chain form. Nonnegative
densities are covered via `Nonatomic.of_absolutelyContinuous`.
-/
module

public import EconLean.Foundations.Measure.Sierpinski
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

noncomputable section

namespace Econ
namespace Lyapunov

open MeasureTheory Set Filter Topology Function Finset

/-! ### The vertex lemma -/

/-- Induction lemma for `exists_few_fractional`. -/
theorem exists_few_fractional_aux {ι η : Type*} [Fintype ι] [Fintype η] (w : ι → η → ℝ) :
    ∀ (k : ℕ) (d : ι → ℝ), (∀ l, 0 ≤ d l ∧ d l ≤ 1) →
      (univ.filter fun l => 0 < d l ∧ d l < 1).card ≤ k →
      ∃ d' : ι → ℝ, (∀ l, 0 ≤ d' l ∧ d' l ≤ 1) ∧ ∑ l, d' l • w l = ∑ l, d l • w l ∧
        (univ.filter fun l => 0 < d' l ∧ d' l < 1).card ≤ Fintype.card η := by
  classical
  set n := Fintype.card η with hn
  intro k
  induction k with
  | zero =>
    intro d hd hk
    exact ⟨d, hd, rfl, by omega⟩
  | succ k ih =>
    intro d hd hk
    set F := univ.filter fun l => 0 < d l ∧ d l < 1 with hF
    by_cases hsmall : F.card ≤ n
    · exact ⟨d, hd, rfl, hsmall⟩
    push Not at hsmall
    -- the fractional vectors are linearly dependent
    have hdep : ¬ LinearIndependent ℝ (fun l : F => w l) := by
      intro hli
      have := LinearIndependent.fintype_card_le_finrank hli
      simp only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card] at this
      omega
    obtain ⟨g, hg0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hdep
    let G : ι → ℝ := fun l => if h : l ∈ F then g ⟨l, h⟩ else 0
    have hG0 : ∀ l, l ∉ F → G l = 0 := fun l hl => by simp [G, hl]
    have hGsum : ∑ l, G l • w l = 0 := by
      rw [← Finset.sum_subset (subset_univ F) (fun l _ hl => by rw [hG0 l hl, zero_smul])]
      rw [← Finset.sum_coe_sort F]
      simpa [G] using hg0
    set S := F.filter fun l => G l ≠ 0 with hS
    have hSne : S.Nonempty := ⟨i0, by
      simp only [hS, Finset.mem_filter]
      exact ⟨i0.2, by simpa [G] using hi0⟩⟩
    let r : ι → ℝ := fun l => if 0 < G l then (1 - d l) / G l else d l / (-G l)
    set s := S.inf' hSne r with hs
    obtain ⟨l0, hl0S, hl0⟩ := S.exists_mem_eq_inf' hSne r
    have hr0 : ∀ l ∈ S, 0 ≤ r l := by
      intro l hl
      have hGl : G l ≠ 0 := (Finset.mem_filter.1 hl).2
      simp only [r]
      split_ifs with hpos
      · exact div_nonneg (by linarith [(hd l).2]) hpos.le
      · exact div_nonneg (hd l).1 (by
          have : G l < 0 := lt_of_le_of_ne (not_lt.1 hpos) hGl
          linarith)
    have hs0 : 0 ≤ s := by rw [hs, hl0]; exact hr0 l0 hl0S
    have hsle : ∀ l ∈ S, s ≤ r l := fun l hl => Finset.inf'_le r hl
    let d' : ι → ℝ := fun l => d l + s * G l
    have hd'mem : ∀ l, 0 ≤ d' l ∧ d' l ≤ 1 := by
      intro l
      by_cases hGl : G l = 0
      · simp only [d', hGl, mul_zero, add_zero]; exact hd l
      have hlF : l ∈ F := by
        by_contra h; exact hGl (hG0 l h)
      have hlS : l ∈ S := Finset.mem_filter.2 ⟨hlF, hGl⟩
      have hb := hsle l hlS
      simp only [r] at hb
      simp only [d']
      split_ifs at hb with hpos
      · rw [le_div_iff₀ hpos] at hb
        constructor <;> nlinarith [(hd l).1, (hd l).2]
      · have hneg : G l < 0 := lt_of_le_of_ne (not_lt.1 hpos) hGl
        rw [le_div_iff₀ (by linarith)] at hb
        constructor <;> nlinarith [(hd l).1, (hd l).2]
    have hl0bd : d' l0 = 0 ∨ d' l0 = 1 := by
      have hGl : G l0 ≠ 0 := (Finset.mem_filter.1 hl0S).2
      simp only [d']
      rw [← hs] at hl0
      rw [hl0]
      simp only [r]
      split_ifs with hpos
      · right; field_simp; ring
      · left
        have : -G l0 ≠ 0 := neg_ne_zero.2 hGl
        field_simp; ring
    have hsum' : ∑ l, d' l • w l = ∑ l, d l • w l := by
      simp only [d', add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hGsum,
        smul_zero, add_zero]
    have hsub : (univ.filter fun l => 0 < d' l ∧ d' l < 1) ⊆ F.erase l0 := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl; rcases hl0bd with h | h <;> rw [h] at hl <;> linarith [hl.1, hl.2]
      · by_contra hlF
        have : d' l = d l := by simp [d', hG0 l hlF]
        rw [this] at hl
        exact hlF (by simp [hF, hl])
    have hcard : (univ.filter fun l => 0 < d' l ∧ d' l < 1).card ≤ k := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_erase_of_mem (Finset.mem_filter.1 hl0S).1
      omega
    obtain ⟨d'', hd'', hs'', hc''⟩ := ih d' hd'mem hcard
    exact ⟨d'', hd'', hs''.trans hsum', hc''⟩

/-- **Few fractional weights** (Carathéodory-type rounding): weights
`d ∈ [0,1]^ι` on finitely many vectors of `ℝ^η` can be moved, keeping `∑ dₗ wₗ`
fixed, to weights with at most `|η|` coordinates in `(0, 1)`. (Any vertex of
the polytope has this property; the result need not be a vertex.) -/
theorem exists_few_fractional {ι η : Type*} [Fintype ι] [Fintype η] (w : ι → η → ℝ)
    (d : ι → ℝ) (hd : ∀ l, 0 ≤ d l ∧ d l ≤ 1) :
    ∃ d' : ι → ℝ, (∀ l, 0 ≤ d' l ∧ d' l ≤ 1) ∧ ∑ l, d' l • w l = ∑ l, d l • w l ∧
      (univ.filter fun l => 0 < d' l ∧ d' l < 1).card ≤ Fintype.card η :=
  exists_few_fractional_aux w _ d hd (Finset.card_le_univ _)

/-! ### Fractional sets and one round of rounding -/

variable {Ω : Type*} [MeasurableSpace Ω] {η : Type*} [Fintype η]

/-- A **fractional set**: a measurable `B ⊆ A` plus disjoint pieces `Qₗ ⊆ A \ B`
with weights `dₗ ∈ [0,1]`, whose vector measure is `t μ(A)`. -/
structure FracState (μ : η → Measure Ω) (A : Set Ω) (t : ℝ) where
  B : Set Ω
  N : ℕ
  Q : Fin N → Set Ω
  d : Fin N → ℝ
  hB : MeasurableSet B
  hBA : B ⊆ A
  hQ : ∀ l, MeasurableSet (Q l)
  hQA : ∀ l, Q l ⊆ A
  hQB : ∀ l, Disjoint B (Q l)
  hQQ : Pairwise (Disjoint on Q)
  hd : ∀ l, 0 ≤ d l ∧ d l ≤ 1
  hsum : ∀ i, (μ i).real B + ∑ l, d l * (μ i).real (Q l) = t * (μ i).real A

variable {μ : η → Measure Ω} [∀ i, IsFiniteMeasure (μ i)]

/-- Each component is dominated by the sum `ν = ∑ⱼ μⱼ`. -/
theorem measureReal_le_sum (i : η) (s : Set Ω) :
    (μ i).real s ≤ (∑ j, μ j).real s := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.single_le_sum (f := fun j => μ j s) (fun j _ => zero_le) (Finset.mem_univ i)

/-- **One round**: any fractional set can be replaced by one with a larger
`B`, at most `|η|` pieces, and every piece of `ν`-measure at most `δ`. -/
theorem FracState.round (hμ : ∀ i, Nonatomic (μ i)) {A : Set Ω} {t : ℝ}
    (S : FracState μ A t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S' : FracState μ A t, S.B ⊆ S'.B ∧ S'.N ≤ Fintype.card η ∧ ∀ l, (∑ j, μ j).real (S'.Q l) ≤ δ := by
  classical
  set ν := ∑ j, μ j with hν
  have hνna : Nonatomic ν := nonatomic_sum μ hμ
  -- refine every piece into small pieces
  have hpart : ∀ l, ∃ (M : ℕ) (P : Fin M → Set Ω), (∀ m, MeasurableSet (P m)) ∧
      Pairwise (Disjoint on P) ∧ (⋃ m, P m) = S.Q l ∧ ∀ m, ν.real (P m) ≤ δ := fun l =>
    exists_partition_measureReal_le hνna hδ (S.hQ l)
  choose M P hPm hPd hPU hPδ using hpart
  let κ := Σ l : Fin S.N, Fin (M l)
  let R : κ → Set Ω := fun k => P k.1 k.2
  have hRQ : ∀ k : κ, R k ⊆ S.Q k.1 := fun k => by
    rw [← hPU k.1]; exact subset_iUnion (P k.1) k.2
  have hRm : ∀ k, MeasurableSet (R k) := fun k => hPm k.1 k.2
  have hRd : Pairwise (Disjoint on R) := by
    rintro ⟨l, m⟩ ⟨l', m'⟩ hne
    by_cases hll : l = l'
    · subst hll
      have hmm : m ≠ m' := fun h => hne (by rw [h])
      exact hPd l hmm
    · exact (S.hQQ hll).mono (hRQ ⟨l, m⟩) (hRQ ⟨l', m'⟩)
  let w : κ → η → ℝ := fun k i => (μ i).real (R k)
  let e : κ → ℝ := fun k => S.d k.1
  have he : ∀ k, 0 ≤ e k ∧ e k ≤ 1 := fun k => S.hd k.1
  obtain ⟨e', he', hsum', hcard⟩ := exists_few_fractional w e he
  -- coordinates of the weighted sums
  have hcoord : ∀ (f : κ → ℝ) (i : η), (∑ k, f k • w k) i = ∑ k, f k * (μ i).real (R k) := by
    intro f i
    simp [w, Finset.sum_apply]
  have hpieces : ∀ i, ∑ k, e k * (μ i).real (R k) = ∑ l, S.d l * (μ i).real (S.Q l) := by
    intro i
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun l _ => ?_
    show ∑ m, S.d l * (μ i).real (P l m) = _
    rw [← Finset.mul_sum, ← hPU l, measureReal_iUnion_fintype (hPd l) (hPm l)]
  -- the new state
  set One := univ.filter fun k => e' k = 1 with hOne
  set Fr := univ.filter fun k => 0 < e' k ∧ e' k < 1 with hFr
  let B' := S.B ∪ ⋃ k ∈ One, R k
  have hRB : ∀ k, Disjoint S.B (R k) := fun k => (S.hQB k.1).mono_right (hRQ k)
  have hOneU : MeasurableSet (⋃ k ∈ One, R k) :=
    Finset.measurableSet_biUnion One fun k _ => hRm k
  have hB'm : MeasurableSet B' := S.hB.union hOneU
  have hdisjBOne : Disjoint S.B (⋃ k ∈ One, R k) :=
    Set.disjoint_iUnion₂_right.2 fun k _ => hRB k
  have hRA : ∀ k, R k ⊆ A := fun k => (hRQ k).trans (S.hQA k.1)
  let eqv := Fr.equivFin
  let Q' : Fin Fr.card → Set Ω := fun j => R (eqv.symm j)
  let d' : Fin Fr.card → ℝ := fun j => e' (eqv.symm j)
  have hFrOne : ∀ k ∈ Fr, k ∉ One := fun k hk hk1 => by
    simp only [hFr, hOne, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk1
    linarith [hk.2]
  -- measure of the new `B`
  have hB'meas : ∀ i, (μ i).real B' = (μ i).real S.B + ∑ k ∈ One, (μ i).real (R k) := by
    intro i
    rw [measureReal_union hdisjBOne hOneU (measure_ne_top _ _) (measure_ne_top _ _),
      measureReal_biUnion_finset (fun k _ k' _ hkk => hRd hkk) (fun k _ => hRm k)
        (fun k _ => measure_ne_top _ _)]
  -- splitting the vertex sum
  have hsplit : ∀ i, ∑ k, e' k * (μ i).real (R k) =
      ∑ k ∈ One, (μ i).real (R k) + ∑ k ∈ Fr, e' k * (μ i).real (R k) := by
    intro i
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : e' k = 1
    · simp [h1]
    · by_cases h0 : e' k = 0
      · simp [h0]
      · have : 0 < e' k ∧ e' k < 1 :=
          ⟨lt_of_le_of_ne (he' k).1 (Ne.symm h0), lt_of_le_of_ne (he' k).2 h1⟩
        simp [h1, this]
  have hFrsum : ∀ i, ∑ j, d' j * (μ i).real (Q' j) = ∑ k ∈ Fr, e' k * (μ i).real (R k) := by
    intro i
    rw [← Finset.sum_coe_sort Fr]
    exact Fintype.sum_equiv eqv.symm _ _ (fun j => rfl)
  refine ⟨⟨B', Fr.card, Q', d', hB'm, union_subset S.hBA (iUnion₂_subset fun k _ => hRA k),
    fun j => hRm _, fun j => hRA _, fun j => ?_, ?_, fun j => he' _, fun i => ?_⟩,
    subset_union_left, ?_, fun j => hPδ _ _⟩
  · -- new pieces are disjoint from the new `B`
    refine Set.disjoint_union_left.2 ⟨hRB _, Set.disjoint_iUnion₂_left.2 fun k hk => ?_⟩
    have hkFr : (eqv.symm j : κ) ∈ Fr := (eqv.symm j).2
    have hne : k ≠ (eqv.symm j : κ) := fun h => hFrOne _ hkFr (h ▸ hk)
    exact hRd hne
  · intro j j' hjj
    have : (eqv.symm j : κ) ≠ (eqv.symm j' : κ) := fun h =>
      hjj (eqv.symm.injective (Subtype.ext h))
    exact hRd this
  · rw [hB'meas, hFrsum, add_assoc, ← hsplit, ← S.hsum i, ← hpieces i]
    have h := congrFun hsum' i
    rw [hcoord, hcoord] at h
    rw [h]
  · simpa [hFr] using hcard

/-! ### Lyapunov's theorem -/

/-- **Lyapunov's convexity theorem** (finite-dimensional, nonatomic): for finite
nonatomic `(μᵢ)_{i ∈ η}`, measurable `A` and `t ∈ [0,1]` there is a measurable
`B ⊆ A` with `μᵢ(B) = t μᵢ(A)` for all `i`. -/
theorem exists_subset_measureReal_eq_smul (hμ : ∀ i, Nonatomic (μ i)) {A : Set Ω}
    (hA : MeasurableSet A) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B ⊆ A, MeasurableSet B ∧ ∀ i, (μ i).real B = t * (μ i).real A := by
  classical
  set ν := ∑ j, μ j with hν
  let S0 : FracState μ A t :=
    { B := ∅, N := 1, Q := fun _ => A, d := fun _ => t, hB := MeasurableSet.empty,
      hBA := empty_subset _, hQ := fun _ => hA, hQA := fun _ => subset_rfl,
      hQB := fun _ => empty_disjoint _,
      hQQ := fun i j hij => absurd (Subsingleton.elim i j) hij,
      hd := fun _ => ⟨ht0, ht1⟩, hsum := fun i => by simp }
  have hround : ∀ (S : FracState μ A t) (k : ℕ), ∃ S' : FracState μ A t, S.B ⊆ S'.B ∧
      S'.N ≤ Fintype.card η ∧ ∀ l, ν.real (S'.Q l) ≤ 1 / ((k : ℝ) + 1) :=
    fun S k => S.round hμ (by positivity)
  choose next hnext using hround
  let seq : ℕ → FracState μ A t := fun k => Nat.rec S0 (fun k S => next S k) k
  have hseq : ∀ k, seq (k + 1) = next (seq k) k := fun k => rfl
  have hmono : Monotone fun k => (seq k).B := monotone_nat_of_le_succ fun k => by
    simp only [hseq]; exact (hnext _ k).1
  set U := ⋃ k, (seq k).B with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun k => (seq k).hB
  have hUA : U ⊆ A := iUnion_subset fun k => (seq k).hBA
  refine ⟨U, hUA, hUm, fun i => ?_⟩
  have htend : Tendsto (fun k => (μ i).real (seq k).B) atTop (𝓝 ((μ i).real U)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ U)).comp (tendsto_measure_iUnion_atTop hmono)
  -- the fractional remainder is small
  have hbound : ∀ k, |t * (μ i).real A - (μ i).real (seq (k + 1)).B| ≤
      (Fintype.card η : ℝ) * (1 / ((k : ℝ) + 1)) := by
    intro k
    set S := seq (k + 1)
    have hS := hnext (seq k) k
    rw [← hseq] at hS
    have hrem : t * (μ i).real A - (μ i).real S.B = ∑ l, S.d l * (μ i).real (S.Q l) := by
      rw [← S.hsum i]; ring
    rw [hrem, abs_of_nonneg (Finset.sum_nonneg fun l _ =>
      mul_nonneg (S.hd l).1 measureReal_nonneg)]
    calc ∑ l, S.d l * (μ i).real (S.Q l) ≤ ∑ _l : Fin S.N, 1 / ((k : ℝ) + 1) := by
          refine Finset.sum_le_sum fun l _ => ?_
          calc S.d l * (μ i).real (S.Q l) ≤ 1 * (μ i).real (S.Q l) :=
                mul_le_mul_of_nonneg_right (S.hd l).2 measureReal_nonneg
            _ ≤ ν.real (S.Q l) := by rw [one_mul]; exact measureReal_le_sum i _
            _ ≤ 1 / ((k : ℝ) + 1) := hS.2.2 l
      _ = S.N * (1 / ((k : ℝ) + 1)) := by simp
      _ ≤ (Fintype.card η : ℝ) * (1 / ((k : ℝ) + 1)) := by
          gcongr
          exact_mod_cast hS.2.1
  have htend2 : Tendsto (fun k => (μ i).real (seq (k + 1)).B) atTop
      (𝓝 (t * (μ i).real A)) := by
    have hzero : Tendsto (fun k : ℕ => (Fintype.card η : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Fintype.card η : ℝ)
    have hlo := (tendsto_const_nhds (x := t * (μ i).real A)).sub hzero
    have hhi := (tendsto_const_nhds (x := t * (μ i).real A)).add hzero
    simp only [sub_zero, add_zero] at hlo hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun k => ?_) (fun k => ?_)
    · have := (abs_le.1 (hbound k)).2; simp only at this ⊢; linarith
    · have := (abs_le.1 (hbound k)).1; simp only at this ⊢; linarith
  exact tendsto_nhds_unique (htend.comp (tendsto_add_atTop_nat 1)) htend2

/-- The **range** of the vector measure `(μᵢ)ᵢ`. -/
protected def range (μ : η → Measure Ω) : Set (η → ℝ) :=
  {v | ∃ B, MeasurableSet B ∧ v = fun i => (μ i).real B}

/-- **Lyapunov's theorem, convexity form**: the range of a finite-dimensional
vector measure with finite nonatomic components is convex. -/
theorem convex_range (hμ : ∀ i, Nonatomic (μ i)) : Convex ℝ (Lyapunov.range μ) := by
  rintro _ ⟨E, hE, rfl⟩ _ ⟨F, hF, rfl⟩ a b ha hb hab
  obtain ⟨B1, hB1, hB1m, hB1μ⟩ := exists_subset_measureReal_eq_smul hμ (hE.diff hF) ha
    (by linarith)
  obtain ⟨B2, hB2, hB2m, hB2μ⟩ := exists_subset_measureReal_eq_smul hμ (hF.diff hE) hb
    (by linarith)
  refine ⟨(E ∩ F) ∪ B1 ∪ B2, ((hE.inter hF).union hB1m).union hB2m, funext fun i => ?_⟩
  symm
  have hd1 : Disjoint (E ∩ F) B1 :=
    Set.disjoint_left.2 fun x hx hx1 => (hB1 hx1).2 hx.2
  have hd2 : Disjoint ((E ∩ F) ∪ B1) B2 := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_left.2 fun x hx hx2 => (hB2 hx2).2 hx.1,
      Set.disjoint_left.2 fun x hx1 hx2 => (hB2 hx2).2 (hB1 hx1).1⟩
  rw [measureReal_union hd2 hB2m, measureReal_union hd1 hB1m, hB1μ, hB2μ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := measureReal_inter_add_sdiff (μ := μ i) (s := E) hF
  have h2 := measureReal_inter_add_sdiff (μ := μ i) (s := F) hE
  rw [Set.inter_comm] at h2
  linear_combination a * h1 + b * h2 - (μ i).real (E ∩ F) * hab

end Lyapunov
end Econ
