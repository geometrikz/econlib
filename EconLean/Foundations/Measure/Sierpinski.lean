/-
# Nonatomic measures take every intermediate value (Sierpiński 1922)

The first building block for Lyapunov's convexity theorem (Lyapunov 1940) and
hence for Aumann's (1964) core equivalence theorem with a continuum of traders.

A measure is **nonatomic** if every set of positive measure has a measurable
subset of strictly smaller positive measure. For finite (all uses here) or
semifinite measures this is the standard notion of an atomless measure
(Fremlin 211I–J); for a set of infinite measure it asks for a subset of finite
positive measure, which is stronger than atomlessness in general. For finite
measures it implies Mathlib's `NoAtoms` (singletons are null), but not
conversely.

**Results** (for finite measures).
* `exists_subset_measureReal_pos_le`: every set of positive measure has subsets
  of arbitrarily small positive measure.
* `exists_subset_measureReal_eq` (**Sierpiński**): if `0 ≤ c ≤ μ(A)` there is a
  measurable `B ⊆ A` with `μ(B) = c`. The proof is the greedy exhaustion
  argument: repeatedly add a subset of at least half the largest admissible
  size; if the limit fell short of `c`, a small positive subset of the
  remainder would have been admissible at every stage, contradicting that the
  admissible sizes tend to zero.
* `exists_partition_measureReal_le`: every measurable set splits into finitely
  many disjoint measurable pieces of measure at most `δ` (via the induction
  lemma `exists_partition_measureReal_le_aux`).
* `nonatomic_sum`: a finite sum of finite nonatomic measures is nonatomic.
* `Nonatomic.of_absolutelyContinuous`: a finite measure absolutely continuous
  with respect to a finite nonatomic one is nonatomic (so measures with
  densities, `B ↦ ∫_B f dλ`, inherit nonatomicity).
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

namespace Econ
namespace Lyapunov

open MeasureTheory Set Filter Topology Function

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `μ` is **nonatomic**: every set of positive measure has a measurable subset
of strictly smaller positive measure. -/
def Nonatomic (μ : Measure Ω) : Prop :=
  ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s

variable {μ : Measure Ω} [IsFiniteMeasure μ]

theorem measureReal_pos_iff {s : Set Ω} : 0 < μ.real s ↔ 0 < μ s := by
  rw [Measure.real, ENNReal.toReal_pos_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, measure_lt_top μ s⟩⟩

/-- Nonatomicity in terms of real-valued measures. -/
theorem Nonatomic.real (hμ : Nonatomic μ) {s : Set Ω} (hs : MeasurableSet s)
    (h : 0 < μ.real s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.real t ∧ μ.real t < μ.real s := by
  obtain ⟨t, hts, ht, ht0, hlt⟩ := hμ s hs (measureReal_pos_iff.1 h)
  exact ⟨t, hts, ht, measureReal_pos_iff.2 ht0,
    ENNReal.toReal_strict_mono (measure_ne_top μ s) hlt⟩

/-- A positive-measure set has a positive-measure subset of at most half its
measure. -/
theorem Nonatomic.exists_subset_half (hμ : Nonatomic μ) {s : Set Ω} (hs : MeasurableSet s)
    (h : 0 < μ.real s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.real t ∧ μ.real t ≤ μ.real s / 2 := by
  obtain ⟨u, hus, hu, hu0, hlt⟩ := hμ.real hs h
  by_cases hle : μ.real u ≤ μ.real s / 2
  · exact ⟨u, hus, hu, hu0, hle⟩
  · have hdiff : μ.real (s \ u) = μ.real s - μ.real u := measureReal_sdiff hus hu
    exact ⟨s \ u, sdiff_subset, hs.diff hu, by linarith, by linarith⟩

/-- Every set of positive measure has subsets of arbitrarily small positive
measure. -/
theorem exists_subset_measureReal_pos_le (hμ : Nonatomic μ) {s : Set Ω} (hs : MeasurableSet s)
    (h : 0 < μ.real s) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.real t ∧ μ.real t ≤ ε := by
  have hk : ∀ k : ℕ, ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.real t ∧
      μ.real t ≤ μ.real s / 2 ^ k := by
    intro k
    induction k with
    | zero => exact ⟨s, subset_rfl, hs, h, by simp⟩
    | succ k ih =>
      obtain ⟨t, hts, ht, ht0, htle⟩ := ih
      obtain ⟨u, hut, hu, hu0, hule⟩ := hμ.exists_subset_half ht ht0
      refine ⟨u, hut.trans hts, hu, hu0, ?_⟩
      rw [pow_succ, ← div_div]
      linarith
  obtain ⟨k, hk'⟩ := exists_nat_gt (μ.real s / ε)
  have h2k : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
  obtain ⟨t, hts, ht, ht0, htle⟩ := hk k
  refine ⟨t, hts, ht, ht0, htle.trans ?_⟩
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hk'
  nlinarith

/-- **Sierpiński's theorem**: a finite nonatomic measure takes on every value
between `0` and `μ(A)` on measurable subsets of `A`. -/
theorem exists_subset_measureReal_eq (hμ : Nonatomic μ) {A : Set Ω} (hA : MeasurableSet A)
    {c : ℝ} (hc0 : 0 ≤ c) (hcA : c ≤ μ.real A) :
    ∃ B ⊆ A, MeasurableSet B ∧ μ.real B = c := by
  classical
  -- admissible additions to `B`
  let Adm : Set Ω → Set ℝ := fun B =>
    {r | ∃ D, D ⊆ A \ B ∧ MeasurableSet D ∧ μ.real B + μ.real D ≤ c ∧ μ.real D = r}
  let S : Set Ω → ℝ := fun B => sSup (Adm B)
  have hbdd : ∀ B, BddAbove (Adm B) := fun B => ⟨μ.real A, by
    rintro _ ⟨D, hD, -, -, rfl⟩
    exact measureReal_mono (hD.trans sdiff_subset)⟩
  have hle_S : ∀ B D, D ⊆ A \ B → MeasurableSet D → μ.real B + μ.real D ≤ c →
      μ.real D ≤ S B := fun B D h1 h2 h3 => le_csSup (hbdd B) ⟨D, h1, h2, h3, rfl⟩
  have key : ∀ B : Set Ω, ∃ D, μ.real B ≤ c →
      D ⊆ A \ B ∧ MeasurableSet D ∧ μ.real B + μ.real D ≤ c ∧ S B ≤ 2 * μ.real D := by
    intro B
    by_cases hB : μ.real B ≤ c
    · by_cases hS : S B ≤ 0
      · exact ⟨∅, fun _ => ⟨empty_subset _, MeasurableSet.empty, by simpa using hB,
          by simpa using hS⟩⟩
      · push Not at hS
        have hne : (Adm B).Nonempty := ⟨0, ∅, empty_subset _, MeasurableSet.empty,
          by simpa using hB, by simp⟩
        obtain ⟨r, ⟨D, hD, hDm, hDc, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne (half_lt_self hS)
        exact ⟨D, fun _ => ⟨hD, hDm, hDc, by linarith⟩⟩
    · exact ⟨∅, fun h => absurd h hB⟩
  choose Dfun hD using key
  let B : ℕ → Set Ω := fun k => Nat.rec ∅ (fun _ B => B ∪ Dfun B) k
  have hBsucc : ∀ k, B (k + 1) = B k ∪ Dfun (B k) := fun k => rfl
  have inv : ∀ k, B k ⊆ A ∧ MeasurableSet (B k) ∧ μ.real (B k) ≤ c := by
    intro k
    induction k with
    | zero => exact ⟨empty_subset _, MeasurableSet.empty, by simpa [B] using hc0⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3, -⟩ := hD (B k) ih.2.2
      rw [hBsucc]
      have hdisj : Disjoint (B k) (Dfun (B k)) :=
        Set.disjoint_left.2 fun x hx hx' => (h1 hx').2 hx
      refine ⟨union_subset ih.1 (h1.trans sdiff_subset), ih.2.1.union h2, ?_⟩
      rw [measureReal_union hdisj h2]
      exact h3
  have hinc : ∀ k, μ.real (B (k + 1)) = μ.real (B k) + μ.real (Dfun (B k)) := by
    intro k
    obtain ⟨h1, h2, -, -⟩ := hD (B k) (inv k).2.2
    rw [hBsucc, measureReal_union (Set.disjoint_left.2 fun x hx hx' => (h1 hx').2 hx) h2]
  have hmono : Monotone B := monotone_nat_of_le_succ fun k => by
    rw [hBsucc]; exact subset_union_left
  set U := ⋃ k, B k with hU
  have hUA : U ⊆ A := iUnion_subset fun k => (inv k).1
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun k => (inv k).2.1
  have htend : Tendsto (fun k => μ.real (B k)) atTop (𝓝 (μ.real U)) :=
    (ENNReal.tendsto_toReal (measure_ne_top μ U)).comp (tendsto_measure_iUnion_atTop hmono)
  have hUc : μ.real U ≤ c := le_of_tendsto' htend fun k => (inv k).2.2
  have hDtend : Tendsto (fun k => μ.real (Dfun (B k))) atTop (𝓝 0) := by
    have h2 := (htend.comp (tendsto_add_atTop_nat 1)).sub htend
    simp only [sub_self] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp, hinc]
    ring
  refine ⟨U, hUA, hUm, le_antisymm hUc ?_⟩
  by_contra hlt
  push Not at hlt
  have hrem : 0 < μ.real (A \ U) := by
    rw [measureReal_sdiff hUA hUm]; linarith
  obtain ⟨D, hDsub, hDm, hD0, hDle⟩ :=
    exists_subset_measureReal_pos_le hμ (hA.diff hUm) hrem (sub_pos.2 hlt)
  have hbound : ∀ k, μ.real D ≤ 2 * μ.real (Dfun (B k)) := by
    intro k
    have hBU : B k ⊆ U := subset_iUnion B k
    have hadm := hle_S (B k) D (hDsub.trans (sdiff_subset_sdiff_right hBU)) hDm (by
      have := measureReal_mono (μ := μ) hBU
      linarith)
    exact hadm.trans (hD (B k) (inv k).2.2).2.2.2
  have hlim : μ.real D ≤ 2 * 0 :=
    ge_of_tendsto' (hDtend.const_mul 2) hbound
  linarith

/-- Induction lemma for `exists_partition_measureReal_le`: a set of measure at
most `n δ` splits into finitely many disjoint measurable pieces of measure at
most `δ`. -/
theorem exists_partition_measureReal_le_aux (hμ : Nonatomic μ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ (n : ℕ) (A : Set Ω), MeasurableSet A → μ.real A ≤ n * δ →
      ∃ (N : ℕ) (P : Fin N → Set Ω), (∀ i, MeasurableSet (P i)) ∧
        Pairwise (Disjoint on P) ∧ (⋃ i, P i) = A ∧ ∀ i, μ.real (P i) ≤ δ := by
  intro n
  induction n with
  | zero =>
    intro A hA hle
    refine ⟨1, fun _ => A, fun _ => hA, fun i j hij => absurd (Subsingleton.elim i j) hij,
      iUnion_const A, fun _ => ?_⟩
    simp at hle
    linarith
  | succ n ih =>
    intro A hA hle
    by_cases hsmall : μ.real A ≤ δ
    · exact ⟨1, fun _ => A, fun _ => hA, fun i j hij => absurd (Subsingleton.elim i j) hij,
        iUnion_const A, fun _ => hsmall⟩
    push Not at hsmall
    obtain ⟨B, hBA, hBm, hBδ⟩ := exists_subset_measureReal_eq hμ hA hδ.le hsmall.le
    have hrest : μ.real (A \ B) ≤ n * δ := by
      rw [measureReal_sdiff hBA hBm, hBδ]
      push_cast at hle
      linarith
    obtain ⟨N, P, hPm, hPd, hPU, hPδ⟩ := ih (A \ B) (hA.diff hBm) hrest
    refine ⟨N + 1, Fin.cons B P, fun i => ?_, ?_, ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hBm
      · simpa using hPm j
    · have hBP : ∀ j, Disjoint B (P j) := fun j =>
        Set.disjoint_left.2 fun x hx hx' => by
          have : x ∈ A \ B := hPU ▸ mem_iUnion.2 ⟨j, hx'⟩
          exact this.2 hx
      intro i j hij
      refine Fin.cases (fun hij => ?_) (fun i hij => ?_) i hij
      · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hij
        simpa [Function.onFun] using hBP j
      · refine Fin.cases (fun _ => ?_) (fun j hij => ?_) j hij
        · simpa [Function.onFun] using (hBP i).symm
        · simpa [Function.onFun] using hPd (fun h => hij (by rw [h]))
    · ext x
      simp only [mem_iUnion, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
      have hx : (∃ i, x ∈ P i) ↔ x ∈ A \ B := by rw [← mem_iUnion (s := P), hPU]
      rw [hx, Set.mem_sdiff]
      constructor
      · rintro (h | h)
        · exact hBA h
        · exact h.1
      · intro h
        by_cases hb : x ∈ B
        · exact Or.inl hb
        · exact Or.inr ⟨h, hb⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp [hBδ]
      · simpa using hPδ j

/-- Every measurable set splits into finitely many disjoint measurable pieces of
measure at most `δ`. -/
theorem exists_partition_measureReal_le (hμ : Nonatomic μ) {δ : ℝ} (hδ : 0 < δ)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∃ (N : ℕ) (P : Fin N → Set Ω), (∀ i, MeasurableSet (P i)) ∧
      Pairwise (Disjoint on P) ∧ (⋃ i, P i) = A ∧ ∀ i, μ.real (P i) ≤ δ := by
  obtain ⟨n, hn⟩ := exists_nat_ge (μ.real A / δ)
  exact exists_partition_measureReal_le_aux hμ hδ n A hA (by rwa [div_le_iff₀ hδ] at hn)

/-- A finite sum of finite nonatomic measures is nonatomic. -/
theorem nonatomic_sum {ι : Type*} [Fintype ι] (ν : ι → Measure Ω)
    [∀ i, IsFiniteMeasure (ν i)] (h : ∀ i, Nonatomic (ν i)) : Nonatomic (∑ i, ν i) := by
  classical
  intro s hs hpos
  rw [FunLike.coe_sum, Finset.sum_apply] at hpos
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < ν i s := by
    by_contra hcon
    push Not at hcon
    have : ∑ i, ν i s = 0 := Finset.sum_eq_zero fun i hi => le_antisymm (hcon i hi) zero_le
    rw [this] at hpos
    exact lt_irrefl _ hpos
  have hreal : 0 < (ν i).real s := measureReal_pos_iff.2 hi
  obtain ⟨t, hts, ht, htc⟩ := exists_subset_measureReal_eq (h i) hs (by positivity)
    (half_le_self hreal.le)
  have ht0 : 0 < ν i t := (measureReal_pos_iff (μ := ν i)).1 (by rw [htc]; positivity)
  have hst0 : 0 < ν i (s \ t) := by
    apply (measureReal_pos_iff (μ := ν i)).1
    rw [measureReal_sdiff hts ht, htc]
    linarith
  refine ⟨t, hts, ht, ?_, ?_⟩
  · rw [FunLike.coe_sum, Finset.sum_apply]
    exact lt_of_lt_of_le ht0 (Finset.single_le_sum (f := fun j => ν j _) (fun j _ => zero_le) (Finset.mem_univ i))
  · have hsplit : (∑ j, ν j) s = (∑ j, ν j) t + (∑ j, ν j) (s \ t) := by
      rw [← measure_union disjoint_sdiff_right (hs.diff ht), union_sdiff_cancel hts]
    rw [hsplit]
    have hfin : (∑ j, ν j) t ≠ ⊤ := measure_ne_top _ _
    have hpos' : 0 < (∑ j, ν j) (s \ t) := by
      rw [FunLike.coe_sum, Finset.sum_apply]
      exact lt_of_lt_of_le hst0
        (Finset.single_le_sum (f := fun j => ν j _) (fun j _ => zero_le) (Finset.mem_univ i))
    exact ENNReal.lt_add_right hfin hpos'.ne'

/-- A finite measure absolutely continuous with respect to a finite nonatomic
measure is nonatomic. (If `ν` had an atom `s`, halving `s` in `λ`-measure
repeatedly while keeping full `ν`-measure would give a `λ`-null set of positive
`ν`-measure.) -/
theorem Nonatomic.of_absolutelyContinuous {lam ν : Measure Ω} [IsFiniteMeasure lam]
    [IsFiniteMeasure ν] (hlam : Nonatomic lam) (hac : ν ≪ lam) : Nonatomic ν := by
  classical
  intro s hs hpos
  by_contra hcon
  push Not at hcon
  have step : ∀ u : Set Ω, ∃ v, (u ⊆ s ∧ MeasurableSet u ∧ ν u = ν s) →
      v ⊆ u ∧ MeasurableSet v ∧ ν v = ν s ∧ lam.real v = lam.real u / 2 := by
    intro u
    by_cases hu : u ⊆ s ∧ MeasurableSet u ∧ ν u = ν s
    · obtain ⟨hus, hum, huν⟩ := hu
      obtain ⟨v, hvu, hvm, hvlam⟩ := exists_subset_measureReal_eq hlam hum
        (by positivity) (half_le_self measureReal_nonneg)
      by_cases hv : ν v = 0
      · refine ⟨u \ v, fun _ => ⟨sdiff_subset, hum.diff hvm, ?_, ?_⟩⟩
        · rw [measure_sdiff hvu hvm.nullMeasurableSet (measure_ne_top _ _), hv, tsub_zero, huν]
        · rw [measureReal_sdiff hvu hvm, hvlam]; ring
      · have h1 := hcon v (hvu.trans hus) hvm (pos_iff_ne_zero.2 hv)
        have h2 : ν v ≤ ν u := measure_mono hvu
        exact ⟨v, fun _ => ⟨hvu, hvm, le_antisymm (h2.trans huν.le) h1, hvlam⟩⟩
    · exact ⟨∅, fun h => absurd h hu⟩
  choose next hnext using step
  let seq : ℕ → Set Ω := fun k => Nat.rec s (fun _ u => next u) k
  have hseq : ∀ k, seq (k + 1) = next (seq k) := fun k => rfl
  have inv : ∀ k, seq k ⊆ s ∧ MeasurableSet (seq k) ∧ ν (seq k) = ν s ∧
      lam.real (seq k) = lam.real s / 2 ^ k := by
    intro k
    induction k with
    | zero => exact ⟨subset_rfl, hs, rfl, by simp [seq]⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3, h4⟩ := hnext (seq k) ⟨ih.1, ih.2.1, ih.2.2.1⟩
      rw [hseq]
      refine ⟨h1.trans ih.1, h2, h3, ?_⟩
      rw [h4, ih.2.2.2, pow_succ]; ring
  have hanti : Antitone seq := antitone_nat_of_succ_le fun k => by
    rw [hseq]; exact (hnext (seq k) ⟨(inv k).1, (inv k).2.1, (inv k).2.2.1⟩).1
  set I := ⋂ k, seq k with hI
  have hIν : ν I = ν s := by
    have ht := tendsto_measure_iInter_atTop (μ := ν) (fun k => (inv k).2.1.nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    have hconst : (ν ∘ seq) = fun _ => ν s := funext fun k => (inv k).2.2.1
    rw [hconst] at ht
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm
  have hIlam : lam I = 0 := by
    have hle : ∀ k : ℕ, lam.real I ≤ lam.real s / 2 ^ k := fun k => by
      rw [← (inv k).2.2.2]; exact measureReal_mono (iInter_subset seq k)
    have hzero : lam.real I = 0 := by
      by_contra hne
      have hIpos : 0 < lam.real I := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
      obtain ⟨k, hk⟩ := exists_nat_gt (lam.real s / lam.real I)
      have h2k : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have := hle k
      rw [div_lt_iff₀ hIpos] at hk
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hzero
  have := hac hIlam
  rw [hIν] at this
  exact hpos.ne' this

end Lyapunov
end Econ
