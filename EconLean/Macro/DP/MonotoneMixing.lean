/-
# Uniqueness of the stationary distribution for monotone Markov processes

Hopenhayn–Prescott (1992); Bhattacharya–Lee (1988); Stokey–Lucas–Prescott
ch. 12.4; Kamihigashi–Stachurski (2014).

Doeblin's condition fails for the wealth process of a savings problem: the
transition from `(a, z)` puts all its wealth mass on the single point
`g(a, z)`, so the transitions from different states need not share any mass.
What such processes have instead is **monotonicity** (more wealth today means
stochastically more wealth tomorrow) and a **splitting** (mixing) condition:
from every state, with probability at least `δ` the process is below a fixed
state `c` after `N` periods, and with probability at least `δ` it is above
`c`.

**First-order stochastic dominance** (`integral_le_of_upper`). On a preordered
space, if `μ(U) ≤ ν(U)` for every measurable upper set `U`, then
`∫ f dμ ≤ ∫ f dν` for every bounded measurable increasing `f`. The proof is the
layer-cake formula: `∫ f = m + ∫_0^l μ{f > m + t} dt` and `{f > m + t}` is an
upper set.

**Monotone kernels** (`IsMonotoneKernel`): `x ↦ κ(x, U)` is increasing for
every measurable upper set `U`. Powers of monotone Markov kernels are monotone.

**Uniqueness** (`unique_invariant_of_splitting`). If `κ` is a monotone Markov
kernel, measurable upper sets generate the σ-algebra, and the splitting
condition holds, then `κ` has at most one invariant probability measure. The
proof is a contraction in the "upper-set distance"
`d(μ, ν) = sup_U |μ(U) - ν(U)|`: for an upper set `U`, `x ↦ κ^N(x, U)` is
increasing with range in an interval of length `1 - δ` (it is `≥ δ` if
`c ∈ U`, and `≤ 1 - δ` if `c ∉ U`), so
`d(μ κ^N, ν κ^N) ≤ (1 - δ) d(μ, ν)`. Invariant measures are fixed points,
so their distance is zero, and they agree on a generating π-system.

**Product spaces** (`generateFrom_upperSets_prod`). On `S × Z` with `S` a
linear order with its order topology and Borel σ-algebra and `Z` a finite
linear order with measurable singletons, with the product (componentwise)
order, measurable upper sets generate the σ-algebra.

Only uniqueness is proved; existence comes from compactness elsewhere
(`StationaryDist`), and convergence of `μ κ^n` is not formalized.
-/
module

public import EconLean.Macro.DP.Doeblin
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

section Layer

variable {X : Type*} [MeasurableSpace X] [Preorder X]

omit [Preorder X] in
/-- Layer cake for a bounded function: if `m ≤ f ≤ m + l`, then
`∫ f dμ = m + ∫_{(0, l]} μ{f - m > t} dt`. -/
theorem integral_eq_layer {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hfm : Measurable f) {m l : ℝ} (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ m + l) :
    ∫ x, f x ∂μ = m + ∫ t in Ioc 0 l, μ.real {x | t < f x - m} := by
  have hint : Integrable f μ :=
    Integrable.mono' (integrable_const (|m| + |m + l|)) hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_le.2 ⟨by linarith [hlo x, neg_abs_le m, abs_nonneg (m + l)],
          by linarith [hhi x, le_abs_self (m + l), abs_nonneg m]⟩)
  have hg : Integrable (fun x => f x - m) μ := hint.sub (integrable_const m)
  have hlc := hg.integral_eq_integral_meas_lt (ae_of_all _ fun x => sub_nonneg.2 (hlo x))
  have hsub : ∫ x, (f x - m) ∂μ = ∫ x, f x ∂μ - m := by
    rw [integral_sub hint (integrable_const m), integral_const, smul_eq_mul, probReal_univ,
      one_mul]
  have hzero : ∀ t ∈ Ioi (0 : ℝ) \ Ioc 0 l, μ.real {x | t < f x - m} = 0 := by
    intro t ht
    have htl : l < t := by
      by_contra h
      exact ht.2 ⟨ht.1, not_lt.1 h⟩
    have : {x | t < f x - m} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith [hhi x]
    rw [this, measureReal_empty]
  have hrestr := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    measurableSet_Ioi (Ioc_subset_Ioi_self : Ioc (0 : ℝ) l ⊆ Ioi 0) hzero
  linarith

omit [Preorder X] in
/-- The layer function `t ↦ μ{f - m > t}` is antitone. -/
theorem antitone_layer (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (m : ℝ) :
    Antitone fun t : ℝ => μ.real {x | t < f x - m} :=
  fun _ _ hst => measureReal_mono (fun _ hx => lt_of_le_of_lt hst hx) (measure_ne_top _ _)

omit [Preorder X] in
theorem integrableOn_layer (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (m l : ℝ) :
    IntegrableOn (fun t : ℝ => μ.real {x | t < f x - m}) (Ioc 0 l) :=
  ((antitone_layer μ f m).antitoneOn _).integrableOn_isCompact isCompact_Icc |>.mono_set
    Ioc_subset_Icc_self

omit [MeasurableSpace X] in
theorem isUpperSet_layer {f : X → ℝ} (hf : Monotone f) (m t : ℝ) :
    IsUpperSet {x | t < f x - m} :=
  fun a b hab (ha : t < f a - m) => show t < f b - m by linarith [hf hab]

/-- **First-order stochastic dominance**: if `μ(U) ≤ ν(U)` for every measurable
upper set `U`, then `∫ f dμ ≤ ∫ f dν` for every bounded measurable increasing
`f`. -/
theorem integral_le_of_upper {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ∀ U, IsUpperSet U → MeasurableSet U → μ.real U ≤ ν.real U)
    {f : X → ℝ} (hf : Monotone f) (hfm : Measurable f) {m l : ℝ}
    (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ m + l) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν := by
  rw [integral_eq_layer hfm hlo hhi, integral_eq_layer hfm hlo hhi]
  have := setIntegral_mono_on (integrableOn_layer μ f m l) (integrableOn_layer ν f m l)
    measurableSet_Ioc fun t _ => hμν _ (isUpperSet_layer hf m t)
      (measurableSet_lt measurable_const (hfm.sub measurable_const))
  linarith

/-- **The upper-set distance controls integrals of increasing functions**: if
`|μ(U) - ν(U)| ≤ D` for every measurable upper set `U`, and `f` is increasing
with values in `[m, m + l]`, then `|∫ f dμ - ∫ f dν| ≤ l D`. -/
theorem abs_integral_sub_le_of_upper {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {D : ℝ}
    (hD : ∀ U, IsUpperSet U → MeasurableSet U → |μ.real U - ν.real U| ≤ D)
    {f : X → ℝ} (hf : Monotone f) (hfm : Measurable f) {m l : ℝ} (hl : 0 ≤ l)
    (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ m + l) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ l * D := by
  rw [integral_eq_layer hfm hlo hhi, integral_eq_layer hfm hlo hhi, add_sub_add_left_eq_sub,
    ← integral_sub (integrableOn_layer μ f m l) (integrableOn_layer ν f m l)]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) l)
    (f := fun t => μ.real {x | t < f x - m} - ν.real {x | t < f x - m}) (C := D)
    measure_Ioc_lt_top fun t _ => by
      rw [Real.norm_eq_abs]
      exact hD _ (isUpperSet_layer hf m t)
        (measurableSet_lt measurable_const (hfm.sub measurable_const))
  rw [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hl] at hb
  linarith

end Layer

section Kernel

variable {X : Type*} [MeasurableSpace X] [Preorder X]

/-- A Markov kernel is **monotone** if the probability of every measurable
upper set increases with the current state. -/
def IsMonotoneKernel (κ : Kernel X X) : Prop :=
  ∀ U, IsUpperSet U → MeasurableSet U → Monotone fun x => (κ x).real U

/-- For a monotone Markov kernel, `x ↦ ∫ f dκ(x)` is increasing for every
bounded measurable increasing `f`. -/
theorem IsMonotoneKernel.integral_mono {κ : Kernel X X} [IsMarkovKernel κ]
    (hκ : IsMonotoneKernel κ) {f : X → ℝ} (hf : Monotone f) (hfm : Measurable f) {m l : ℝ}
    (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ m + l) :
    Monotone fun x => ∫ y, f y ∂(κ x) :=
  fun _ _ hxy => integral_le_of_upper (fun U hU hUm => hκ U hU hUm hxy) hf hfm hlo hhi

omit [Preorder X] in
theorem measurable_real_kernel (κ : Kernel X X) [IsFiniteKernel κ] {U : Set X}
    (hU : MeasurableSet U) : Measurable fun x => (κ x).real U :=
  (κ.measurable_coe hU).ennreal_toReal

omit [Preorder X] in
/-- `(η ∘ₖ κ)(x, U) = ∫ η(y, U) dκ(x)`. -/
theorem comp_real_apply (η κ : Kernel X X) [IsMarkovKernel η] [IsMarkovKernel κ] (x : X)
    {U : Set X} (hU : MeasurableSet U) :
    ((η ∘ₖ κ) x).real U = ∫ y, (η y).real U ∂(κ x) := by
  rw [Kernel.comp_apply]
  exact comp_real_eq_integral η (κ x) hU

/-- The composition of monotone Markov kernels is monotone. -/
theorem IsMonotoneKernel.comp {η κ : Kernel X X} [IsMarkovKernel η] [IsMarkovKernel κ]
    (hη : IsMonotoneKernel η) (hκ : IsMonotoneKernel κ) : IsMonotoneKernel (η ∘ₖ κ) := by
  intro U hU hUm x x' hxx
  simp only
  rw [comp_real_apply η κ x hUm, comp_real_apply η κ x' hUm]
  exact hκ.integral_mono (hη U hU hUm) (measurable_real_kernel η hUm) (m := 0) (l := 1)
    (fun _ => measureReal_nonneg) (fun y => by rw [zero_add]; exact measureReal_le_one) hxx

theorem IsMonotoneKernel.pow {κ : Kernel X X} [IsMarkovKernel κ] (hκ : IsMonotoneKernel κ) :
    ∀ n : ℕ, IsMonotoneKernel (κ ^ n)
  | 0 => by
    rw [pow_zero]
    intro U hU hUm x x' hxx
    change (Kernel.id x).real U ≤ (Kernel.id x').real U
    rw [Kernel.id_apply, Kernel.id_apply, measureReal_def, measureReal_def,
      Measure.dirac_apply' _ hUm, Measure.dirac_apply' _ hUm]
    by_cases hx : x ∈ U
    · have hx' : x' ∈ U := hU hxx hx
      simp [indicator_of_mem hx, indicator_of_mem hx']
    · rw [indicator_of_notMem hx, ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg
  | n + 1 => by
    have := isMarkovKernel_pow κ n
    rw [pow_succ]
    exact (hκ.pow n).comp hκ

/-- **Uniqueness of the invariant distribution of a monotone Markov process
under a splitting condition** (Hopenhayn–Prescott 1992, Theorem 2;
Bhattacharya–Lee 1988): let `κ` be a monotone Markov kernel on a preordered
space whose σ-algebra is generated by its measurable upper sets. If for some
state `c`, some `N` and some `δ > 0`, from every state the process is below
`c` after `N` steps with probability at least `δ`, and above `c` with
probability at least `δ`, then `κ` has at most one invariant probability
measure. -/
theorem unique_invariant_of_splitting {κ : Kernel X X} [IsMarkovKernel κ]
    (hmono : IsMonotoneKernel κ)
    (hgen : ‹MeasurableSpace X› =
      MeasurableSpace.generateFrom {U | IsUpperSet U ∧ MeasurableSet U})
    {N : ℕ} {c : X} {δ : ℝ} (hδ : 0 < δ) (hIic : MeasurableSet (Iic c))
    (hlow : ∀ x, δ ≤ ((κ ^ N) x).real (Iic c)) (hup : ∀ x, δ ≤ ((κ ^ N) x).real (Ici c))
    {π π' : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π') : π' = π := by
  have := isMarkovKernel_pow κ N
  set K := κ ^ N
  have hK : IsMonotoneKernel K := hmono.pow N
  have hδ1 : δ ≤ 1 := by
    obtain ⟨x⟩ : Nonempty X := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := measure_univ (μ := π)
      rw [univ_eq_empty_iff.2 h, measure_empty] at this
      exact zero_ne_one this
    exact (hlow x).trans measureReal_le_one
  -- the upper-set distance
  let 𝒰 := {U : Set X // IsUpperSet U ∧ MeasurableSet U}
  let d : 𝒰 → ℝ := fun U => |π'.real U.1 - π.real U.1|
  have hbdd : BddAbove (range d) := ⟨1, by
    rintro _ ⟨U, rfl⟩
    have h1 : π'.real U.1 ≤ 1 := measureReal_le_one
    have h2 : π.real U.1 ≤ 1 := measureReal_le_one
    have h3 : 0 ≤ π'.real U.1 := measureReal_nonneg
    have h4 : 0 ≤ π.real U.1 := measureReal_nonneg
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩
  have hne : Nonempty 𝒰 := ⟨⟨univ, isUpperSet_univ, MeasurableSet.univ⟩⟩
  set D := ⨆ U, d U
  have hdD : ∀ U, IsUpperSet U → MeasurableSet U → |π'.real U - π.real U| ≤ D :=
    fun U hU hUm => le_ciSup hbdd ⟨U, hU, hUm⟩
  -- contraction
  have hcontr : ∀ U : 𝒰, d U ≤ (1 - δ) * D := by
    rintro ⟨U, hU, hUm⟩
    have e1 : π'.real U = ∫ x, (K x).real U ∂π' := by
      rw [← comp_real_eq_integral K π' hUm, (invariant_pow hπ' N : K ∘ₘ π' = π')]
    have e2 : π.real U = ∫ x, (K x).real U ∂π := by
      rw [← comp_real_eq_integral K π hUm, (invariant_pow hπ N : K ∘ₘ π = π)]
    show |π'.real U - π.real U| ≤ (1 - δ) * D
    rw [e1, e2]
    have hfm := measurable_real_kernel K hUm
    by_cases hc : c ∈ U
    · have hge : ∀ x, δ ≤ (K x).real U := fun x =>
        (hup x).trans (measureReal_mono (fun y hy => hU hy hc) (measure_ne_top _ _))
      exact abs_integral_sub_le_of_upper hdD (hK U hU hUm) hfm (by linarith) hge
        (fun x => by linarith [measureReal_le_one (μ := K x) (s := U)])
    · have hdisj : Disjoint U (Iic c) := disjoint_left.2 fun y hy hyc => hc (hU hyc hy)
      have hle : ∀ x, (K x).real U ≤ 0 + (1 - δ) := fun x => by
        have := measureReal_union (μ := K x) hdisj hIic
        have h1 : (K x).real (U ∪ Iic c) ≤ 1 := measureReal_le_one
        linarith [hlow x]
      exact abs_integral_sub_le_of_upper hdD (hK U hU hUm) hfm (by linarith)
        (fun x => measureReal_nonneg) hle
  have hD : D ≤ (1 - δ) * D := ciSup_le hcontr
  have hD0 : D ≤ 0 := by nlinarith
  -- agreement on upper sets, then on the σ-algebra
  refine ext_of_generate_finite _ hgen ?_ ?_ (by simp)
  · intro s hs t ht _
    exact ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
  · intro U ⟨hU, hUm⟩
    have h := (hdD U hU hUm).trans hD0
    have : π'.real U = π.real U := by linarith [abs_nonneg (π'.real U - π.real U), abs_le.1 h]
    rwa [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)] at this

omit [Preorder X] in
/-- A two-step lower bound: if `κ(x, A) ≥ p` for every `x` and `η(y, B) ≥ q`
for every `y ∈ A`, then `(η ∘ₖ κ)(x, B) ≥ p q`. -/
theorem le_comp_real {η κ : Kernel X X} [IsMarkovKernel η] [IsMarkovKernel κ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) {p q : ℝ} (hq : 0 ≤ q)
    (hp : ∀ x, p ≤ (κ x).real A) (hηq : ∀ y ∈ A, q ≤ (η y).real B) (x : X) :
    p * q ≤ ((η ∘ₖ κ) x).real B := by
  rw [comp_real_apply η κ x hB]
  have hi : Integrable (A.indicator fun _ => q) (κ x) := (integrable_const q).indicator hA
  have hle : ∫ y, A.indicator (fun _ => q) y ∂(κ x) ≤ ∫ y, (η y).real B ∂(κ x) := by
    refine integral_mono hi ?_ fun y => ?_
    · exact Integrable.mono' (integrable_const 1)
        (measurable_real_kernel η hB).aestronglyMeasurable
        (ae_of_all _ fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
    · by_cases hy : y ∈ A
      · rw [indicator_of_mem hy]; exact hηq y hy
      · rw [indicator_of_notMem hy]; exact measureReal_nonneg
  rw [integral_indicator_const _ hA, smul_eq_mul] at hle
  nlinarith [hp x]

end Kernel

section Product

/-- **Measurable upper sets generate the σ-algebra of `S × Z`** (product
order), for `S` a second-countable linear order with its order topology and
Borel σ-algebra and `Z` a finite linear order with measurable singletons. -/
theorem generateFrom_upperSets_prod {S Z : Type*} [LinearOrder S] [TopologicalSpace S]
    [OrderTopology S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    [LinearOrder Z] [Finite Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] :
    (inferInstance : MeasurableSpace (S × Z)) =
      MeasurableSpace.generateFrom {U | IsUpperSet U ∧ MeasurableSet U} := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun U hU => hU.2)
  have hmem : ∀ U : Set (S × Z), IsUpperSet U → MeasurableSet U →
      MeasurableSet[MeasurableSpace.generateFrom {U | IsUpperSet U ∧ MeasurableSet U}] U :=
    fun U h1 h2 => MeasurableSpace.measurableSet_generateFrom ⟨h1, h2⟩
  refine sup_le ?_ ?_
  · have hS : (inferInstance : MeasurableSpace S) = MeasurableSpace.generateFrom (range Ici) := by
      rw [BorelSpace.measurable_eq (α := S), borel_eq_generateFrom_Ici]
    calc MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)
        = MeasurableSpace.comap Prod.fst (MeasurableSpace.generateFrom (range Ici)) :=
          congrArg _ hS
      _ = MeasurableSpace.generateFrom (Set.preimage Prod.fst '' range Ici) :=
          MeasurableSpace.comap_generateFrom
      _ ≤ _ := ?_
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hmem (Prod.fst ⁻¹' Ici a) (fun p q hpq (hp : a ≤ p.1) => show a ≤ q.1 from le_trans hp hpq.1)
      (measurable_fst measurableSet_Ici)
  · rintro _ ⟨B, -, rfl⟩
    have hB : Prod.snd ⁻¹' B =
        ⋃ z ∈ B, (Prod.snd ⁻¹' Ici z \ Prod.snd ⁻¹' Ioi z : Set (S × Z)) := by
      ext p
      simp only [mem_preimage, mem_iUnion, mem_sdiff, mem_Ici, mem_Ioi, not_lt, exists_prop]
      exact ⟨fun h => ⟨p.2, h, le_rfl, le_rfl⟩,
        fun ⟨z, hz, h1, h2⟩ => le_antisymm h2 h1 ▸ hz⟩
    rw [hB]
    refine (toFinite B).measurableSet_biUnion fun z _ => ?_
    refine MeasurableSet.diff (hmem (Prod.snd ⁻¹' Ici z) ?_ ?_) (hmem (Prod.snd ⁻¹' Ioi z) ?_ ?_)
    · exact fun p q hpq (hp : z ≤ p.2) => show z ≤ q.2 from le_trans hp hpq.2
    · exact measurable_snd (toFinite _).measurableSet
    · exact fun p q hpq (hp : z < p.2) => show z < q.2 from lt_of_lt_of_le hp hpq.2
    · exact measurable_snd (toFinite _).measurableSet

end Product

end Econ
