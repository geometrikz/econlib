/-
# Doeblin's theorem on a general state space: uniqueness and geometric convergence

Stokey–Lucas (SL) §11.4 (Thm 11.12, uniform-minorization case); Meyn–Tweedie Thm 16.2.4.

**Doeblin minorization.** A Markov kernel `K` satisfies the minorization
condition with constant `ε ∈ (0, 1]` and a probability measure `φ` if

  `K(x, A) ≥ ε φ(A)` for every state `x` and every measurable set `A`.

Every state then sends at least probability `ε` "the same way". Applied to an
`N`-step kernel `κ^N`, this is the uniform minorization (Meyn–Tweedie's
"uniformly ergodic" condition). It is stronger than SL's Condition D: it
implies SL's Condition M, so these results are special cases of SL Thm 11.12.
Periodic chains such as `[[0, 1], [1, 0]]` satisfy Condition D (with a unique
invariant distribution) but no power of them admits a minorization, so they
are not covered here. Existence of an invariant distribution is not part of
these statements: it comes from `exists_invariant_of_feller` (compact Feller
case) or `exists_invariant` (finite chains).

**Results.**
* `doeblin_step`: one step of `K` contracts the total-variation gap
  `sup_A (μ(A) - ν(A))` by the factor `1 - ε`.
* `doeblin_convergence`: if `π` is `K`-invariant, then from any initial
  distribution `μ`, `|μKⁿ(A) - π(A)| ≤ (1 - ε)ⁿ` for every measurable `A`
  (geometric convergence in total variation).
* `doeblin_unique` / `unique_invariant_of_pow`: the invariant distribution is
  unique. The second form applies to a kernel whose `N`-th power satisfies
  the minorization.

**Proof idea.** Write `K(x, ·) = ε φ + (1 - ε) R(x, ·)`. The `φ` part is the
same for every starting distribution, so it cancels in `μK - νK`. The
remainder integrates a function with values in `[0, 1 - ε]` against `μ - ν`.
A Hahn decomposition `P` of `μ - ν` bounds such an integral by
`(1 - ε)(μ(P) - ν(P))`, and `μ(P) - ν(P)` is the largest gap `μ(A) - ν(A)`.
-/
module

public import EconLean.Macro.DP.InvariantMeasure
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Sub

@[expose] public section

namespace Econ

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem integrable_of_bounded {ρ : Measure X} [IsFiniteMeasure ρ] {f : X → ℝ} (hf : Measurable f)
    {a b : ℝ} (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) : Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le a, le_max_left |a| |b|, ha x]
    · linarith [le_abs_self b, le_max_right |a| |b|, hb x])

/-- **Integral bound from a Hahn decomposition.** If `P` is a Hahn set for
`μ - ν` (`μ ≥ ν` inside `P`, `μ ≤ ν` outside), then every measurable `f` with
values in `[0, c]` satisfies `∫ f dμ - ∫ f dν ≤ c (μ(P) - ν(P))`. -/
theorem integral_sub_le_hahn {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {P : Set X} (hP : MeasurableSet P) (h1 : ∀ t, MeasurableSet t → t ⊆ P → ν t ≤ μ t)
    (h2 : ∀ t, MeasurableSet t → t ⊆ Pᶜ → μ t ≤ ν t) {f : X → ℝ} {c : ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfc : ∀ x, f x ≤ c) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ c * (μ.real P - ν.real P) := by
  have hint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable f ρ := fun ρ _ =>
    integrable_of_bounded hf hf0 hfc
  have hle1 : ν.restrict P ≤ μ.restrict P := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact h1 _ (ht.inter hP) Set.inter_subset_right
  have hle2 : μ.restrict Pᶜ ≤ ν.restrict Pᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact h2 _ (ht.inter hP.compl) Set.inter_subset_right
  rw [← integral_add_compl hP (hint μ), ← integral_add_compl hP (hint ν)]
  have hB : ∫ x in Pᶜ, f x ∂μ ≤ ∫ x in Pᶜ, f x ∂ν :=
    integral_mono_measure hle2 (ae_of_all _ hf0) (hint _)
  set ρ := μ.restrict P - ν.restrict P
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le _ Measure.sub_le
  have hdecomp : μ.restrict P = ρ + ν.restrict P := (Measure.sub_add_cancel_of_le hle1).symm
  have hA : ∫ x in P, f x ∂μ = ∫ x, f x ∂ρ + ∫ x in P, f x ∂ν := by
    rw [hdecomp, integral_add_measure (hint _) (hint _)]
  have hρ : ∫ x, f x ∂ρ ≤ c * ρ.real Set.univ := by
    calc ∫ x, f x ∂ρ ≤ ∫ _, c ∂ρ := integral_mono (hint _) (integrable_const c) hfc
      _ = c * ρ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hρu : ρ.real Set.univ = μ.real P - ν.real P := by
    rw [measureReal_def, Measure.sub_apply MeasurableSet.univ hle1,
      Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, ENNReal.toReal_sub_of_le (h1 P hP subset_rfl) (measure_ne_top _ _)]
    rfl
  rw [hρu] at hρ
  linarith

/-- `(K ∘ₘ ρ)(A) = ∫ K(x, A) dρ(x)`. -/
theorem comp_real_eq_integral (K : Kernel X X) [IsMarkovKernel K] (ρ : Measure X)
    [IsProbabilityMeasure ρ] {A : Set X} (hA : MeasurableSet A) :
    (K ∘ₘ ρ).real A = ∫ x, (K x).real A ∂ρ := by
  have h := integral_comp_measure (κ := K) (μ := ρ) (f := A.indicator 1)
    ((integrable_const (1 : ℝ)).indicator hA)
  rw [integral_indicator_one hA] at h
  rw [h]
  exact integral_congr_ae (ae_of_all _ fun x => integral_indicator_one hA)

/-- **One Doeblin step contracts the total-variation gap by `1 - ε`.** -/
theorem doeblin_step {K : Kernel X X} [IsMarkovKernel K] {φ : Measure X} [IsProbabilityMeasure φ]
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ K x A)
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ}
    (hc : ∀ A, MeasurableSet A → μ.real A - ν.real A ≤ c) :
    ∀ A, MeasurableSet A → (K ∘ₘ μ).real A - (K ∘ₘ ν).real A ≤ (1 - ε) * c := by
  intro A hA
  obtain ⟨P, hP, h1, h2⟩ := hahn_decomposition μ ν
  have hreal : ∀ x B, MeasurableSet B → ε * φ.real B ≤ (K x).real B := fun x B hB => by
    have := ENNReal.toReal_mono (measure_ne_top _ _) (hmin x B hB)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0] at this
  set g : X → ℝ := fun x => (K x).real A - ε * φ.real A
  have hg0 : ∀ x, 0 ≤ g x := fun x => sub_nonneg.2 (hreal x A hA)
  have hg1 : ∀ x, g x ≤ 1 - ε := fun x => by
    have h := hreal x Aᶜ hA.compl
    rw [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hA] at h
    have : φ.real A ≤ 1 := measureReal_le_one
    simp only [g]
    nlinarith
  have hgm : Measurable g := ((K.measurable_coe hA).ennreal_toReal).sub measurable_const
  have key := integral_sub_le_hahn hP h1 h2 hgm hg0 hg1
  have hKm : Measurable fun x => (K x).real A := (K.measurable_coe hA).ennreal_toReal
  have hgint : ∀ (ρ : Measure X) [IsProbabilityMeasure ρ],
      ∫ x, g x ∂ρ = (K ∘ₘ ρ).real A - ε * φ.real A := fun ρ _ => by
    rw [comp_real_eq_integral K ρ hA, integral_sub (integrable_of_bounded hKm
      (fun x => measureReal_nonneg) (fun x => measureReal_le_one)) (integrable_const _),
      integral_const, probReal_univ, one_smul]
  rw [hgint μ, hgint ν] at key
  have hcP := hc P hP
  nlinarith

/-- The distribution after `n` applications of `K`. -/
noncomputable def iterComp (K : Kernel X X) (μ : Measure X) : ℕ → Measure X
  | 0 => μ
  | n + 1 => K ∘ₘ iterComp K μ n

theorem isProbabilityMeasure_iterComp (K : Kernel X X) [IsMarkovKernel K] (μ : Measure X)
    [IsProbabilityMeasure μ] : ∀ n, IsProbabilityMeasure (iterComp K μ n)
  | 0 => by unfold iterComp; infer_instance
  | n + 1 => by
    have := isProbabilityMeasure_iterComp K μ n
    unfold iterComp; infer_instance

/-- **Doeblin's theorem: geometric convergence** (SL Thm 11.12, minorization case; Meyn–Tweedie
16.2.4). Under the minorization `K(x, ·) ≥ ε φ`, every initial distribution
converges to the invariant distribution `π` in total variation at rate
`(1 - ε)ⁿ`. -/
theorem doeblin_convergence {K : Kernel X X} [IsMarkovKernel K] {φ : Measure X}
    [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ K x A)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : Kernel.Invariant K π)
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    |(iterComp K μ n).real A - π.real A| ≤ (1 - ε) ^ n := by
  have hπ' : K ∘ₘ π = π := hπ
  have main : ∀ n, (∀ A, MeasurableSet A → (iterComp K μ n).real A - π.real A ≤ (1 - ε) ^ n) ∧
      (∀ A, MeasurableSet A → π.real A - (iterComp K μ n).real A ≤ (1 - ε) ^ n) := by
    intro n
    induction n with
    | zero =>
      have := isProbabilityMeasure_iterComp K μ 0
      refine ⟨fun A _ => ?_, fun A _ => ?_⟩ <;> rw [pow_zero] <;>
        linarith [measureReal_le_one (μ := iterComp K μ 0) (s := A),
          measureReal_nonneg (μ := iterComp K μ 0) (s := A),
          measureReal_le_one (μ := π) (s := A), measureReal_nonneg (μ := π) (s := A)]
    | succ n ih =>
      have := isProbabilityMeasure_iterComp K μ n
      refine ⟨fun A hA => ?_, fun A hA => ?_⟩
      · have h := doeblin_step hε0 hε1 hmin ih.1 A hA
        rw [hπ'] at h
        rw [pow_succ']
        exact h
      · have h := doeblin_step hε0 hε1 hmin (μ := π) (ν := iterComp K μ n) ih.2 A hA
        rw [hπ'] at h
        rw [pow_succ']
        exact h
  rw [abs_le]
  exact ⟨by linarith [(main n).2 A hA], (main n).1 A hA⟩

/-- **Doeblin's theorem: uniqueness.** Under the minorization with `ε > 0`,
there is at most one invariant probability distribution. -/
theorem doeblin_unique {K : Kernel X X} [IsMarkovKernel K] {φ : Measure X}
    [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ K x A)
    {π π' : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant K π) (hπ' : Kernel.Invariant K π') : π' = π := by
  have hiter : ∀ n, iterComp K π' n = π' := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => show K ∘ₘ iterComp K π' n = π'; rw [ih]; exact hπ'
  ext A hA
  have hb : ∀ n, |π'.real A - π.real A| ≤ (1 - ε) ^ n := fun n => by
    simpa [hiter n] using doeblin_convergence hε0.le hε1 hmin hπ π' n hA
  have hlim : Tendsto (fun n : ℕ => (1 - ε) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h0 : |π'.real A - π.real A| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hb)
  have : π'.real A = π.real A := by linarith [abs_nonneg (π'.real A - π.real A), abs_le.1 h0]
  rwa [measureReal_def, measureReal_def, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (measure_ne_top _ _)] at this

theorem isMarkovKernel_pow (κ : Kernel X X) [IsMarkovKernel κ] :
    ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel Kernel.id)
  | n + 1 => by
    have := isMarkovKernel_pow κ n
    rw [pow_succ]
    exact (inferInstance : IsMarkovKernel ((κ ^ n) ∘ₖ κ))

theorem invariant_pow {κ : Kernel X X} {π : Measure X} (hπ : Kernel.Invariant κ π) :
    ∀ n : ℕ, Kernel.Invariant (κ ^ n) π
  | 0 => by
    rw [pow_zero]
    exact (Measure.id_comp (μ := π) : Kernel.id ∘ₘ π = π)
  | n + 1 => by
    rw [pow_succ]
    exact (invariant_pow hπ n).comp hπ

/-- **Uniqueness under an `N`-step minorization** (SL Condition D in
minorization form): if `κ^N(x, ·) ≥ ε φ` for all `x`, then `κ` has at most one
invariant probability distribution. -/
theorem unique_invariant_of_pow {κ : Kernel X X} [IsMarkovKernel κ] {N : ℕ} {φ : Measure X}
    [IsProbabilityMeasure φ] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmin : ∀ x A, MeasurableSet A → ENNReal.ofReal ε * φ A ≤ (κ ^ N) x A)
    {π π' : Measure X} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π') : π' = π := by
  have := isMarkovKernel_pow κ N
  exact doeblin_unique hε0 hε1 hmin (invariant_pow hπ N) (invariant_pow hπ' N)

end Econ
