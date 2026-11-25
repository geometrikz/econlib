/-
# Frozen statements: nonatomic measures, Lyapunov's theorem, Aumann core equivalence

Headline statements of `Foundations/Measure/*.lean` (and later the continuum
economy files), copied after context-isolated adversarial review. Each theorem
is closed by the library theorem and each definition pinned by `Iff.rfl`, so if
a library statement changes this file stops compiling. Do not edit a statement
here without a new review.
-/
module

public import EconLean.Foundations.Measure.Lyapunov
public import EconLean.GE.ContinuumEconomy
public import EconLean.Foundations.Measure.LyapunovIntegral
public import EconLean.GE.AumannCore

@[expose] public section

namespace Econ.Audit

open MeasureTheory

section Sierpinski

open Lyapunov

theorem frozen_nonatomic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    Nonatomic μ ↔
      ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s :=
  Iff.rfl

theorem frozen_exists_subset_measureReal_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (hμ : Nonatomic μ) {A : Set Ω} (hA : MeasurableSet A)
    {c : ℝ} (hc0 : 0 ≤ c) (hcA : c ≤ μ.real A) :
    ∃ B ⊆ A, MeasurableSet B ∧ μ.real B = c :=
  exists_subset_measureReal_eq hμ hA hc0 hcA

theorem frozen_exists_partition_measureReal_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : Nonatomic μ) {δ : ℝ} (hδ : 0 < δ)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∃ (N : ℕ) (P : Fin N → Set Ω), (∀ i, MeasurableSet (P i)) ∧
      Pairwise (Function.onFun Disjoint P) ∧ (⋃ i, P i) = A ∧ ∀ i, μ.real (P i) ≤ δ :=
  exists_partition_measureReal_le hμ hδ hA

theorem frozen_nonatomic_sum {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (ν : ι → Measure Ω) [∀ i, IsFiniteMeasure (ν i)] (h : ∀ i, Nonatomic (ν i)) :
    Nonatomic (∑ i, ν i) :=
  nonatomic_sum ν h

theorem frozen_nonatomic_of_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    {lam ν : Measure Ω} [IsFiniteMeasure lam] [IsFiniteMeasure ν] (hlam : Nonatomic lam)
    (hac : ν ≪ lam) : Nonatomic ν :=
  hlam.of_absolutelyContinuous hac

end Sierpinski

section Lyapunov

open Lyapunov

theorem frozen_lyapunov_range {Ω η : Type*} [MeasurableSpace Ω]
    (μ : η → Measure Ω) (v : η → ℝ) :
    v ∈ Lyapunov.range μ ↔ ∃ B, MeasurableSet B ∧ v = fun i => (μ i).real B := Iff.rfl

theorem frozen_exists_subset_measureReal_eq_smul {Ω η : Type*} [MeasurableSpace Ω]
    [Fintype η] {μ : η → Measure Ω} [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Nonatomic (μ i))
    {A : Set Ω} (hA : MeasurableSet A) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B ⊆ A, MeasurableSet B ∧ ∀ i, (μ i).real B = t * (μ i).real A :=
  exists_subset_measureReal_eq_smul hμ hA ht0 ht1

theorem frozen_convex_range {Ω η : Type*} [MeasurableSpace Ω] [Fintype η]
    {μ : η → Measure Ω} [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Nonatomic (μ i)) :
    Convex ℝ (Lyapunov.range μ) :=
  convex_range hμ

theorem frozen_exists_few_fractional {ι η : Type*} [Fintype ι] [Fintype η] (w : ι → η → ℝ)
    (d : ι → ℝ) (hd : ∀ l, 0 ≤ d l ∧ d l ≤ 1) :
    ∃ d' : ι → ℝ, (∀ l, 0 ≤ d' l ∧ d' l ≤ 1) ∧ ∑ l, d' l • w l = ∑ l, d l • w l ∧
      (Finset.univ.filter fun l => 0 < d' l ∧ d' l < 1).card ≤ Fintype.card η :=
  exists_few_fractional w d hd

end Lyapunov

section LyapunovIntegral

open Lyapunov

variable {Ω η : Type*} [MeasurableSpace Ω] [Fintype η]

theorem frozen_exists_subset_setIntegral_eq_smul {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) {f : Ω → η → ℝ} (hf : Integrable f lam) {A : Set Ω}
    (hA : MeasurableSet A) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B ⊆ A, MeasurableSet B ∧ ∫ a in B, f a ∂lam = t • ∫ a in A, f a ∂lam :=
  exists_subset_setIntegral_eq_smul hlam hf hA ht0 ht1

theorem frozen_integralRange (lam : Measure Ω) (f : Ω → η → ℝ) (v : η → ℝ) :
    v ∈ integralRange lam f ↔ ∃ B, MeasurableSet B ∧ v = ∫ a in B, f a ∂lam := Iff.rfl

theorem frozen_convex_integralRange {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) {f : Ω → η → ℝ} (hf : Integrable f lam) :
    Convex ℝ (integralRange lam f) :=
  convex_integralRange hlam hf

theorem frozen_exists_subset_piecewise_setIntegral_eq {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) {g₁ g₂ : Ω → η → ℝ} (h₁ : Integrable g₁ lam) (h₂ : Integrable g₂ lam)
    {A : Set Ω} (hA : MeasurableSet A) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ B ⊆ A, MeasurableSet B ∧ ∀ [DecidablePred (· ∈ B)],
      ∫ a in A, B.piecewise g₁ g₂ a ∂lam =
        t • ∫ a in A, g₁ a ∂lam + (1 - t) • ∫ a in A, g₂ a ∂lam :=
  exists_subset_piecewise_setIntegral_eq hlam h₁ h₂ hA ht0 ht1

theorem frozen_selectionIntegral (lam : Measure Ω) (F : Ω → Set (η → ℝ)) (v : η → ℝ) :
    v ∈ selectionIntegral lam F ↔
      ∃ g : Ω → η → ℝ, Integrable g lam ∧ (∀ᵐ a ∂lam, g a ∈ F a) ∧ v = ∫ a, g a ∂lam :=
  Iff.rfl

theorem frozen_convex_selectionIntegral {lam : Measure Ω} [IsFiniteMeasure lam]
    (hlam : Nonatomic lam) (F : Ω → Set (η → ℝ)) : Convex ℝ (selectionIntegral lam F) :=
  convex_selectionIntegral hlam F

theorem frozen_nonatomic_volume_Icc :
    Nonatomic (volume.restrict (Set.Icc (0 : ℝ) 1)) := nonatomic_volume_Icc

end LyapunovIntegral

section ContinuumEconomy

open Continuum ContinuumEconomy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

theorem frozen_continuum_feasible (x : Ω → ι → ℝ) :
    E.Feasible x ↔
      Integrable x E.μ ∧ (∀ᵐ a ∂E.μ, 0 ≤ x a) ∧ ∫ a, x a ∂E.μ = ∫ a, E.endow a ∂E.μ :=
  Iff.rfl

theorem frozen_continuum_blocks (S : Set Ω) (x : Ω → ι → ℝ) :
    E.Blocks S x ↔ MeasurableSet S ∧ 0 < E.μ S ∧ ∃ y : Ω → ι → ℝ, IntegrableOn y S E.μ ∧
      (∀ᵐ a ∂E.μ, a ∈ S → 0 ≤ y a ∧ P (E.pref a) (y a) (x a)) ∧
      ∫ a in S, y a ∂E.μ = ∫ a in S, E.endow a ∂E.μ :=
  Iff.rfl

theorem frozen_continuum_inCore (x : Ω → ι → ℝ) :
    E.InCore x ↔ E.Feasible x ∧ ∀ S, ¬ E.Blocks S x := Iff.rfl

theorem frozen_continuum_isWalrasianEquilibrium (p : ι → ℝ) (x : Ω → ι → ℝ) :
    E.IsWalrasianEquilibrium p x ↔
      E.Feasible x ∧ ∀ᵐ a ∂E.μ, x a ∈ demand (E.pref a) p (cost p (E.endow a)) :=
  Iff.rfl

theorem frozen_continuum_walrasian_inCore {p : ι → ℝ} {x : Ω → ι → ℝ}
    (h : E.IsWalrasianEquilibrium p x) : E.InCore x :=
  h.inCore

theorem frozen_linContinuum_witnesses :
    linContinuum.InCore linContinuum.endow ∧ linContinuum.Blocks (Set.Icc 0 1) 0 :=
  ⟨linContinuum_inCore, linContinuum_blocks_zero⟩

end ContinuumEconomy

section AumannCore

open Continuum ContinuumEconomy Lyapunov Filter Topology

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

theorem frozen_aumann_core_walrasian [Nonempty ι] {x : Ω → ι → ℝ} (hx : E.InCore x)
    [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i)
    (hrat : ∀ᵐ a ∂E.μ, Rational (E.pref a))
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hcont : ∀ᵐ a ∂E.μ, ∀ z, 0 ≤ z → P (E.pref a) z (x a) →
      ∀ᶠ w in 𝓝 z, 0 ≤ w → P (E.pref a) w (x a))
    (hmeas : ∀ y : Ω → ι → ℝ, AEStronglyMeasurable y E.μ →
      NullMeasurableSet {a | P (E.pref a) (y a) (x a)} E.μ) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ E.IsWalrasianEquilibrium p x :=
  hx.isWalrasianEquilibrium hμ he hrat hmono hcont hmeas

theorem frozen_aumann_core_equivalence [Nonempty ι] [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i)
    (hrat : ∀ᵐ a ∂E.μ, Rational (E.pref a))
    (hmono : ∀ᵐ a ∂E.μ, StronglyMonotone (E.pref a))
    (hcont : ∀ᵐ a ∂E.μ, ContinuousPref (E.pref a))
    (hR : MeasurableSet {q : Ω × (ι → ℝ) × (ι → ℝ) | P (E.pref q.1) q.2.1 q.2.2})
    (x : Ω → ι → ℝ) :
    E.InCore x ↔ ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ E.IsWalrasianEquilibrium p x :=
  inCore_iff_of_continuousPref hμ he hrat hmono hcont hR x

theorem frozen_aumann_witnesses (x : ℝ → Fin 2 → ℝ) :
    (linContinuum.InCore x ↔
      ∃ p : Fin 2 → ℝ, (∀ i, 0 < p i) ∧ linContinuum.IsWalrasianEquilibrium p x) ∧
    (bumpContinuum.InCore x ↔
      ∃ p : Fin 2 → ℝ, (∀ i, 0 < p i) ∧ bumpContinuum.IsWalrasianEquilibrium p x) ∧
    ∀ a, ¬ ConvexPref (bumpContinuum.pref a) :=
  ⟨linContinuum_inCore_iff x, bumpContinuum_inCore_iff x, bumpContinuum_not_convexPref⟩

end AumannCore

end Econ.Audit
