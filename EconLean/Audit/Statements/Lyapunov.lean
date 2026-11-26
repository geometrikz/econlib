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
public import EconLean.GE.ContinuumExistence
public import EconLean.Foundations.ConvexifiedCorrespondence
public import EconLean.GE.AumannExistence
public import EconLean.GE.ApproximateEquilibrium

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

section ContinuumExistence

open Continuum ContinuumEconomy Lyapunov Function

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

theorem frozen_exists_partition_measureReal_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : Nonatomic μ) {κ : Type*} [Fintype κ] [Nonempty κ] {A : Set Ω}
    (hA : MeasurableSet A) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) (hsum : ∑ k, c k = μ.real A) :
    ∃ B : κ → Set Ω, (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ A) ∧
      Pairwise (Disjoint on B) ∧ (∀ a ∈ A, ∃ k, a ∈ B k) ∧ ∀ k, μ.real (B k) = c k :=
  exists_partition_measureReal_eq hμ hA c hc hsum

theorem frozen_exists_fin_convexComb {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hs : s.Nonempty) {v : V} (hv : v ∈ convexHull ℝ s) :
    ∃ (w : Fin (Module.finrank ℝ V + 1) → ℝ) (z : Fin (Module.finrank ℝ V + 1) → V),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = v :=
  exists_fin_convexComb hs hv

theorem frozen_isClosed_graph_convexHull {X V : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {Φ : X → Set V} {K : Set V} (hK : IsCompact K) (hsub : ∀ x, Φ x ⊆ K)
    (h : IsClosed (graph Φ)) : IsClosed (graph fun x => convexHull ℝ (Φ x)) :=
  isClosed_graph_convexHull hK hsub h

theorem frozen_demand_scaled {u : (ι → ℝ) → ℝ} {m : ℝ} (hm : 0 < m) (p ω : ι → ℝ) :
    demand (prefOf fun x => u (m⁻¹ • x)) p (cost p (m • ω)) =
      (m • ·) '' demand (prefOf u) p (cost p ω) :=
  demand_scaled hm p ω

theorem frozen_convexification_bridge [IsFiniteMeasure E.μ] (hμ : Nonatomic E.μ)
    {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (τ : Ω → T) (hτ : Measurable τ) (R : T → (ι → ℝ) → (ι → ℝ) → Prop) (ω : T → ι → ℝ)
    (hR : ∀ a, E.pref a = R (τ a)) (hω : ∀ a, E.endow a = ω (τ a))
    (p : ι → ℝ) (xbar : T → ι → ℝ)
    (hx : ∀ t, xbar t ∈ convexHull ℝ (demand (R t) p (cost p (ω t))))
    (hclear : ∑ t, E.μ.real (τ ⁻¹' {t}) • xbar t = ∑ t, E.μ.real (τ ⁻¹' {t}) • ω t) :
    ∃ x : Ω → ι → ℝ, E.IsWalrasianEquilibrium p x :=
  exists_allocation_isWalrasianEquilibrium_of_mem_convexHull hμ τ hτ R ω hR hω p xbar hx hclear

theorem frozen_continuum_existence_of_types [Nonempty ι] [IsFiniteMeasure E.μ]
    {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {τ : Ω → T} (hτ : Measurable τ)
    {u : T → (ι → ℝ) → ℝ} {ω : T → ι → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u (τ a))) (hω : ∀ a, E.endow a = ω (τ a))
    (hmass : ∀ t, 0 < E.μ.real (τ ⁻¹' {t}))
    (hu : ∀ t, Continuous (u t)) (hsq : ∀ t, StrictlyQuasiconcave (u t))
    (hmono : ∀ t, StronglyMonotone (prefOf (u t))) (hω0 : ∀ t, ω t ≠ 0)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i) :
    ∃ (p : ι → ℝ) (x : T → ι → ℝ), PositivePrices p ∧
      E.IsWalrasianEquilibrium p (fun a => x (τ a)) :=
  exists_isWalrasianEquilibrium_of_types hτ hpref hω hmass hu hsq hmono hω0 he

theorem frozen_isClosed_graph_convexHull_on {X V : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {Φ : X → Set V} {s : Set X} {K : Set V} (hK : IsCompact K) (hsub : ∀ x ∈ s, Φ x ⊆ K)
    (h : IsClosed {q : X × V | q.1 ∈ s ∧ q.2 ∈ Φ q.1}) :
    IsClosed {q : X × V | q.1 ∈ s ∧ q.2 ∈ convexHull ℝ (Φ q.1)} :=
  isClosed_graph_convexHull_on hK hsub h

theorem frozen_continuum_existence_witnesses :
    (∃ (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ), PositivePrices p ∧
      sqrtContinuum.IsWalrasianEquilibrium p (fun a => x (sqrtType a))) ∧
    (∃ x : ℝ → Fin 2 → ℝ, maxContinuum.IsWalrasianEquilibrium one2 x) ∧
    ∀ p : Fin 2 → ℝ, PositivePrices p → ∀ (c : Fin 2 → ℝ) (x : ℝ → Fin 2 → ℝ),
      x =ᵐ[maxContinuum.μ] (fun _ => c) → ¬ maxContinuum.IsWalrasianEquilibrium p x :=
  ⟨sqrtContinuum_exists_equilibrium, maxContinuum_exists_equilibrium,
    fun _ hp c _ hx => maxContinuum_no_symmetric_equilibrium hp c hx⟩

end ContinuumExistence

section AumannExistence

open Continuum ContinuumEconomy Lyapunov AumannExistence Topology Filter

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

theorem frozen_truncDemand_def (u : (ι → ℝ) → ℝ) (ω : ι → ℝ) (c m : ℝ) (q d : ι → ℝ) :
    d ∈ truncDemand u ω c m q ↔
      (d ∈ Set.Icc (0 : ι → ℝ) (fun _ => c) ∧ cost q d ≤ max (cost q ω) m) ∧
        ∀ y, (y ∈ Set.Icc (0 : ι → ℝ) (fun _ => c) ∧ cost q y ≤ max (cost q ω) m) → u y ≤ u d :=
  Iff.rfl

theorem frozen_eventually_lt_sum_of_mem_truncDemand [DecidableEq ι] {u : (ι → ℝ) → ℝ}
    (hu : Continuous u) (hmono : StronglyMonotone (prefOf u)) {m : ℝ} (hm : 0 < m)
    (ω : ι → ℝ) {p : ι → ℝ} {i : ι} (hpi : p i = 0) (B : ℝ) :
    ∀ᶠ q in 𝓝 p, ∀ c, B + 1 ≤ c → ∀ d ∈ truncDemand u ω c m q, B < ∑ j, d j :=
  eventually_lt_sum_of_mem_truncDemand hu hmono hm ω hpi B

theorem frozen_exists_convexifiedEquilibrium [Nonempty ι] [DecidableEq ι] {T : Type*}
    [Fintype T] [Nonempty T] (mass : T → ℝ) (hmass : ∀ t, 0 < mass t)
    {u : T → (ι → ℝ) → ℝ} (hu : ∀ t, Continuous (u t))
    (hmono : ∀ t, StronglyMonotone (prefOf (u t)))
    {ω : T → ι → ℝ} (hω : ∀ t, PositivePrices (ω t)) :
    ∃ (p : ι → ℝ) (xbar : T → ι → ℝ), PositivePrices p ∧
      (∀ t, xbar t ∈ convexHull ℝ (demand (prefOf (u t)) p (cost p (ω t)))) ∧
      ∑ t, mass t • xbar t = ∑ t, mass t • ω t :=
  exists_convexifiedEquilibrium mass hmass hu hmono hω

theorem frozen_continuum_existence_nonconvex [Nonempty ι] [IsFiniteMeasure E.μ]
    (hμ : Nonatomic E.μ) {T : Type*} [Fintype T] [Nonempty T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {τ : Ω → T} (hτ : Measurable τ)
    {u : T → (ι → ℝ) → ℝ} {ω : T → ι → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u (τ a))) (hω : ∀ a, E.endow a = ω (τ a))
    (hmass : ∀ t, 0 < E.μ.real (τ ⁻¹' {t}))
    (hu : ∀ t, Continuous (u t)) (hmono : ∀ t, StronglyMonotone (prefOf (u t)))
    (hωpos : ∀ t, PositivePrices (ω t)) :
    ∃ (p : ι → ℝ) (x : Ω → ι → ℝ), PositivePrices p ∧ E.IsWalrasianEquilibrium p x :=
  exists_isWalrasianEquilibrium_of_types_nonconvex E hμ hτ hpref hω hmass hu hmono hωpos

theorem frozen_aumann_existence_witness :
    (∀ x, sqContinuum.pref x = prefOf uSq) ∧ (∀ x, sqContinuum.endow x = one2) ∧
    Continuous uSq ∧ StronglyMonotone (prefOf uSq) ∧ ¬ QuasiconcaveOn ℝ (Set.Ici 0) uSq ∧
    ∃ (p : Fin 2 → ℝ) (x : ℝ → Fin 2 → ℝ), PositivePrices p ∧
      sqContinuum.IsWalrasianEquilibrium p x ∧
      ∀ c : Fin 2 → ℝ, ¬ x =ᵐ[sqContinuum.μ] fun _ => c :=
  ⟨fun _ => rfl, fun _ => rfl, continuous_uSq, stronglyMonotone_uSq, not_quasiconcaveOn_uSq,
    sqContinuum_exists_asymmetric_equilibrium⟩

theorem frozen_sqContinuum_no_symmetric_equilibrium :
    ∀ p : Fin 2 → ℝ, PositivePrices p → ∀ (c : Fin 2 → ℝ) (x : ℝ → Fin 2 → ℝ),
      x =ᵐ[sqContinuum.μ] (fun _ => c) → ¬ sqContinuum.IsWalrasianEquilibrium p x :=
  fun _ hp c _ hx => sqContinuum_no_symmetric_equilibrium hp c hx

theorem frozen_exists_pos_le_of_notMem [Nonempty ι] {U : Set (ι → ℝ)}
    (hU : ∀ p ∈ priceSimplex ι, ∀ i, p i = 0 → U ∈ 𝓝 p) :
    ∃ π > 0, ∀ q ∈ priceSimplex ι, q ∉ U → ∀ i, π ≤ q i :=
  exists_pos_le_of_notMem hU

theorem frozen_sqContinuum_def :
    (∀ x : Fin 2 → ℝ, uSq x = x 0 ^ 2 + x 1 ^ 2) ∧
      sqContinuum.μ = volume.restrict (Set.Icc (0 : ℝ) 1) ∧ one2 = (fun _ => 1) ∧
      sqContinuum.endow = (fun _ => one2) :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

end AumannExistence

section ApproxEquilibrium

open ApproxEquilibrium Continuum.ContinuumEconomy

theorem frozen_exists_counts {M : ℕ} (w : Fin (M + 1) → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (n : ℕ) :
    ∃ cnt : Fin (M + 1) → ℕ, ∑ k, cnt k = n ∧ ∀ k, |(cnt k : ℝ) - n * w k| ≤ M + 1 :=
  exists_counts w hw0 hw1 n

theorem frozen_exists_assign {N n : ℕ} (cnt : Fin N → ℕ) (h : ∑ k, cnt k = n) {V : Type*}
    [AddCommMonoid V] (g : Fin N → V) :
    ∃ f : Fin n → Fin N, ∑ j, g (f j) = ∑ k, cnt k • g k :=
  exists_assign cnt h g

theorem frozen_exists_approxEquilibrium_replica {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] {T : Type*} [Fintype T] [Nonempty T] {u : T → (ι → ℝ) → ℝ}
    (hu : ∀ t, Continuous (u t)) (hmono : ∀ t, StronglyMonotone (prefOf (u t)))
    {ω : T → ι → ℝ} (hω : ∀ t, PositivePrices (ω t)) :
    ∃ (p : ι → ℝ) (C : ℝ), PositivePrices p ∧ ∀ n : ℕ, ∃ x : T × Fin n → ι → ℝ,
      (∀ a, x a ∈ demand (prefOf (u a.1)) p (cost p (ω a.1))) ∧
      ∀ i, |∑ a : T × Fin n, x a i - ∑ a : T × Fin n, ω a.1 i| ≤ C :=
  exists_approxEquilibrium_replica hu hmono hω

theorem frozen_sqReplica_witness :
    (∃ (p : Fin 2 → ℝ) (C : ℝ), PositivePrices p ∧ ∀ n : ℕ, ∃ x : Fin 1 × Fin n → Fin 2 → ℝ,
      (∀ a, x a ∈ demand (prefOf uSq) p (cost p one2)) ∧
      ∀ i, |∑ a : Fin 1 × Fin n, x a i - ∑ _a : Fin 1 × Fin n, one2 i| ≤ C) ∧
    ∀ n : ℕ, Odd n → ∀ (p : Fin 2 → ℝ) (x : Fin 1 × Fin n → Fin 2 → ℝ),
      (∀ a, x a ∈ demand (prefOf uSq) p (cost p one2)) → ∑ a, x a ≠ ∑ _a : Fin 1 × Fin n, one2 :=
  ⟨sqReplica_exists_approxEquilibrium, fun _ hn p x hx => sqReplica_odd_no_equilibrium hn p x hx⟩

theorem frozen_mem_demand_uSq {p : Fin 2 → ℝ} {d : Fin 2 → ℝ}
    (hd : d ∈ demand (prefOf uSq) p (cost p one2)) :
    (d 1 = 0 ∧ d 0 = (p 0 + p 1) / p 0 ∧ p 0 ≤ p 1) ∨
      (d 0 = 0 ∧ d 1 = (p 0 + p 1) / p 1 ∧ p 1 ≤ p 0) :=
  mem_demand_uSq hd

theorem frozen_positivePrices_of_mem_demand_uSq {p : Fin 2 → ℝ} {w : ℝ} {d : Fin 2 → ℝ}
    (hd : d ∈ demand (prefOf uSq) p w) : PositivePrices p :=
  positivePrices_of_mem_demand_uSq hd

end ApproxEquilibrium

end Econ.Audit
