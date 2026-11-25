/-
# Continuum economies with finitely many types: equilibria via convexification

**The economics.** Aumann (1964) showed that in a nonatomic continuum economy
the core is the set of Walrasian allocations (`GE/AumannCore.lean`); Aumann
(1966) showed that equilibria exist **without convexity of preferences**,
because averaging over a nonatomic population convexifies aggregate demand.
This file proves the measure-theoretic heart of that insight for economies with
finitely many types, and a (convex-case) existence theorem.

**1. Splitting a population.** `Lyapunov.exists_partition_measureReal_eq` splits
a measurable set of traders into finitely many disjoint measurable pieces of
prescribed masses `cₖ ≥ 0` summing to `μ(A)` (iterated Sierpiński).

**2. The convexification bridge** (the continuum-specific step).
`exists_allocation_isWalrasianEquilibrium_of_mem_convexHull`: with finitely many
types and `μ` nonatomic, if at prices `p` each type `t` has a mean bundle
`x̄ t ∈ conv (demand)` and the mass-weighted means clear the market, then `p` is
an equilibrium price of the continuum economy. Each type's traders are split
into groups of the right masses, each group consuming one demanded bundle, so
no individual needs to hold a convex mixture. No convexity, monotonicity or
mass positivity is assumed. The witness `maxContinuum_*` shows the splitting is
necessary: with the non-convex utility `max(x₀, x₁)` and one type, no
type-constant allocation (the form the convex-case theorem below produces) is an
equilibrium at positive prices, yet splitting the type gives one.

**3. Absorbing masses (convex case).** `demand_scaled`: a consumer with utility
`x ↦ u (m⁻¹ x)` and endowment `m ω` demands `m` times what `u, ω` demands (a
change of units). Hence mass-weighted clearing is ordinary clearing in a finite
auxiliary economy over the types, and `exists_isWalrasianEquilibrium_of_types`
gives existence for finitely many types of **strictly convex** (strictly
quasiconcave) preferences, with every trader of a type consuming the same
bundle. This is a reduction to the finite theorem (MWG 17.B.2 + 17.C.1) and does
not use nonatomicity.

**Scope.** Aumann's (1966) theorem itself, without convexity, needs a Kakutani
argument producing `x̄ t ∈ conv (demand)` with clearing; the closed-graph
lemmas for convexified correspondences it requires are in
`Foundations/ConvexifiedCorrespondence.lean`, but the fixed-point step is not
formalised here. A measurable preference map (infinitely many types) is also not
covered.
-/
module

public import EconLean.GE.AumannCore
public import Mathlib.Analysis.Convex.Caratheodory
public import EconLean.GE.ExistencePreferences

@[expose] public section

noncomputable section

namespace Econ

namespace Lyapunov

open MeasureTheory Set Function

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Splitting a set by prescribed masses** (finite nonatomic `μ`): if
`c₀, …, cₙ ≥ 0` sum to `μ(A)`, then `A` is partitioned into measurable pieces with
`μ(Bₖ) = cₖ`. -/
theorem exists_partition_measureReal_eq_fin (hμ : Nonatomic μ) :
    ∀ (n : ℕ) {A : Set Ω}, MeasurableSet A → ∀ c : Fin (n + 1) → ℝ, (∀ k, 0 ≤ c k) →
      ∑ k, c k = μ.real A →
      ∃ B : Fin (n + 1) → Set Ω, (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ A) ∧
        Pairwise (Disjoint on B) ∧ (∀ a ∈ A, ∃ k, a ∈ B k) ∧ ∀ k, μ.real (B k) = c k := by
  intro n
  induction n with
  | zero =>
    intro A hA c _ hsum
    refine ⟨fun _ => A, fun _ => hA, fun _ => subset_rfl, fun i j hij => ?_,
      fun a ha => ⟨0, ha⟩, fun k => ?_⟩
    · exact absurd (Fin.fin_one_eq_zero i ▸ Fin.fin_one_eq_zero j ▸ rfl) hij
    · rw [Fin.fin_one_eq_zero k, ← hsum]; simp
  | succ n ih =>
    intro A hA c hc hsum
    rw [Fin.sum_univ_succ] at hsum
    have hrest : 0 ≤ ∑ k : Fin (n + 1), c k.succ := Finset.sum_nonneg fun k _ => hc _
    obtain ⟨B0, hB0A, hB0, hμB0⟩ :=
      exists_subset_measureReal_eq hμ hA (hc 0) (by linarith)
    obtain ⟨B', hB'm, hB'A, hB'd, hB'cov, hμB'⟩ := ih (hA.diff hB0) (fun k => c k.succ)
      (fun k => hc _) (by rw [measureReal_sdiff hB0A hB0, hμB0]; linarith)
    refine ⟨Fin.cons B0 B', fun k => ?_, fun k => ?_, ?_, ?_, fun k => ?_⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hB0
      · simpa using hB'm k
    · refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hB0A
      · simpa using (hB'A k).trans sdiff_subset
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [onFun, Fin.cons_zero, Fin.cons_succ]
          exact Set.disjoint_left.2 fun a ha hb => (Set.mem_sdiff _ |>.1 (hB'A j hb)).2 ha
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [onFun, Fin.cons_zero, Fin.cons_succ]
          exact Set.disjoint_left.2 fun a ha hb => (Set.mem_sdiff _ |>.1 (hB'A i ha)).2 hb
        | succ j =>
          simp only [onFun, Fin.cons_succ]
          exact hB'd fun h => hij (by rw [h])
    · intro a ha
      by_cases h0 : a ∈ B0
      · exact ⟨0, by simpa using h0⟩
      · obtain ⟨k, hk⟩ := hB'cov a ⟨ha, h0⟩
        exact ⟨k.succ, by simpa using hk⟩
    · refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hμB0
      · simpa using hμB' k

/-- **Splitting a set by prescribed masses**, for any nonempty finite index. -/
theorem exists_partition_measureReal_eq (hμ : Nonatomic μ) {κ : Type*} [Fintype κ]
    [Nonempty κ] {A : Set Ω} (hA : MeasurableSet A) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hsum : ∑ k, c k = μ.real A) :
    ∃ B : κ → Set Ω, (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ A) ∧
      Pairwise (Disjoint on B) ∧ (∀ a ∈ A, ∃ k, a ∈ B k) ∧ ∀ k, μ.real (B k) = c k := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card κ = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : κ ≃ Fin (n + 1) := (Fintype.equivFin κ).trans (finCongr hn)
  obtain ⟨B, hBm, hBA, hBd, hBcov, hμB⟩ := exists_partition_measureReal_eq_fin hμ n hA
    (c ∘ e.symm) (fun k => hc _) (by rw [← hsum]; exact e.symm.sum_comp c)
  refine ⟨B ∘ e, fun k => hBm _, fun k => hBA _, fun i j hij => hBd (e.injective.ne hij),
    fun a ha => ?_, fun k => by simp [hμB]⟩
  obtain ⟨k, hk⟩ := hBcov a ha
  exact ⟨e.symm k, by simpa using hk⟩

end Lyapunov
namespace Continuum
namespace ContinuumEconomy

open MeasureTheory Set Function Filter Lyapunov

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {E : ContinuumEconomy Ω ι}


/-! ### Rescaling a consumer -/

omit [MeasurableSpace Ω] in
/-- **Rescaling a utility rescales demand**: the consumer with utility
`x ↦ u (m⁻¹ x)` and endowment `m ω` demands exactly `m` times what the consumer
with utility `u` and endowment `ω` demands. This is how the masses of a
continuum of types are absorbed into a finite auxiliary economy. -/
theorem demand_scaled {u : (ι → ℝ) → ℝ} {m : ℝ} (hm : 0 < m) (p ω : ι → ℝ) :
    demand (prefOf fun x => u (m⁻¹ • x)) p (cost p (m • ω)) =
      (m • ·) '' demand (prefOf u) p (cost p ω) := by
  have hbud : ∀ y : ι → ℝ, y ∈ budgetSet p (cost p (m • ω)) ↔
      m⁻¹ • y ∈ budgetSet p (cost p ω) := by
    intro y
    simp only [budgetSet, mem_ofPred_eq, cost_smul_right]
    have hinv : 0 < m⁻¹ := inv_pos.2 hm
    constructor
    · rintro ⟨h0, hc⟩
      refine ⟨fun i => ?_, ?_⟩
      · show (0:ℝ) ≤ m⁻¹ * y i
        exact mul_nonneg hinv.le (h0 i)
      · calc m⁻¹ * cost p y ≤ m⁻¹ * (m * cost p ω) := by nlinarith
          _ = cost p ω := by field_simp
    · rintro ⟨h0, hc⟩
      refine ⟨fun i => ?_, ?_⟩
      · have h : (0:ℝ) ≤ m⁻¹ * y i := h0 i
        show (0:ℝ) ≤ y i
        nlinarith
      · show cost p y ≤ m * cost p ω
        have := mul_le_mul_of_nonneg_left hc hm.le
        rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at this
        exact this
  ext y
  simp only [demand, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hy, hopt⟩
    refine ⟨m⁻¹ • y, ⟨(hbud y).1 hy, fun z hz => ?_⟩, by rw [smul_inv_smul₀ hm.ne']⟩
    have h := hopt (m • z) ((hbud (m • z)).2 (by rwa [inv_smul_smul₀ hm.ne']))
    show u z ≤ u (m⁻¹ • y)
    have h' : u (m⁻¹ • (m • z)) ≤ u (m⁻¹ • y) := h
    rwa [inv_smul_smul₀ hm.ne'] at h'
  · rintro ⟨x, ⟨hx, hopt⟩, rfl⟩
    refine ⟨(hbud (m • x)).2 (by rwa [inv_smul_smul₀ hm.ne']), fun z hz => ?_⟩
    show u (m⁻¹ • z) ≤ u (m⁻¹ • (m • x))
    rw [inv_smul_smul₀ hm.ne']
    exact hopt _ ((hbud z).1 hz)

omit [Fintype ι] in
/-- Rescaling preserves strict quasiconcavity. -/
theorem strictlyQuasiconcave_scaled {u : (ι → ℝ) → ℝ} {m : ℝ} (hm : 0 < m)
    (hu : StrictlyQuasiconcave u) : StrictlyQuasiconcave fun x => u (m⁻¹ • x) := by
  intro x y hx hy hne t ht ht1
  have hinv : 0 < m⁻¹ := inv_pos.2 hm
  have hne' : m⁻¹ • x ≠ m⁻¹ • y := fun h => hne (by
    have := congrArg (fun z => m • z) h
    rwa [smul_inv_smul₀ hm.ne', smul_inv_smul₀ hm.ne'] at this)
  have h := hu (m⁻¹ • x) (m⁻¹ • y)
    (fun i => show (0:ℝ) ≤ m⁻¹ * x i from mul_nonneg hinv.le (hx i))
    (fun i => show (0:ℝ) ≤ m⁻¹ * y i from mul_nonneg hinv.le (hy i)) hne' t ht ht1
  show min (u (m⁻¹ • x)) (u (m⁻¹ • y)) < u (m⁻¹ • (t • x + (1 - t) • y))
  rwa [smul_add, smul_comm m⁻¹ t, smul_comm m⁻¹ (1 - t)]

omit [Fintype ι] in
/-- Rescaling preserves strong monotonicity. -/
theorem stronglyMonotone_scaled {u : (ι → ℝ) → ℝ} {m : ℝ} (hm : 0 < m)
    (hu : StronglyMonotone (prefOf u)) : StronglyMonotone (prefOf fun x => u (m⁻¹ • x)) := by
  intro x y hx hxy hne
  have hinv : 0 < m⁻¹ := inv_pos.2 hm
  have hne' : m⁻¹ • x ≠ m⁻¹ • y := fun h => hne (by
    have := congrArg (fun z => m • z) h
    rwa [smul_inv_smul₀ hm.ne', smul_inv_smul₀ hm.ne'] at this)
  exact hu (m⁻¹ • x) (m⁻¹ • y)
    (fun i => show (0:ℝ) ≤ m⁻¹ * x i from mul_nonneg hinv.le (hx i))
    (fun i => show m⁻¹ * x i ≤ m⁻¹ * y i from mul_le_mul_of_nonneg_left (hxy i) hinv.le)
    hne'

omit [MeasurableSpace Ω] [Fintype ι] in
/-- A function of the type alone is a finite sum of indicators. -/
theorem comp_type_eq_sum {T : Type*} [Fintype T] (τ : Ω → T) (f : T → ι → ℝ) :
    (fun a => f (τ a)) = fun a => ∑ t, (τ ⁻¹' {t}).indicator (fun _ => f t) a := by
  classical
  funext a
  rw [Finset.sum_eq_single (τ a) (fun t _ ht => indicator_of_notMem
    (by simpa [eq_comm] using ht) _) (by simp), indicator_of_mem (by simp)]

/-- A function of the type alone is integrable. -/
theorem integrable_comp_type {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [IsFiniteMeasure E.μ] {τ : Ω → T} (hτ : Measurable τ)
    (f : T → ι → ℝ) : Integrable (fun a => f (τ a)) E.μ := by
  rw [comp_type_eq_sum τ f]
  exact integrable_finsetSum _ fun t _ =>
    (integrable_const (f t)).indicator (hτ (measurableSet_singleton t))

/-- The integral of a function of the type alone is the mass-weighted sum of its
values. -/
theorem integral_comp_type {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [IsFiniteMeasure E.μ] {τ : Ω → T} (hτ : Measurable τ)
    (f : T → ι → ℝ) : ∫ a, f (τ a) ∂E.μ = ∑ t, E.μ.real (τ ⁻¹' {t}) • f t := by
  have hfib : ∀ t, MeasurableSet (τ ⁻¹' {t}) := fun t => hτ (measurableSet_singleton t)
  rw [comp_type_eq_sum τ f,
    integral_finsetSum _ fun t _ => (integrable_const (f t)).indicator (hfib t)]
  exact Finset.sum_congr rfl fun t _ => by rw [integral_indicator_const _ (hfib t)]

/-- The aggregate endowment of a finitely-typed economy is the mass-weighted sum
of the types' endowments. -/
theorem integral_endow_eq_sum {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [IsFiniteMeasure E.μ] {τ : Ω → T} (hτ : Measurable τ)
    {ω : T → ι → ℝ} (hω : ∀ a, E.endow a = ω (τ a)) :
    ∫ a, E.endow a ∂E.μ = ∑ t, E.μ.real (τ ⁻¹' {t}) • ω t := by
  rw [show E.endow = fun a => ω (τ a) from funext hω]
  exact integral_comp_type hτ ω

/-- **Convexification bridge** (the splitting step of Aumann's 1966 proof). Let the economy have finitely many
types `τ : Ω → T`, with trader `a` having preference `R (τ a)` and endowment
`ω (τ a)`, and let `μ` be finite and nonatomic. If at prices `p` each type `t`
has a mean bundle `x̄ t` in the **convex hull** of its demand, and these clear the
market on aggregate, `∑ₜ μ(τ⁻¹ t) x̄ t = ∑ₜ μ(τ⁻¹ t) ω t`, then `p` supports a
Walrasian equilibrium of the continuum economy: split each type's traders into
groups of the right masses and give each group one demanded bundle. -/
theorem exists_allocation_isWalrasianEquilibrium_of_mem_convexHull [IsFiniteMeasure E.μ]
    (hμ : Nonatomic E.μ) {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (τ : Ω → T) (hτ : Measurable τ)
    (R : T → (ι → ℝ) → (ι → ℝ) → Prop) (ω : T → ι → ℝ)
    (hR : ∀ a, E.pref a = R (τ a)) (hω : ∀ a, E.endow a = ω (τ a))
    (p : ι → ℝ) (xbar : T → ι → ℝ)
    (hx : ∀ t, xbar t ∈ convexHull ℝ (demand (R t) p (cost p (ω t))))
    (hclear : ∑ t, E.μ.real (τ ⁻¹' {t}) • xbar t = ∑ t, E.μ.real (τ ⁻¹' {t}) • ω t) :
    ∃ x : Ω → ι → ℝ, E.IsWalrasianEquilibrium p x := by
  classical
  choose κ hκ z w hz _ hw0 hw1 hwz using fun t => eq_pos_convex_span_of_mem_convexHull (hx t)
  have hne : ∀ t, Nonempty (κ t) := fun t => by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hw1 t
    simp at this
  have hfib : ∀ t, MeasurableSet (τ ⁻¹' {t}) := fun t => hτ (measurableSet_singleton t)
  choose B hBm hBA hBd hBcov hμB using fun t =>
    exists_partition_measureReal_eq hμ (hfib t) (fun k => w t k * E.μ.real (τ ⁻¹' {t}))
      (fun k => mul_nonneg (hw0 t k).le measureReal_nonneg)
      (by rw [← Finset.sum_mul, hw1 t, one_mul])
  -- index all pieces by `σ = Σ t, κ t`
  let Bσ : (Σ t, κ t) → Set Ω := fun s => B s.1 s.2
  let zσ : (Σ t, κ t) → ι → ℝ := fun s => z s.1 s.2
  have hBσm : ∀ s, MeasurableSet (Bσ s) := fun s => hBm s.1 s.2
  have hdisj : Pairwise (Disjoint on Bσ) := by
    rintro ⟨t, k⟩ ⟨t', k'⟩ hne'
    by_cases ht : t = t'
    · subst ht
      have hk : k ≠ k' := fun h => hne' (by rw [h])
      exact hBd t hk
    · refine Set.disjoint_left.2 fun a ha hb => ht ?_
      have h1 : τ a = t := hBA t k ha
      have h2 : τ a = t' := hBA t' k' hb
      rw [← h1, ← h2]
  set x : Ω → ι → ℝ := fun a => ∑ s, (Bσ s).indicator (fun _ => zσ s) a with hxdef
  have hxeq : ∀ s, ∀ a ∈ Bσ s, x a = zσ s := by
    intro s a ha
    simp only [hxdef]
    rw [Finset.sum_eq_single s (fun s' _ hs' => indicator_of_notMem
      (Set.disjoint_left.1 (hdisj hs'.symm) ha) _) (by simp), indicator_of_mem ha]
  have hcov : ∀ a, ∃ s, a ∈ Bσ s := fun a => by
    obtain ⟨k, hk⟩ := hBcov (τ a) a rfl
    exact ⟨⟨τ a, k⟩, hk⟩
  have hdem : ∀ a, x a ∈ demand (E.pref a) p (cost p (E.endow a)) := by
    intro a
    obtain ⟨⟨t, k⟩, hs⟩ := hcov a
    have ht : τ a = t := hBA t k hs
    rw [hxeq _ a hs, hR, hω, ht]
    exact hz t (Set.mem_range_self k)
  have hxint : Integrable x E.μ :=
    integrable_finsetSum _ fun s _ => (integrable_const (zσ s)).indicator (hBσm s)
  have hEint : ∫ a, E.endow a ∂E.μ = ∑ t, E.μ.real (τ ⁻¹' {t}) • ω t :=
    integral_endow_eq_sum hτ hω
  have hXint : ∫ a, x a ∂E.μ = ∑ t, E.μ.real (τ ⁻¹' {t}) • xbar t := by
    rw [hxdef, integral_finsetSum _ fun s _ => (integrable_const (zσ s)).indicator (hBσm s)]
    simp_rw [integral_indicator_const _ (hBσm _)]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Bσ, zσ, hμB, ← hwz t, Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun k _ => by ring_nf
  refine ⟨x, ⟨hxint, ae_of_all _ fun a => (hdem a).1.1, by rw [hXint, hEint, hclear]⟩,
    ae_of_all _ hdem⟩

/-! ### Existence of equilibrium with finitely many types -/

/-- **Existence of a Walrasian equilibrium in a continuum economy with finitely
many types and strictly convex preferences**, by reduction to a finite economy
(nonatomicity is not needed). Traders come in finitely
many types of positive mass; each type has a continuous, strictly quasiconcave
utility representing strongly monotone preferences, and a nonzero endowment,
with strictly positive aggregate endowment. Then an equilibrium exists at
strictly positive prices.

The masses are absorbed into a **finite auxiliary economy** whose type-`t`
consumer has utility `x ↦ u t (mₜ⁻¹ x)` and endowment `mₜ ω t`: by
`demand_scaled` its demand is `mₜ` times type `t`'s, so clearing in the
auxiliary economy is exactly mass-weighted clearing here; all traders of a type
consume the same bundle. -/
theorem exists_isWalrasianEquilibrium_of_types [Nonempty ι] [IsFiniteMeasure E.μ]
    {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] {τ : Ω → T} (hτ : Measurable τ)
    {u : T → (ι → ℝ) → ℝ} {ω : T → ι → ℝ}
    (hpref : ∀ a, E.pref a = prefOf (u (τ a))) (hω : ∀ a, E.endow a = ω (τ a))
    (hmass : ∀ t, 0 < E.μ.real (τ ⁻¹' {t}))
    (hu : ∀ t, Continuous (u t)) (hsq : ∀ t, StrictlyQuasiconcave (u t))
    (hmono : ∀ t, StronglyMonotone (prefOf (u t))) (hω0 : ∀ t, ω t ≠ 0)
    (he : ∀ i, 0 < (∫ a, E.endow a ∂E.μ) i) :
    ∃ (p : ι → ℝ) (x : T → ι → ℝ), PositivePrices p ∧
      E.IsWalrasianEquilibrium p (fun a => x (τ a)) := by
  classical
  set m : T → ℝ := fun t => E.μ.real (τ ⁻¹' {t}) with hm
  have hfibne : ∀ t, (τ ⁻¹' {t}).Nonempty := by
    intro t
    rw [nonempty_iff_ne_empty]
    intro he0
    have h := hmass t
    rw [he0] at h
    simp at h
  have hω0' : ∀ t, 0 ≤ ω t := by
    intro t
    obtain ⟨a, ha⟩ := hfibne t
    have := E.endow_nonneg a
    rwa [hω a, show τ a = t from ha] at this
  -- the finite auxiliary economy: utilities rescaled, endowments scaled by mass
  let F : ExchangeEconomy T ι :=
    { pref := fun t => prefOf fun y => u t ((m t)⁻¹ • y)
      endow := fun t => m t • ω t
      endow_nonneg := fun t i => mul_nonneg (hmass t).le (hω0' t i) }
  have hFendow : ∀ t, F.endow t = m t • ω t := fun _ => rfl
  have hFtotal : F.totalEndowment = ∫ a, E.endow a ∂E.μ := by
    rw [ExchangeEconomy.totalEndowment, integral_endow_eq_sum hτ hω]
  obtain ⟨p, y, hp, hyd, hyclear⟩ := F.exists_walrasianEquilibrium_of_preferences
    (u := fun t y => u t ((m t)⁻¹ • y)) (fun _ => rfl) (fun t => (hu t).comp (by fun_prop))
    (fun t => strictlyQuasiconcave_scaled (hmass t) (hsq t))
    (fun t => stronglyMonotone_scaled (hmass t) (hmono t))
    (by rw [hFtotal]; exact he)
    (fun t h => hω0 t (by
      have := congrFun h
      funext i
      have hi := this i
      simp only [hFendow, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      exact (mul_eq_zero.1 hi).resolve_left (hmass t).ne'))
  -- unscale: `y t = m t • x t` with `x t` demanded by type `t`
  have hx : ∀ t, ∃ xt ∈ demand (prefOf (u t)) p (cost p (ω t)), y t = m t • xt := by
    intro t
    have := hyd t
    rw [show F.wealth p t = cost p (m t • ω t) from rfl,
      show F.pref t = prefOf fun z => u t ((m t)⁻¹ • z) from rfl,
      demand_scaled (hmass t)] at this
    obtain ⟨xt, hxt, hxteq⟩ := this
    exact ⟨xt, hxt, hxteq.symm⟩
  choose xt hxtd hxteq using hx
  have hclear : ∑ t, E.μ.real (τ ⁻¹' {t}) • xt t = ∑ t, E.μ.real (τ ⁻¹' {t}) • ω t := by
    have h1 : ∑ t, m t • xt t = ∑ t, y t :=
      Finset.sum_congr rfl fun t _ => (hxteq t).symm
    have h2 : ∑ t, y t = ∑ t, m t • ω t := by
      rw [hyclear, ExchangeEconomy.totalEndowment]
    exact h1.trans h2
  -- every trader of type `t` consumes `xt t`
  refine ⟨p, xt, hp, ⟨?_, ae_of_all _ fun a => ?_, ?_⟩, ae_of_all _ fun a => ?_⟩
  · exact integrable_comp_type hτ xt
  · exact (hxtd (τ a)).1.1
  · rw [integral_comp_type hτ xt, hclear, integral_endow_eq_sum hτ hω]
  · rw [hpref, hω]
    exact hxtd (τ a)

/-! ### Witness: two types of square-root consumers

Traders uniform on `[0, 1]`; those in `[0, 1/3]` (mass `1/3`) have endowment
`(1, 2)` and those in `(1/3, 1]` (mass `2/3`) have `(2, 1)`; everyone has utility `√x₀ + √x₁`, which is
continuous, strictly quasiconcave and strongly monotone but has no demand when a
price is zero, so only the boundary-condition route gives existence. -/


noncomputable def sqrtType (a : ℝ) : Fin 2 := if a ≤ 1/3 then 0 else 1

theorem measurable_sqrtType : Measurable sqrtType := by
  unfold sqrtType
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

noncomputable def sqrtOmega : Fin 2 → Fin 2 → ℝ := fun t => if t = 0 then ![1, 2] else ![2, 1]

noncomputable def sqrtContinuum : ContinuumEconomy ℝ (Fin 2) where
  μ := volume.restrict (Icc (0 : ℝ) 1)
  pref a := prefOf GEExamples.uSqrt
  endow a := sqrtOmega (sqrtType a)
  endow_nonneg a i := by
    simp only [sqrtOmega]
    split_ifs <;> fin_cases i <;> norm_num
  endow_integrable := by
    have hm : Measurable fun a : ℝ => sqrtOmega (sqrtType a) :=
      (measurable_from_top (f := sqrtOmega)).comp measurable_sqrtType
    refine Integrable.mono' (integrable_const (2 : ℝ)) hm.aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simp only [sqrtOmega]
    split_ifs <;> fin_cases i <;> simp

theorem sqrtType_fiber_zero : sqrtType ⁻¹' {0} = Iic (1/3 : ℝ) := by
  ext a
  simp only [sqrtType, mem_preimage, mem_singleton_iff, mem_Iic]
  split_ifs with h
  · simpa using h
  · refine iff_of_false (by simp) ?_
    simpa using not_le.1 h

theorem sqrtType_fiber_one : sqrtType ⁻¹' {1} = Ioi (1/3 : ℝ) := by
  ext a
  simp only [sqrtType, mem_preimage, mem_singleton_iff, mem_Ioi]
  split_ifs with h
  · refine iff_of_false (by simp) ?_
    simpa using h
  · simpa using not_le.1 h

theorem sqrtContinuum_mass_zero : sqrtContinuum.μ.real (sqrtType ⁻¹' {0}) = 1/3 := by
  rw [sqrtType_fiber_zero]
  show (volume.restrict (Icc (0:ℝ) 1)).real (Iic (1/3)) = 1/3
  rw [measureReal_restrict_apply measurableSet_Iic,
    show Iic (1/3 : ℝ) ∩ Icc (0:ℝ) 1 = Icc (0:ℝ) (1/3) by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, by linarith [h.2]⟩⟩]
  simp [Real.volume_real_Icc]

theorem sqrtContinuum_mass_one : sqrtContinuum.μ.real (sqrtType ⁻¹' {1}) = 2/3 := by
  rw [sqrtType_fiber_one]
  show (volume.restrict (Icc (0:ℝ) 1)).real (Ioi (1/3)) = 2/3
  rw [measureReal_restrict_apply measurableSet_Ioi,
    show Ioi (1/3 : ℝ) ∩ Icc (0:ℝ) 1 = Ioc (1/3 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, by linarith [h.1], h.2⟩⟩]
  rw [Real.volume_real_Ioc]
  norm_num

theorem sqrtContinuum_mass_pos (t : Fin 2) : 0 < sqrtContinuum.μ.real (sqrtType ⁻¹' {t}) := by
  fin_cases t
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, sqrtContinuum_mass_zero]; norm_num
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, sqrtContinuum_mass_one]; norm_num

instance : IsFiniteMeasure sqrtContinuum.μ := by unfold sqrtContinuum; infer_instance

theorem sqrtContinuum_endow_integral (i : Fin 2) :
    0 < (∫ a, sqrtContinuum.endow a ∂sqrtContinuum.μ) i := by
  rw [integral_endow_eq_sum (E := sqrtContinuum) measurable_sqrtType (ω := sqrtOmega)
    (fun a => rfl)]
  rw [Fin.sum_univ_two]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sqrtContinuum_mass_zero,
    sqrtContinuum_mass_one, sqrtOmega]
  fin_cases i <;> norm_num

theorem sqrtContinuum_exists_equilibrium :
    ∃ (p : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ), PositivePrices p ∧
      sqrtContinuum.IsWalrasianEquilibrium p (fun a => x (sqrtType a)) := by
  refine exists_isWalrasianEquilibrium_of_types measurable_sqrtType
    (u := fun _ => GEExamples.uSqrt) (ω := sqrtOmega) (fun a => rfl) (fun a => rfl)
    sqrtContinuum_mass_pos
    (fun _ => GEExamples.continuous_uSqrt) (fun _ => GEExamples.strictlyQuasiconcave_uSqrt)
    (fun _ => GEExamples.stronglyMonotone_uSqrt) (fun t => ?_)
    sqrtContinuum_endow_integral
  intro h
  have := congrFun h 0
  simp only [sqrtOmega, Pi.zero_apply] at this
  split_ifs at this <;> norm_num at this

/-! ### Witness: the continuum is essential (non-convex preferences)

One type of traders, uniform on `[0, 1]`, endowment `(1, 1)` and the
**non-convex** utility `max(x₀, x₁)` ("specialise in one good"). At prices
`(1, 1)` demand contains `(2, 0)` and `(0, 2)` but not the average `(1, 1)`, so
no allocation giving (almost) all traders the same bundle is an equilibrium at
any positive prices (`maxContinuum_no_symmetric_equilibrium`). But `(1, 1)` is the midpoint of two demanded bundles, so the
bridge splits the population in halves, one consuming `(2, 0)` and the other
`(0, 2)`: an equilibrium of the continuum economy
(`maxContinuum_exists_equilibrium`). -/

/-- The specialisation utility `max(x₀, x₁)`. -/
def uMax (x : Fin 2 → ℝ) : ℝ := max (x 0) (x 1)

/-- One type, endowment `(1, 1)`, utility `max(x₀, x₁)`. -/
noncomputable def maxContinuum : ContinuumEconomy ℝ (Fin 2) where
  μ := volume.restrict (Icc (0 : ℝ) 1)
  pref _ := prefOf uMax
  endow _ := fun _ => 1
  endow_nonneg _ _ := zero_le_one
  endow_integrable := integrable_const _

instance : IsFiniteMeasure maxContinuum.μ := by unfold maxContinuum; infer_instance

/-- The unit price and unit bundle. -/
def one2 : Fin 2 → ℝ := fun _ => 1

theorem uMax_le_two {y : Fin 2 → ℝ} (hy : y ∈ budgetSet one2 (cost one2 one2)) :
    uMax y ≤ 2 := by
  obtain ⟨h0, hc⟩ := hy
  simp only [cost, one2, Fin.sum_univ_two, one_mul] at hc
  have ha : (0:ℝ) ≤ y 0 := h0 0
  have hb : (0:ℝ) ≤ y 1 := h0 1
  simp only [uMax]
  norm_num at hc
  exact max_le (by linarith) (by linarith)

theorem mem_demand_uMax {z : Fin 2 → ℝ} (hz0 : 0 ≤ z) (hz : z 0 + z 1 = 2)
    (hmax : uMax z = 2) :
    z ∈ demand (prefOf uMax) one2 (cost one2 one2) := by
  refine ⟨⟨hz0, ?_⟩, fun y hy => ?_⟩
  · simp only [cost, one2, Fin.sum_univ_two, one_mul]; linarith
  · show uMax y ≤ uMax z
    rw [hmax]; exact uMax_le_two hy

/-- **No trader demands the average bundle** `(1, 1)` at any positive prices:
spending everything on the cheaper good gives more than `1` of it. -/
theorem maxContinuum_const_not_demanded {p : Fin 2 → ℝ} (hp : PositivePrices p) :
    one2 ∉ demand (prefOf uMax) p (cost p one2) := by
  rintro ⟨-, hopt⟩
  have hw : cost p (fun _ => 1) = p 0 + p 1 := by simp [cost, Fin.sum_univ_two]
  have h0 := hp 0; have h1 := hp 1
  set y : Fin 2 → ℝ := ![(p 0 + p 1) / p 0, 0]
  have hy : y ∈ budgetSet p (cost p (fun _ => 1)) := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · show (0:ℝ) ≤ (p 0 + p 1) / p 0
        positivity
      · simp [y]
    · rw [hw]; simp [y, cost, Fin.sum_univ_two]; field_simp; rfl
  have := hopt y hy
  change uMax y ≤ uMax (fun _ => 1) at this
  simp only [uMax, y, Matrix.cons_val_zero, Matrix.cons_val_one, max_self] at this
  have hgt : 1 < (p 0 + p 1) / p 0 := by rw [lt_div_iff₀ h0]; linarith
  have := le_trans (le_max_left _ _) this
  linarith

/-- Hence **no equilibrium at positive prices gives identical traders identical
bundles**: a feasible constant allocation must be `(1, 1)`, which nobody demands. -/
theorem maxContinuum_no_symmetric_equilibrium {p : Fin 2 → ℝ} (hp : PositivePrices p)
    (c : Fin 2 → ℝ) {x : ℝ → Fin 2 → ℝ} (hx : x =ᵐ[maxContinuum.μ] fun _ => c) :
    ¬ maxContinuum.IsWalrasianEquilibrium p x := by
  rintro ⟨⟨-, -, hint⟩, hdem⟩
  have hvol : maxContinuum.μ.real univ = 1 := by
    show (volume.restrict (Icc (0:ℝ) 1)).real univ = 1
    simp [Real.volume_real_Icc]
  have hc : c = one2 := by
    have h := hint
    have he : (∫ a, maxContinuum.endow a ∂maxContinuum.μ) = one2 := by
      show ∫ _, (fun _ : Fin 2 => (1:ℝ)) ∂maxContinuum.μ = one2
      rw [integral_const, hvol, one_smul]; rfl
    rw [integral_congr_ae hx, integral_const, hvol, one_smul, he] at h
    exact h
  subst hc
  have hne : (ae maxContinuum.μ).NeBot := by
    rw [ae_neBot]
    intro h0
    have := congrArg (fun μ => μ.real univ) h0
    simp only [hvol] at this
    simp at this
  obtain ⟨a, ha, hxa⟩ := (hdem.and hx).exists
  rw [hxa] at ha
  exact maxContinuum_const_not_demanded hp ha

/-- **The continuum economy has an equilibrium** at prices `(1, 1)`, in which
identical traders consume different bundles. -/
theorem maxContinuum_exists_equilibrium :
    ∃ x : ℝ → Fin 2 → ℝ, maxContinuum.IsWalrasianEquilibrium one2 x := by
  have h20 := mem_demand_uMax (z := ![2, 0]) (fun i => by fin_cases i <;> simp)
    (by simp) (by simp [uMax])
  have h02 := mem_demand_uMax (z := ![0, 2]) (fun i => by fin_cases i <;> simp)
    (by simp) (by simp [uMax])
  have hmid : one2 ∈ convexHull ℝ (demand (prefOf uMax) one2 (cost one2 one2)) := by
    have := segment_subset_convexHull (𝕜 := ℝ) h20 h02
    refine this ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i; fin_cases i <;> simp [one2]
  exact exists_allocation_isWalrasianEquilibrium_of_mem_convexHull nonatomic_volume_Icc
    (fun _ => (0 : Fin 1)) measurable_const (fun _ => prefOf uMax) (fun _ => one2)
    (fun _ => rfl) (fun _ => rfl) one2 (fun _ => one2) (fun _ => hmid) rfl

end ContinuumEconomy
end Continuum

end Econ
