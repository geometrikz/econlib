/-
# Exchange economies with a continuum of traders (Aumann 1964)

**The economics.** Aumann (1964) modelled perfect competition by a nonatomic
measure space of traders: every individual is negligible, so no one has market
power. In such an economy the core coincides with the set of Walrasian
allocations (Aumann's core equivalence theorem), the limit counterpart of the
Debreu–Scarf replica theorem (`GE/DebreuScarf.lean`).

**Setup.** Traders form a measure space `(Ω, μ)` (finite and nonatomic in the
intended application; the structure itself allows any `μ`, and for `μ = 0`
everything is trivially feasible and unblocked); goods are a finite type
`ι`. Trader `a` has preference relation `R a` on `ℝ^ι` and endowment `e a ≥ 0`,
with `e` integrable. An allocation `x : Ω → ℝ^ι` is feasible if it is
integrable, nonnegative a.e., and `∫ x dμ = ∫ e dμ`. A **coalition** is a
measurable set of traders of positive measure; it **blocks** `x` if it can
reallocate its own endowment, `∫_S y = ∫_S e`, so that almost every member is
strictly better off. The **core** is the set of feasible allocations no
coalition blocks. A **Walrasian equilibrium** is a price `p` and a feasible `x`
with `x a` in trader `a`'s demand at wealth `p · e a` for almost every `a`.

**Results.**
* `IsWalrasianEquilibrium.inCore`: every Walrasian allocation is in the core
  (the easy half of Aumann's theorem; no convexity, monotonicity,
  nonatomicity or sign restriction on `p` needed, thanks to the equality form
  of blocking). If a coalition blocked, each member's new bundle would
  cost more than her endowment, so integrating over the coalition, its total
  cost would exceed the value of its endowment, contradicting `∫_S y = ∫_S e`.
* `linContinuum_*`: a witness: traders uniformly distributed on `[0, 1]`, each
  with endowment `(1, 1)` and perfect-substitutes utility `x₀ + x₁`; at prices
  `(1, 1)` autarky is a Walrasian equilibrium, hence in the core; and the grand
  coalition blocks the zero allocation (so `Blocks` is satisfiable).

The converse (core ⊆ Walrasian, Aumann 1964) is proved in
`GE/AumannCore.lean` (`InCore.isWalrasianEquilibrium_of_continuousPref`,
`inCore_iff_of_continuousPref`), via Lyapunov's theorem.

Feasibility and blocking use the equality form `∫ x = ∫ e` (as in Aumann
1964); under strong monotonicity this is equivalent to the free-disposal form
`∫ x ≤ ∫ e`.
-/
module

public import EconLean.GE.Exchange
public import EconLean.GE.Examples
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import EconLean.Foundations.Measure.Lyapunov
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

noncomputable section

namespace Econ
namespace Continuum

open MeasureTheory Set Filter

/-- An **exchange economy with a measure space of traders**. -/
structure ContinuumEconomy (Ω ι : Type*) [MeasurableSpace Ω] [Fintype ι] where
  /-- The distribution of traders. -/
  μ : Measure Ω
  /-- Trader `a`'s preference relation. -/
  pref : Ω → (ι → ℝ) → (ι → ℝ) → Prop
  /-- Trader `a`'s endowment. -/
  endow : Ω → ι → ℝ
  endow_nonneg : ∀ a, 0 ≤ endow a
  endow_integrable : Integrable endow μ

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (E : ContinuumEconomy Ω ι)

namespace ContinuumEconomy

/-- `x` is a **feasible allocation**: integrable, nonnegative for almost every
trader, and total consumption equals total endowment. -/
def Feasible (x : Ω → ι → ℝ) : Prop :=
  Integrable x E.μ ∧ (∀ᵐ a ∂E.μ, 0 ≤ x a) ∧ ∫ a, x a ∂E.μ = ∫ a, E.endow a ∂E.μ

/-- Coalition `S` **blocks** `x`: `S` is measurable with positive measure, and
some reallocation `y` of the coalition's own endowment makes almost every member
strictly better off. -/
def Blocks (S : Set Ω) (x : Ω → ι → ℝ) : Prop :=
  MeasurableSet S ∧ 0 < E.μ S ∧ ∃ y : Ω → ι → ℝ, IntegrableOn y S E.μ ∧
    (∀ᵐ a ∂E.μ, a ∈ S → 0 ≤ y a ∧ P (E.pref a) (y a) (x a)) ∧
    ∫ a in S, y a ∂E.μ = ∫ a in S, E.endow a ∂E.μ

/-- `x` is in the **core**: feasible and blocked by no coalition. -/
def InCore (x : Ω → ι → ℝ) : Prop :=
  E.Feasible x ∧ ∀ S, ¬ E.Blocks S x

/-- `(p, x)` is a **Walrasian equilibrium**: `x` is feasible and almost every
trader's bundle is in her demand at prices `p` and wealth `p · e a`. -/
def IsWalrasianEquilibrium (p : ι → ℝ) (x : Ω → ι → ℝ) : Prop :=
  E.Feasible x ∧ ∀ᵐ a ∂E.μ, x a ∈ demand (E.pref a) p (cost p (E.endow a))

/-- The cost map `z ↦ p · z` as a continuous linear functional. -/
def costCLM (p : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj i

theorem costCLM_apply (p z : ι → ℝ) : costCLM p z = cost p z := by
  simp [costCLM, cost]

/-- The value of an integral is the integral of the values. -/
theorem cost_setIntegral (p : ι → ℝ) {S : Set Ω} {y : Ω → ι → ℝ} (hy : IntegrableOn y S E.μ) :
    cost p (∫ a in S, y a ∂E.μ) = ∫ a in S, cost p (y a) ∂E.μ := by
  rw [← costCLM_apply, ← (costCLM p).integral_comp_comm hy]
  simp only [costCLM_apply]

/-- **Walrasian allocations are in the core** (Aumann 1964, easy half). -/
theorem IsWalrasianEquilibrium.inCore {p : ι → ℝ} {x : Ω → ι → ℝ}
    (h : E.IsWalrasianEquilibrium p x) : E.InCore x := by
  refine ⟨h.1, fun S ⟨hS, hSpos, y, hyint, hy, hsum⟩ => ?_⟩
  have heint : IntegrableOn E.endow S E.μ := E.endow_integrable.integrableOn
  -- every member's new bundle costs strictly more than her endowment
  have hgt : ∀ᵐ a ∂E.μ.restrict S, 0 < cost p (y a) - cost p (E.endow a) := by
    rw [ae_restrict_iff' hS]
    filter_upwards [h.2, hy] with a hxa hya haS
    obtain ⟨hy0, hyP⟩ := hya haS
    exact sub_pos.2 (ExchangeEconomy.cost_gt_of_mem_demand hxa hy0 hyP)
  have hfint : Integrable (fun a => cost p (y a) - cost p (E.endow a)) (E.μ.restrict S) := by
    refine Integrable.sub ?_ ?_
    · simpa only [costCLM_apply] using (costCLM p).integrable_comp hyint
    · simpa only [costCLM_apply] using (costCLM p).integrable_comp heint
  have hpos : 0 < ∫ a in S, (cost p (y a) - cost p (E.endow a)) ∂E.μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hgt.mono fun a ha => ha.le) hfint]
    have hsupp : (univ : Set Ω) ≤ᵐ[E.μ.restrict S]
        Function.support fun a => cost p (y a) - cost p (E.endow a) :=
      hgt.mono fun a ha _ => ne_of_gt ha
    calc (0 : ENNReal) < E.μ.restrict S univ := by
          rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact hSpos
      _ ≤ _ := measure_mono_ae hsupp
  rw [integral_sub ((costCLM p).integrable_comp hyint |>.congr (by simp [costCLM_apply]))
    ((costCLM p).integrable_comp heint |>.congr (by simp [costCLM_apply])),
    ← E.cost_setIntegral p hyint, ← E.cost_setIntegral p heint, hsum, sub_self] at hpos
  exact lt_irrefl _ hpos

/-! ### Witness -/

/-- Traders uniformly distributed on `[0, 1]`, endowment `(1, 1)`, utility
`x₀ + x₁`. -/
def linContinuum : ContinuumEconomy ℝ (Fin 2) where
  μ := MeasureTheory.volume.restrict (Icc (0 : ℝ) 1)
  pref _ := prefOf GEExamples.uLin
  endow _ := fun _ => 1
  endow_nonneg _ _ := zero_le_one
  endow_integrable := integrable_const _

/-- **Autarky is a Walrasian equilibrium** of `linContinuum` at prices `(1, 1)`. -/
theorem linContinuum_isWalrasianEquilibrium :
    linContinuum.IsWalrasianEquilibrium (fun _ => 1) linContinuum.endow := by
  refine ⟨⟨linContinuum.endow_integrable, Eventually.of_forall fun a => linContinuum.endow_nonneg a,
    rfl⟩, Eventually.of_forall fun a => ⟨⟨linContinuum.endow_nonneg a, le_rfl⟩, ?_⟩⟩
  rintro y ⟨-, hy⟩
  simp only [linContinuum, cost, Fin.sum_univ_two, one_mul] at hy
  show GEExamples.uLin y ≤ GEExamples.uLin (fun _ => 1)
  simp only [GEExamples.uLin]
  linarith

/-- Hence autarky is in the core of `linContinuum`. -/
theorem linContinuum_inCore : linContinuum.InCore linContinuum.endow :=
  linContinuum_isWalrasianEquilibrium.inCore

/-- The grand coalition `[0, 1]` **blocks** the zero allocation by returning to
everyone her endowment. -/
theorem linContinuum_blocks_zero : linContinuum.Blocks (Icc 0 1) 0 := by
  refine ⟨measurableSet_Icc, ?_, linContinuum.endow, linContinuum.endow_integrable.integrableOn,
    Eventually.of_forall fun a _ => ⟨linContinuum.endow_nonneg a, ?_⟩, rfl⟩
  · simp [linContinuum]
  · show GEExamples.uLin 0 ≤ GEExamples.uLin _ ∧ ¬ GEExamples.uLin _ ≤ GEExamples.uLin 0
    simp only [GEExamples.uLin, linContinuum, Pi.zero_apply]
    norm_num

/-- Hence the zero allocation is not in the core. -/
theorem linContinuum_zero_not_inCore : ¬ linContinuum.InCore 0 := fun h =>
  h.2 _ linContinuum_blocks_zero

end ContinuumEconomy

end Continuum
end Econ
