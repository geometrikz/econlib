/-
# Existence of Walrasian equilibrium: the excess-demand approach

MWG §17.B–17.C; Debreu, *Theory of Value* (1959) §5.6; Gale (1955),
Nikaido (1956), Debreu (1956).

**The economics.** Normalize prices to the simplex
`Δ = {p ≥ 0 | ∑ᵢ pᵢ = 1}` (only relative prices matter). Given a demand
function `dₐ(p)` for each consumer, the **aggregate excess demand** is

    z(p) = ∑ₐ dₐ(p) − ω̄.

Walras' law says `p · z(p) = 0`. The **Gale–Nikaido–Debreu lemma**: if `z` is
continuous on `Δ` and `p · z(p) ≤ 0`, there is `p* ∈ Δ` with `z(p*) ≤ 0`.
Its proof is Brouwer's fixed point theorem applied to the "price-raising" map

    f(p)ᵢ = (pᵢ + max(zᵢ(p), 0)) / (1 + ∑ⱼ max(zⱼ(p), 0)),

which raises the relative price of every good in excess demand. At a fixed
point, `max(zᵢ, 0) = pᵢ · S` for all `i`, and Walras' law forces `S = 0`.

`z(p*) ≤ 0` together with Walras' law gives a **free-disposal equilibrium**:
markets clear except for goods in excess supply, and those are free
(`pᵢ* = 0`). If all prices are positive, it is a Walrasian equilibrium.

**About Brouwer.** Mathlib does not (yet) contain Brouwer's fixed point
theorem. Rather than assume it as an axiom, we state it as a hypothesis,
`BrouwerSimplex ι`, so every theorem here is honest about using it and the
axiom audit stays clean. The hypothesis is discharged
* here, for **two goods**, from the intermediate value theorem
  (`brouwerSimplex_fin_two`), giving unconditional existence for 2 goods;
* in general, once Brouwer is imported from an existing Lean formalization
  (Lyu–Li 2026; see `PLAN.md` §1 `Foundations/FixedPoint/`).

**Scope (important).** This is the "excess demand continuous on the whole
simplex" version (Debreu 1959 §5.6). It needs demand to exist at prices where
some good is free, so it does *not* apply to strongly monotone economies
(MWG Prop. 17.C.1, Cobb–Douglas), whose excess demand blows up at the boundary.
Covering those needs a boundary-condition / truncation argument and is the
next step. Outside two goods, every existence theorem here is conditional on
the `BrouwerSimplex` hypothesis.

**Shared abstractions.** `excessDemand` and `IsDemandSelection` are stated for
an arbitrary finite population `α`, so the aggregation results of PLAN §7.2a
(Sonnenschein–Mantel–Debreu, gross substitutes) can be stated about them.
-/
module

public import EconLean.GE.Exchange
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace Econ

open Finset Set

variable {α ι : Type*}

/-! ### The price simplex and Brouwer's fixed point property -/

/-- The **price simplex** `Δ = {p ≥ 0 | ∑ᵢ pᵢ = 1}` (MWG §17.B). (Mathlib's
`stdSimplex` is being renamed upstream, so we use our own one-line
definition.) -/
def priceSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {p | 0 ≤ p ∧ ∑ i, p i = 1}

/-- Prices in the simplex are at most `1`. -/
theorem le_one_of_mem_priceSimplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ priceSimplex ι) (i : ι) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

/-- **Brouwer's fixed point theorem for the simplex** `Δ ⊆ ℝ^ι`, as a
proposition: every continuous self-map of `Δ` has a fixed point. It is a true
theorem of mathematics; we take it as a hypothesis until it is available in
Lean. -/
def BrouwerSimplex (ι : Type*) [Fintype ι] : Prop :=
  ∀ f : (ι → ℝ) → (ι → ℝ), ContinuousOn f (priceSimplex ι) →
    MapsTo f (priceSimplex ι) (priceSimplex ι) → ∃ p ∈ priceSimplex ι, f p = p

/-- **Brouwer for two goods.** The simplex in `ℝ²` is a segment, and
Brouwer's theorem there is the intermediate value theorem: `t ↦ f(t, 1-t)₀ - t`
is `≥ 0` at `t = 0` and `≤ 0` at `t = 1`, so it has a zero. -/
theorem brouwerSimplex_fin_two : BrouwerSimplex (Fin 2) := by
  intro f hf hmaps
  -- Parametrize the simplex by `t ∈ [0, 1]`.
  set γ : ℝ → (Fin 2 → ℝ) := fun t => ![t, 1 - t] with hγ
  have hγc : Continuous γ := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [hγ] <;> fun_prop
  have hγΔ : MapsTo γ (Icc 0 1) (priceSimplex (Fin 2)) := by
    intro t ht
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [hγ] <;> linarith [ht.1, ht.2]
    · simp [hγ, Fin.sum_univ_two]
  -- The function whose zero is a fixed point.
  set h : ℝ → ℝ := fun t => f (γ t) 0 - t with hh
  have hhc : ContinuousOn h (Icc 0 1) :=
    ((continuous_apply 0).comp_continuousOn (hf.comp hγc.continuousOn hγΔ)).sub
      continuousOn_id
  have h0 : 0 ≤ h 0 := by
    simpa [hh] using (hmaps (hγΔ ⟨le_rfl, zero_le_one⟩)).1 0
  have h1 : h 1 ≤ 0 := by
    have := le_one_of_mem_priceSimplex (hmaps (hγΔ ⟨zero_le_one, le_rfl⟩)) 0
    simp only [hh]
    linarith
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' zero_le_one hhc ⟨h1, h0⟩
  refine ⟨γ t, hγΔ ht, ?_⟩
  -- First coordinate: `f(γ t)₀ = t`. Second: both vectors sum to 1.
  have hfirst : f (γ t) 0 = t := by simp only [hh] at hzero; linarith
  have hsum := (hmaps (hγΔ ht)).2
  rw [Fin.sum_univ_two] at hsum
  funext i
  fin_cases i
  · simpa [hγ] using hfirst
  · simp only [hγ, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith

/-! ### The Gale–Nikaido–Debreu lemma -/

section GND

variable [Fintype ι]

/-- **Gale–Nikaido–Debreu lemma** (Debreu 1959 §5.6; MWG Prop. 17.C.1's core
step). If `z` is continuous on the price simplex and satisfies the weak form
of Walras' law, `p · z(p) ≤ 0`, then some price vector in the simplex has no
excess demand for any good: `z(p) ≤ 0`. Uses Brouwer (as a hypothesis). -/
theorem gale_nikaido_debreu (hB : BrouwerSimplex ι) {z : (ι → ℝ) → (ι → ℝ)}
    (hz : ContinuousOn z (priceSimplex ι))
    (hW : ∀ p ∈ priceSimplex ι, cost p (z p) ≤ 0) :
    ∃ p ∈ priceSimplex ι, z p ≤ 0 := by
  -- `m p i = max(zᵢ(p), 0)`, the excess demand for good `i` if positive.
  set m : (ι → ℝ) → ι → ℝ := fun p i => max (z p i) 0 with hm
  set S : (ι → ℝ) → ℝ := fun p => ∑ i, m p i with hS
  have hm0 : ∀ p i, 0 ≤ m p i := fun p i => le_max_right _ _
  have hS0 : ∀ p, 0 ≤ S p := fun p => Finset.sum_nonneg fun i _ => hm0 p i
  have hden : ∀ p, 0 < 1 + S p := fun p => by linarith [hS0 p]
  -- The price-adjustment map.
  set f : (ι → ℝ) → (ι → ℝ) := fun p i => (p i + m p i) / (1 + S p) with hf
  have hmc : ∀ i, ContinuousOn (fun p => m p i) (priceSimplex ι) := fun i => by
    have : ContinuousOn (fun p => z p i) (priceSimplex ι) :=
      (continuous_apply i).comp_continuousOn hz
    simp only [hm]
    fun_prop
  have hfc : ContinuousOn f (priceSimplex ι) := by
    refine continuousOn_pi.2 fun i => ?_
    refine ((continuous_apply i).continuousOn.add (hmc i)).div
      (continuousOn_const.add (continuousOn_finsetSum _ fun j _ => hmc j))
      fun p _ => (hden p).ne'
  have hfmaps : MapsTo f (priceSimplex ι) (priceSimplex ι) := by
    intro p hp
    refine ⟨fun i => div_nonneg (add_nonneg (hp.1 i) (hm0 p i)) (hden p).le, ?_⟩
    simp only [hf]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp.2]
    exact div_self (hden p).ne'
  obtain ⟨p, hp, hfix⟩ := hB f hfc hfmaps
  -- At the fixed point, `mᵢ = pᵢ S` for every good.
  have hmi : ∀ i, m p i = p i * S p := by
    intro i
    have := congrFun hfix i
    simp only [hf] at this
    rw [div_eq_iff (hden p).ne'] at this
    linarith
  -- `zᵢ mᵢ = mᵢ²`, so `∑ mᵢ² = ∑ zᵢ mᵢ = S (p · z) ≤ 0`.
  have hzm : ∀ i, z p i * m p i = m p i * m p i := by
    intro i
    simp only [hm]
    rcases le_total (z p i) 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_left h]
  have hsum_le : ∑ i, m p i * m p i ≤ 0 := by
    calc ∑ i, m p i * m p i = ∑ i, z p i * m p i := by simp [hzm]
      _ = S p * cost p (z p) := by
        simp only [cost, hmi, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hS0 p) (hW p hp)
  have hsum0 : ∑ i, m p i * m p i = 0 :=
    le_antisymm hsum_le (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  refine ⟨p, hp, fun i => ?_⟩
  have hmi0 : m p i * m p i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (m p j))).1 hsum0 i
      (Finset.mem_univ i)
  have : max (z p i) 0 = 0 := mul_self_eq_zero.1 hmi0
  exact (max_eq_right_iff.1 this)

/-- With Walras' law holding with equality, `z(p) ≤ 0` and `p ≥ 0` mean every
good in excess supply is free: `pᵢ zᵢ(p) = 0` for each `i`. -/
theorem price_eq_zero_of_excess_supply {p e : ι → ℝ} (hp : 0 ≤ p) (he : e ≤ 0)
    (hW : cost p e = 0) {i : ι} (hi : e i < 0) : p i = 0 := by
  -- Each term `pⱼ eⱼ ≤ 0` and the terms sum to `0`, so each is `0`.
  have hterms := (Finset.sum_eq_zero_iff_of_nonpos
    (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hp j) (he j))).1 hW i (Finset.mem_univ i)
  exact (mul_eq_zero.1 hterms).resolve_right hi.ne

end GND

/-! ### Exchange economies: excess demand and equilibrium -/

namespace ExchangeEconomy

variable [Fintype α] [Fintype ι] (E : ExchangeEconomy α ι)

/-- A **demand selection** on a set of prices `D`: for every `p ∈ D`, `dₐ(p)`
is one of consumer `a`'s demanded bundles at wealth `p · ωₐ`. -/
def IsDemandSelection (d : α → (ι → ℝ) → (ι → ℝ)) (D : Set (ι → ℝ)) : Prop :=
  ∀ p ∈ D, ∀ a, d a p ∈ demand (E.pref a) p (E.wealth p a)

/-- **Aggregate excess demand** `z(p) = ∑ₐ dₐ(p) − ω̄` (MWG Def. 17.B.2). -/
def excessDemand (d : α → (ι → ℝ) → (ι → ℝ)) (p : ι → ℝ) : ι → ℝ :=
  ∑ a, d a p - E.totalEndowment

/-- A **free-disposal equilibrium** (Debreu 1959 §5.7; MWG Exercise 17.B.3):
every consumer demands their bundle, demand does not exceed supply, and any
good in excess supply has price zero. -/
def IsFreeDisposalEquilibrium (p : ι → ℝ) (x : Allocation α ι) : Prop :=
  0 ≤ p ∧ (∀ a, x a ∈ demand (E.pref a) p (E.wealth p a)) ∧ ∑ a, x a ≤ E.totalEndowment ∧
    ∀ i, (∑ a, x a) i < E.totalEndowment i → p i = 0

variable {E}

/-- **Aggregate Walras' law** (MWG Prop. 17.B.2(ii)): with locally nonsatiated
consumers, `p · z(p) = 0`. -/
theorem cost_excessDemand (hlns : ∀ a, LocallyNonsatiated (E.pref a))
    {d : α → (ι → ℝ) → (ι → ℝ)} {D : Set (ι → ℝ)} (hd : E.IsDemandSelection d D)
    {p : ι → ℝ} (hp : p ∈ D) : cost p (E.excessDemand d p) = 0 := by
  rw [excessDemand, cost_sub_right, cost_sum, totalEndowment, cost_sum]
  -- Each consumer spends exactly their wealth.
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl fun a _ => walras_law (hlns a) (hd p hp a)

/-- Zero excess demand at `p` is a Walrasian equilibrium. -/
theorem isWalrasianEquilibrium_of_excessDemand_eq_zero {d : α → (ι → ℝ) → (ι → ℝ)}
    {D : Set (ι → ℝ)} (hd : E.IsDemandSelection d D) {p : ι → ℝ} (hp : p ∈ D)
    (hz : E.excessDemand d p = 0) : E.IsWalrasianEquilibrium p (fun a => d a p) :=
  ⟨hd p hp, sub_eq_zero.1 hz⟩

/-- A free-disposal equilibrium with strictly positive prices is a Walrasian
equilibrium. -/
theorem IsFreeDisposalEquilibrium.isWalrasianEquilibrium {p : ι → ℝ}
    {x : Allocation α ι} (h : E.IsFreeDisposalEquilibrium p x) (hp : ∀ i, 0 < p i) :
    E.IsWalrasianEquilibrium p x := by
  refine ⟨h.2.1, funext fun i => ?_⟩
  rcases (h.2.2.1 i).lt_or_eq with hlt | heq
  · exact absurd (h.2.2.2 i hlt) (hp i).ne'
  · exact heq

/-- **Existence of equilibrium, excess-demand approach** (Debreu 1959 §5.6).
Assume Brouwer for the simplex, locally nonsatiated consumers, and a demand
selection that is defined and continuous on the whole price simplex. Then a
free-disposal equilibrium exists.

**Limitation (review finding).** The demand selection must exist at *boundary*
prices where some good is free. Strongly monotone consumers have no demand
there (they want unboundedly much of the free good), so this theorem does
**not** cover MWG Prop. 17.C.1 or Cobb–Douglas economies; that needs the
boundary-condition argument (or Debreu's truncation of consumption sets), which
is the next step. Continuity of the selection is assumed, not derived from
preferences via Berge. -/
theorem exists_freeDisposalEquilibrium (hB : BrouwerSimplex ι)
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d : α → (ι → ℝ) → (ι → ℝ)}
    (hd : E.IsDemandSelection d (priceSimplex ι))
    (hc : ∀ a, ContinuousOn (d a) (priceSimplex ι)) :
    ∃ p ∈ priceSimplex ι, E.IsFreeDisposalEquilibrium p (fun a => d a p) := by
  have hzc : ContinuousOn (E.excessDemand d) (priceSimplex ι) := by
    have : ContinuousOn (fun p => ∑ a, d a p) (priceSimplex ι) := by
      have h := continuousOn_finsetSum (Finset.univ : Finset α) fun a _ => hc a
      simpa [Finset.sum_fn] using h
    exact this.sub continuousOn_const
  obtain ⟨p, hp, hz⟩ := gale_nikaido_debreu hB hzc
    fun q hq => (cost_excessDemand hlns hd hq).le
  refine ⟨p, hp, hp.1, hd p hp, ?_, fun i hi => ?_⟩
  · intro i
    have := hz i
    simp only [excessDemand, Pi.sub_apply, Pi.zero_apply] at this
    show (∑ a, d a p) i ≤ E.totalEndowment i
    linarith
  · refine price_eq_zero_of_excess_supply hp.1 hz (cost_excessDemand hlns hd hp) ?_
    have hi' : (∑ a, d a p) i < E.totalEndowment i := hi
    simp only [excessDemand, Pi.sub_apply]
    linarith

/-- **Existence for two goods, unconditionally.** In a two-good exchange
economy with locally nonsatiated consumers and a demand selection continuous on
the price simplex, a free-disposal equilibrium exists. (Brouwer is discharged
by the intermediate value theorem.) -/
theorem exists_freeDisposalEquilibrium_two_goods {E : ExchangeEconomy α (Fin 2)}
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d : α → (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hd : E.IsDemandSelection d (priceSimplex (Fin 2)))
    (hc : ∀ a, ContinuousOn (d a) (priceSimplex (Fin 2))) :
    ∃ p ∈ priceSimplex (Fin 2), E.IsFreeDisposalEquilibrium p (fun a => d a p) :=
  exists_freeDisposalEquilibrium brouwerSimplex_fin_two hlns hd hc

end ExchangeEconomy

end Econ
