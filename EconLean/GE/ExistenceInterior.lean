/-
# Existence of Walrasian equilibrium with a boundary condition (MWG Prop. 17.C.1)

PLAN.md §1 (M4). MWG Prop. 17.B.2 and 17.C.1; Debreu (1959) §5.6; Arrow & Hahn
(1971) ch. 2.

**The economics.** `GE/ExistenceGeneral.lean` needs excess demand defined and
continuous on the *closed* price simplex. That fails for strongly monotone
consumers (Cobb–Douglas, CES, linear): when a good is free they want unboundedly
much of it. MWG Prop. 17.C.1 instead assumes, for excess demand `z` defined on
strictly positive prices,

1. `z` is continuous on `p ≫ 0`;
2. Walras' law `p · z(p) = 0`;
3. `z` is bounded below: `zₗ(p) > −s` for all `p ≫ 0` and goods `l`;
4. the **boundary condition** (MWG 17.B.2(v)): if `pⁿ ≫ 0`, `pⁿ → p ≠ 0` and
   `pₗ = 0` for some `l`, then `maxₗ zₗ(pⁿ) → ∞`.

and concludes that some `p ≫ 0` has `z(p) = 0`. (Homogeneity of degree zero,
also in MWG's list, is not needed for this conclusion.)

**Proof.** For small `ε > 0`, shrink the simplex by `r(p) = (1 − Nε) p + ε 𝟙`
(`N` = number of goods), which maps the simplex onto the prices in it with every
coordinate `≥ ε`. The function

    w(p)ₗ = (1 − Nε) zₗ(r p) + ε ∑ₖ zₖ(r p)

is continuous on the simplex and satisfies `p · w(p) = r(p) · z(r p) = 0`, so
the Gale–Nikaido–Debreu lemma gives `p` with `w(p) ≤ 0`. Writing `x = r(p)`:
`(1 − Nε) zₗ(x) + ε ∑ₖ zₖ(x) ≤ 0` for every `l`. With the lower bound this
bounds `z(x)` above uniformly in `ε`. Let `ε → 0` and pass to a convergent
subsequence `x → p̄` in the simplex. The boundary condition and the upper bound
force `p̄ ≫ 0`; continuity then gives `zₗ(p̄) ≤ 0` for all `l`, and Walras'
law with `p̄ ≫ 0` gives `z(p̄) = 0`.

Not yet done: deriving conditions 1–4 from preferences (continuous, strictly
convex, strongly monotone, positive endowments; MWG 17.B.2) via Berge.
-/
module

public import EconLean.GE.ExistenceGeneral
public import EconLean.Bridges.Aggregation.GrossSubstitutes
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace Econ

open Set Filter Topology Finset

variable {ι : Type*} [Fintype ι]

/-- Excess demand is **bounded below** on strictly positive prices
(MWG 17.B.2(iv)). -/
def ExcessBoundedBelow (z : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∃ s : ℝ, ∀ p, PositivePrices p → ∀ l, -s < z p l

/-- The **boundary condition** (MWG 17.B.2(v)): along strictly positive prices
converging to a nonzero price vector with some zero price, the largest excess
demand becomes arbitrarily large. -/
def BoundaryCondition (z : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∀ (pn : ℕ → ι → ℝ) (pbar : ι → ℝ), (∀ n, PositivePrices (pn n)) →
    Tendsto pn atTop (𝓝 pbar) → pbar ≠ 0 → (∃ l, pbar l = 0) →
      ∀ M : ℝ, ∀ᶠ n in atTop, ∃ l, M < z (pn n) l

/-- The shrinking map `r_ε(p) = (1 − Nε) p + ε 𝟙`. -/
def shrinkPrice (ε : ℝ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (1 - (Fintype.card ι : ℝ) * ε) * p i + ε

omit [Fintype ι] in
theorem isOpen_positivePrices [Finite ι] : IsOpen {p : ι → ℝ | PositivePrices p} := by
  have : {p : ι → ℝ | PositivePrices p} = ⋂ i, {p | 0 < p i} := by
    ext p; simp [PositivePrices]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem continuous_shrinkPrice (ε : ℝ) : Continuous (shrinkPrice (ι := ι) ε) :=
  continuous_pi fun i => ((continuous_apply i).const_mul _).add continuous_const

/-- `r_ε` maps the simplex into strictly positive prices in the simplex, when
`0 < ε` and `Nε ≤ 1`. -/
theorem shrinkPrice_mem {ε : ℝ} (hε : 0 < ε) (hNε : (Fintype.card ι : ℝ) * ε ≤ 1)
    {p : ι → ℝ} (hp : p ∈ priceSimplex ι) :
    PositivePrices (shrinkPrice ε p) ∧ shrinkPrice ε p ∈ priceSimplex ι := by
  have hpos : PositivePrices (shrinkPrice ε p) := fun i => by
    have := mul_nonneg (sub_nonneg.2 hNε) (hp.1 i)
    simp only [shrinkPrice]; linarith
  refine ⟨hpos, fun i => (hpos i).le, ?_⟩
  simp only [shrinkPrice, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- `r_ε(p) · x = (1 − Nε) p · x + ε ∑ₖ xₖ`. -/
theorem cost_shrinkPrice (ε : ℝ) (p x : ι → ℝ) :
    cost (shrinkPrice ε p) x
      = (1 - (Fintype.card ι : ℝ) * ε) * cost p x + ε * ∑ k, x k := by
  simp only [cost, shrinkPrice, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Step 1: approximate equilibria.** For `0 < ε` with `Nε ≤ 1`, there is a
strictly positive price `x` in the simplex with
`(1 − Nε) zₗ(x) + ε ∑ₖ zₖ(x) ≤ 0` for every good `l`. -/
theorem exists_approx_equilibrium [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    (hc : ContinuousOn z {p | PositivePrices p}) (hW : ∀ p, PositivePrices p → cost p (z p) = 0)
    {ε : ℝ} (hε : 0 < ε) (hNε : (Fintype.card ι : ℝ) * ε ≤ 1) :
    ∃ x, PositivePrices x ∧ x ∈ priceSimplex ι ∧
      ∀ l, (1 - (Fintype.card ι : ℝ) * ε) * z x l + ε * ∑ k, z x k ≤ 0 := by
  set N : ℝ := (Fintype.card ι : ℝ)
  let w : (ι → ℝ) → (ι → ℝ) := fun p l =>
    (1 - N * ε) * z (shrinkPrice ε p) l + ε * ∑ k, z (shrinkPrice ε p) k
  have hzr : ContinuousOn (fun p => z (shrinkPrice ε p)) (priceSimplex ι) :=
    hc.comp (continuous_shrinkPrice ε).continuousOn fun p hp => (shrinkPrice_mem hε hNε hp).1
  have hzri : ∀ k, ContinuousOn (fun p => z (shrinkPrice ε p) k) (priceSimplex ι) :=
    fun k => (continuous_apply k).comp_continuousOn hzr
  have hwc : ContinuousOn w (priceSimplex ι) := by
    refine continuousOn_pi.2 fun l => ?_
    exact ((hzri l).const_smul (1 - N * ε)).add
      ((continuousOn_finsetSum _ fun k _ => hzri k).const_smul ε)
  have hwW : ∀ p ∈ priceSimplex ι, cost p (w p) ≤ 0 := by
    intro p hp
    have hr := hW _ (shrinkPrice_mem hε hNε hp).1
    rw [cost_shrinkPrice] at hr
    have e1 : ∑ i, p i * ((1 - N * ε) * z (shrinkPrice ε p) i)
        = (1 - N * ε) * ∑ i, p i * z (shrinkPrice ε p) i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, p i * (ε * ∑ k, z (shrinkPrice ε p) k) = ε * ∑ k, z (shrinkPrice ε p) k := by
      rw [← Finset.sum_mul, hp.2, one_mul]
    have : cost p (w p) = (1 - N * ε) * cost p (z (shrinkPrice ε p))
        + ε * ∑ k, z (shrinkPrice ε p) k := by
      simp only [w, cost, mul_add, Finset.sum_add_distrib]
      rw [e1, e2]
    rw [this, hr]
  obtain ⟨p, hp, hwp⟩ := gale_nikaido_debreu' hwc hwW
  obtain ⟨hxpos, hxΔ⟩ := shrinkPrice_mem hε hNε hp
  exact ⟨shrinkPrice ε p, hxpos, hxΔ, fun l => hwp l⟩

/-- **Existence of a Walrasian equilibrium with strictly positive prices**
(MWG Prop. 17.C.1). If excess demand `z` is continuous on strictly positive
prices, satisfies Walras' law there, is bounded below, and satisfies the
boundary condition, then `z(p) = 0` for some `p ≫ 0`.

MWG's homogeneity hypothesis 17.B.2(ii) is deliberately omitted: the theorem
is more general without it (homogeneity is only used to move to the simplex). -/
theorem exists_equilibrium_of_boundaryCondition [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    (hc : ContinuousOn z {p | PositivePrices p}) (hW : ∀ p, PositivePrices p → cost p (z p) = 0)
    (hb : ExcessBoundedBelow z) (hbd : BoundaryCondition z) :
    ∃ p, PositivePrices p ∧ z p = 0 := by
  classical
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 1 ≤ N := by
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨s, hs⟩ := hb
  set S := max s 0
  have hS : ∀ p, PositivePrices p → ∀ l, -S < z p l := fun p hp l =>
    lt_of_le_of_lt (neg_le_neg (le_max_left s 0)) (hs p hp l)
  -- The sequence of shrink factors `εₙ = 1 / (2N (n + 1))`.
  let ε : ℕ → ℝ := fun n => 1 / (2 * N) * (1 / ((n : ℝ) + 1))
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hNε : ∀ n, N * ε n ≤ 1 / 2 := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have : N * ε n = 1 / 2 * (1 / ((n : ℝ) + 1)) := by
      simp only [ε]; field_simp
    rw [this]; nlinarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / (2 * N))
    simpa [ε] using this
  -- Approximate equilibria.
  have happrox := fun n => exists_approx_equilibrium hc hW (hε n) ((hNε n).trans (by norm_num))
  choose x hxpos hxΔ hxineq using happrox
  -- Uniform upper bound `zₗ(xₙ) ≤ S`.
  have hub : ∀ n l, z (x n) l ≤ S := by
    intro n l
    by_contra hlt
    push Not at hlt
    have hsum : -(N * S) < ∑ k, z (x n) k := by
      have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun k _ => hS (x n) (hxpos n) k)
      simpa [Finset.sum_const, Finset.card_univ, hNdef] using this
    have h := hxineq n l
    have hS0 : 0 ≤ S := le_max_right s 0
    have hεn := hε n
    have hNεn := hNε n
    nlinarith [mul_le_mul_of_nonneg_left hNεn hS0]
  -- A convergent subsequence.
  obtain ⟨pbar, hpbarΔ, φ, hφ, hlim⟩ := isCompact_priceSimplex.tendsto_subseq hxΔ
  have hpbar0 : pbar ≠ 0 := by
    intro h; have := hpbarΔ.2; simp [h] at this
  -- The limit is strictly positive, by the boundary condition.
  have hpbarpos : PositivePrices pbar := by
    by_contra hnot
    simp only [PositivePrices, not_forall, not_lt] at hnot
    obtain ⟨l, hl⟩ := hnot
    have hl0 : pbar l = 0 := le_antisymm hl (hpbarΔ.1 l)
    obtain ⟨n, k, hk⟩ := (hbd (x ∘ φ) pbar (fun n => hxpos (φ n)) hlim hpbar0 ⟨l, hl0⟩ S).exists
    exact absurd (hub (φ n) k) (not_le.2 hk)
  -- Continuity of `z` at the limit.
  have hzc : ContinuousAt z pbar :=
    hc.continuousAt (isOpen_positivePrices.mem_nhds hpbarpos)
  have hzlim : Tendsto (fun n => z (x (φ n))) atTop (𝓝 (z pbar)) := hzc.tendsto.comp hlim
  have hεφ : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) := hεlim.comp hφ.tendsto_atTop
  -- Each excess demand is `≤ 0` at the limit.
  have hle : ∀ l, z pbar l ≤ 0 := by
    intro l
    have hcomp : ∀ k, Tendsto (fun n => z (x (φ n)) k) atTop (𝓝 (z pbar k)) :=
      fun k => (continuous_apply k).continuousAt.tendsto.comp hzlim
    have hT : Tendsto (fun n => (1 - N * ε (φ n)) * z (x (φ n)) l
        + ε (φ n) * ∑ k, z (x (φ n)) k) atTop
        (𝓝 ((1 - N * 0) * z pbar l + 0 * ∑ k, z pbar k)) :=
      (((tendsto_const_nhds.sub (tendsto_const_nhds.mul hεφ)).mul (hcomp l)).add
        (hεφ.mul (tendsto_finsetSum _ fun k _ => hcomp k)))
    simp only [mul_zero, sub_zero, one_mul, zero_mul, add_zero] at hT
    exact le_of_tendsto' hT fun n => hxineq (φ n) l
  -- Walras' law at a strictly positive price turns `z ≤ 0` into `z = 0`.
  refine ⟨pbar, hpbarpos, funext fun i => ?_⟩
  have hWp := hW pbar hpbarpos
  have hterms := (Finset.sum_eq_zero_iff_of_nonpos
    (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hpbarpos j).le (hle j))).1 hWp i
    (Finset.mem_univ i)
  exact (mul_eq_zero.1 hterms).resolve_left (hpbarpos i).ne'

/-! ### Exchange economies -/

namespace ExchangeEconomy

variable {α : Type*} [Fintype α]

/-- **Existence of Walrasian equilibrium in an exchange economy** (MWG Prop.
17.C.1, economy form). With locally nonsatiated consumers and a demand selection
on strictly positive prices whose aggregate excess demand is continuous there,
bounded below and satisfies the boundary condition, a Walrasian equilibrium with
strictly positive prices exists. (Walras' law is derived from local
nonsatiation.) -/
theorem exists_walrasianEquilibrium_of_boundaryCondition [Nonempty ι] (E : ExchangeEconomy α ι)
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d : α → (ι → ℝ) → (ι → ℝ)}
    (hd : E.IsDemandSelection d {p | PositivePrices p})
    (hc : ContinuousOn (E.excessDemand d) {p | PositivePrices p})
    (hb : ExcessBoundedBelow (E.excessDemand d)) (hbd : BoundaryCondition (E.excessDemand d)) :
    ∃ p, PositivePrices p ∧ E.IsWalrasianEquilibrium p (fun a => d a p) := by
  obtain ⟨p, hp, hz⟩ := exists_equilibrium_of_boundaryCondition hc
    (fun p hp => cost_excessDemand hlns hd hp) hb hbd
  exact ⟨p, hp, isWalrasianEquilibrium_of_excessDemand_eq_zero hd hp hz⟩

end ExchangeEconomy

end Econ
