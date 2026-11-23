/-
# Gross substitutes: preserved by aggregation, and it buys uniqueness

PLAN.md §7.2a (bridge B0, "which micro restrictions escape SMD"), row
"Gross substitutes". MWG Def. 17.F.2, Prop. 17.F.3; Arrow, Block & Hurwicz
(1959).

**The economics.** The Sonnenschein–Mantel–Debreu theorem says the standard
consumer axioms put almost no restriction on aggregate excess demand, so
equilibrium need not be unique. Gross substitutability is one of the few
restrictions that (i) survives adding up consumers and (ii) does buy
uniqueness.

An excess demand function `z`, defined on strictly positive prices, has the
**gross substitutes property** if raising the price of one good `l` (holding
the others fixed) strictly raises the excess demand for every *other* good
`k ≠ l` (MWG Def. 17.F.2).

Results:
1. **Preserved under summation** (`GrossSubstitutes.add`, `GrossSubstitutes.sum`):
   the sum of gross-substitute excess demands is gross substitute. So it is a
   property one can check consumer by consumer.
2. **Monotone path lemma** (MWG Lemma 17.F.2-style): if `p ≤ p'` coordinatewise,
   `p ≠ p'` and `p_k = p'_k`, then `z_k(p') > z_k(p)`. Raise the prices one
   good at a time.
3. **Uniqueness** (MWG Prop. 17.F.3): with homogeneity of degree zero, a
   gross-substitute excess demand has at most one equilibrium up to scale:
   if `z(p) = z(p') = 0` then `p' = t p` for some `t > 0`.
-/
module

public import EconLean.Consumer.Budget
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Econ

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Strictly positive price vectors, the domain of excess demand in MWG §17.B. -/
def PositivePrices (p : ι → ℝ) : Prop := ∀ i, 0 < p i

/-- **Gross substitutes** (MWG Def. 17.F.2): on strictly positive prices,
raising only the price of good `l` strictly raises excess demand for every
other good. -/
def GrossSubstitutes (z : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∀ p l (t : ℝ), PositivePrices p → p l < t →
    ∀ k, k ≠ l → z p k < z (Function.update p l t) k

/-- **Homogeneity of degree zero** of excess demand on positive prices
(MWG Prop. 17.B.2(i)). -/
def HomogeneousZero (z : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∀ p, PositivePrices p → ∀ t : ℝ, 0 < t → z (t • p) = z p

/-! ### 1. Preservation under aggregation -/

/-- The sum of two gross-substitute excess demands is gross substitute. -/
theorem GrossSubstitutes.add {z₁ z₂ : (ι → ℝ) → (ι → ℝ)} (h₁ : GrossSubstitutes z₁)
    (h₂ : GrossSubstitutes z₂) : GrossSubstitutes (z₁ + z₂) := by
  intro p l t hp hlt k hk
  simp only [Pi.add_apply]
  linarith [h₁ p l t hp hlt k hk, h₂ p l t hp hlt k hk]

/-- **Gross substitutes is preserved under aggregation**: if every consumer's
excess demand is gross substitute (and there is at least one consumer), so is
the aggregate. -/
theorem GrossSubstitutes.sum {α : Type*} (s : Finset α) (hs : s.Nonempty)
    {z : α → (ι → ℝ) → (ι → ℝ)} (h : ∀ a ∈ s, GrossSubstitutes (z a)) :
    GrossSubstitutes (fun p => ∑ a ∈ s, z a p) := by
  intro p l t hp hlt k hk
  simp only [Finset.sum_apply]
  exact Finset.sum_lt_sum_of_nonempty hs fun a ha => h a ha p l t hp hlt k hk

/-! ### 2. Raising several prices at once -/

/-- Prices equal to `p'` on `S` and to `p` elsewhere. -/
def mixPrices (S : Finset ι) (p p' : ι → ℝ) : ι → ℝ := fun i => if i ∈ S then p' i else p i

/-- **Monotone path, finite-set form.** If `p ≤ p'` are positive and `k ∉ S`,
then switching the prices in `S` from `p` to `p'` weakly raises `z_k`, and
strictly if some price in `S` actually rises. -/
theorem GrossSubstitutes.le_mixPrices {z : (ι → ℝ) → (ι → ℝ)} (hGS : GrossSubstitutes z)
    {p p' : ι → ℝ} (hp : PositivePrices p) (hle : p ≤ p') {k : ι} :
    ∀ S : Finset ι, k ∉ S →
      z p k ≤ z (mixPrices S p p') k ∧ ((∃ i ∈ S, p i < p' i) → z p k < z (mixPrices S p p') k) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have : mixPrices ∅ p p' = p := by funext i; simp [mixPrices]
    simp [this]
  | insert l S hlS ih =>
    intro hk
    have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
    have hkl : k ≠ l := fun h => hk (h ▸ Finset.mem_insert_self l S)
    obtain ⟨ih₁, ih₂⟩ := ih hkS
    -- The new price vector is the old one with `l`'s price raised to `p' l`.
    have hupd : mixPrices (insert l S) p p' = Function.update (mixPrices S p p') l (p' l) := by
      funext i
      by_cases hil : i = l
      · subst hil; simp [mixPrices]
      · simp [mixPrices, hil]
    have hpos : PositivePrices (mixPrices S p p') := fun i => by
      unfold mixPrices; split_ifs
      · exact lt_of_lt_of_le (hp i) (hle i)
      · exact hp i
    have hold : mixPrices S p p' l = p l := by simp [mixPrices, hlS]
    rcases (hle l).lt_or_eq with hlt | heq
    · -- Price of `l` strictly rises: strict increase by gross substitutes.
      have hstep := hGS (mixPrices S p p') l (p' l) hpos (by rw [hold]; exact hlt) k hkl
      rw [hupd]
      exact ⟨ih₁.trans hstep.le, fun _ => lt_of_le_of_lt ih₁ hstep⟩
    · -- Price of `l` unchanged: nothing moves.
      have hsame : Function.update (mixPrices S p p') l (p' l) = mixPrices S p p' := by
        rw [← heq, ← hold, Function.update_eq_self]
      rw [hupd, hsame]
      refine ⟨ih₁, fun ⟨i, hi, hlt⟩ => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hiS
      · exact absurd heq hlt.ne
      · exact ih₂ ⟨i, hiS, hlt⟩

/-- **Monotone path lemma.** If `p ≤ p'` are positive, `p ≠ p'`, and the price
of good `k` is the same in both, then `z_k(p') > z_k(p)`. -/
theorem GrossSubstitutes.lt_of_le [Fintype ι] {z : (ι → ℝ) → (ι → ℝ)} (hGS : GrossSubstitutes z)
    {p p' : ι → ℝ} (hp : PositivePrices p) (hle : p ≤ p') (hne : p ≠ p') {k : ι}
    (hk : p k = p' k) : z p k < z p' k := by
  have hmix : mixPrices (Finset.univ.erase k) p p' = p' := by
    funext i
    by_cases hik : i = k
    · subst hik; simp [mixPrices, hk]
    · simp [mixPrices, hik]
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ p' i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hik : i ≠ k := fun h => hi (h ▸ hk)
  have := (hGS.le_mixPrices hp hle (Finset.univ.erase k) (Finset.notMem_erase k _)).2
    ⟨i, Finset.mem_erase.2 ⟨hik, Finset.mem_univ i⟩, lt_of_le_of_ne (hle i) hi⟩
  rwa [hmix] at this

/-! ### 3. Uniqueness of equilibrium (MWG Prop. 17.F.3) -/

/-- **Uniqueness of Walrasian equilibrium under gross substitutes**
(MWG Prop. 17.F.3). If `z` is homogeneous of degree zero and has the gross
substitutes property, any two strictly positive equilibrium price vectors are
proportional.

Proof: scale `p'` by `λ = maxᵢ pᵢ / p'ᵢ`, attained at `k`. Then `λ p' ≥ p` with
equality at `k`. If `λ p' ≠ p`, the monotone path lemma gives
`z_k(λ p') > z_k(p) = 0`, but `z(λ p') = z(p') = 0`. -/
theorem GrossSubstitutes.unique_equilibrium [Fintype ι] [Nonempty ι] {z : (ι → ℝ) → (ι → ℝ)}
    (hGS : GrossSubstitutes z) (hhom : HomogeneousZero z) {p p' : ι → ℝ}
    (hp : PositivePrices p) (hp' : PositivePrices p') (hz : z p = 0) (hz' : z p' = 0) :
    ∃ t : ℝ, 0 < t ∧ p' = t • p := by
  obtain ⟨k, -, hkmax⟩ := Finset.exists_max_image Finset.univ (fun i => p i / p' i)
    Finset.univ_nonempty
  set lam := p k / p' k with hlam
  have hlam0 : 0 < lam := div_pos (hp k) (hp' k)
  set q := lam • p' with hq
  have hqpos : PositivePrices q := fun i => by simp [hq]; exact mul_pos hlam0 (hp' i)
  have hle : p ≤ q := by
    intro i
    have := hkmax i (Finset.mem_univ i)
    simp only [hq, Pi.smul_apply, smul_eq_mul]
    rw [div_le_iff₀ (hp' i)] at this
    linarith
  have hk : p k = q k := by
    simp only [hq, Pi.smul_apply, smul_eq_mul, hlam]
    field_simp [(hp' k).ne']
  have hzq : z q = 0 := by rw [hq, hhom p' hp' lam hlam0, hz']
  by_cases hpq : p = q
  · refine ⟨lam⁻¹, inv_pos.2 hlam0, ?_⟩
    rw [hpq, hq, smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
  · have := hGS.lt_of_le hp hle hpq hk
    rw [hz, hzq] at this
    exact absurd this (lt_irrefl _)

end Econ
