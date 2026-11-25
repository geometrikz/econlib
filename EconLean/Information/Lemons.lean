/-
# Adverse selection: Akerlof's market for lemons

MWG §13.B (Example 13.B.1 and Prop. 13.B.1); Akerlof (1970). Used cars have quality `θ`,
distributed according to a simple lottery `F`. A seller of quality `θ` values the car at
`θ`; buyers value a car of quality `θ` at `θ` too, but cannot observe it. At a price `p`
exactly the owners of cars with `θ ≤ p` sell, so buyers are willing to pay the average
quality of the cars on offer, `E[θ | θ ≤ p]`. A **competitive equilibrium** with trade is
a price with a positive mass of cars offered and `p = E[θ | θ ≤ p]`.

**Unravelling** (`isLemonsEq_iff`): an equilibrium with trade exists only at the lowest
quality, `p = min supp F`, and only cars of that quality trade. Every car above the worst
is withdrawn. (Here sellers and buyers value quality equally, `r(θ) = θ`, so the market is thin
but no surplus is lost; the welfare-loss version with `r(θ) < θ` is in
`Information/LemonsGains.lean`.)
-/
module

public import EconLean.Uncertainty.MoneyLottery
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Econ

open Finset SimpleLottery

/-- Probability that the quality is at most `p` (the share of cars offered at price `p`). -/
noncomputable def offeredMass (F : SimpleLottery) (p : ℝ) : ℝ :=
  F.expect fun x => if x ≤ p then 1 else 0

/-- Total quality of the cars offered at price `p`, `E[θ · 1{θ ≤ p}]`. -/
noncomputable def offeredQuality (F : SimpleLottery) (p : ℝ) : ℝ :=
  F.expect fun x => if x ≤ p then x else 0

/-- **Competitive equilibrium with trade** in the lemons market: some cars are offered and
the price equals the expected quality of the cars offered. -/
def IsLemonsEq (F : SimpleLottery) (p : ℝ) : Prop :=
  0 < offeredMass F p ∧ offeredQuality F p = p * offeredMass F p

/-- **Akerlof's unravelling** (MWG Example 13.B.1 with `r(θ) = θ`): `p` is an equilibrium
price with trade iff it is the lowest quality in the support. -/
theorem isLemonsEq_iff (F : SimpleLottery) (p : ℝ) :
    IsLemonsEq F p ↔ p = F.prob.support.min' F.support_nonempty := by
  set S := F.prob.support
  set m := S.min' F.support_nonempty
  -- `E[(θ - p) 1{θ ≤ p}] = 0` and every term is `≤ 0`.
  have hdiff : offeredQuality F p - p * offeredMass F p =
      ∑ x ∈ S, F.prob x * (if x ≤ p then x - p else 0) := by
    simp only [offeredQuality, offeredMass, expect_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  constructor
  · rintro ⟨hpos, heq⟩
    have hzero : ∑ x ∈ S, F.prob x * (if x ≤ p then x - p else 0) = 0 := by
      rw [← hdiff, heq, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonpos fun x _ => by
      split_ifs with h
      · exact mul_nonpos_of_nonneg_of_nonpos (F.nonneg x) (by linarith)
      · simp).1 hzero
    -- Every support point `≤ p` equals `p`.
    have hall : ∀ x ∈ S, x ≤ p → x = p := fun x hx hxp => by
      have h := hterm x hx
      simp only [hxp, ↓reduceIte] at h
      rcases mul_eq_zero.1 h with h0 | h0
      · exact absurd h0 (Finsupp.mem_support_iff.1 hx)
      · linarith
    -- Some support point is `≤ p`, since the offered mass is positive.
    obtain ⟨x, hx, hxp⟩ : ∃ x ∈ S, x ≤ p := by
      by_contra h
      push Not at h
      have : offeredMass F p = 0 := by
        simp only [offeredMass, expect_eq_sum]
        exact Finset.sum_eq_zero fun x hx => by simp [not_le.2 (h x hx)]
      linarith
    have hxp' := hall x hx hxp
    subst hxp'
    exact (hall m (S.min'_mem _) (S.min'_le x hx)).symm
  · rintro rfl
    have hm : m ∈ S := S.min'_mem _
    -- Only the lowest quality is offered.
    have honly : ∀ x ∈ S, x ≤ m → x = m := fun x hx hxm => le_antisymm hxm (S.min'_le x hx)
    refine ⟨?_, ?_⟩
    · simp only [offeredMass, expect_eq_sum]
      refine Finset.sum_pos' (fun x _ => ?_) ⟨m, hm, ?_⟩
      · split_ifs <;> simp [F.nonneg x]
      · simp only [le_refl, ↓reduceIte, mul_one]
        exact lt_of_le_of_ne (F.nonneg m) (Ne.symm (Finsupp.mem_support_iff.1 hm))
    · have hzero : ∑ x ∈ S, F.prob x * (if x ≤ m then x - m else 0) = 0 :=
        Finset.sum_eq_zero fun x hx => by
          split_ifs with h
          · rw [honly x hx h, sub_self, mul_zero]
          · rw [mul_zero]
      linarith

/-- In any equilibrium with trade, only cars of the equilibrium quality are offered. -/
theorem IsLemonsEq.only_worst {F : SimpleLottery} {p : ℝ} (h : IsLemonsEq F p) :
    ∀ x ∈ F.prob.support, x ≤ p → x = p := by
  rw [isLemonsEq_iff] at h
  subst h
  exact fun x hx hxm => le_antisymm hxm (Finset.min'_le _ x hx)

end Econ
