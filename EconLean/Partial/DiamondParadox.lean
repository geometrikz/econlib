/-
# The Diamond paradox

Diamond (1971); Tirole, *The Theory of Industrial Organization*, §2.6 (Supplementary
section on search). `n` identical firms with marginal cost `c` sell a homogeneous good to
consumers with unit demand and value `u > c`. Each consumer sees one firm's price for free;
seeing another costs `s > 0`.

In a symmetric profile in which all firms charge `p`, a consumer who sees a price `q` at the
firm she visits keeps searching (or drops out) if `q > u` or if `q > p + s`, since searching
costs `s` and is expected to yield price `p`. So a firm deviating to `q` keeps its `1/n`
share of consumers iff `q ≤ u` and `q ≤ p + s`; consumers who first visit other firms see
`p` and do not search further.

* `diamond_paradox`: however small the search cost, the unique symmetric equilibrium price
  is the monopoly price `u`.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Econ

/-- Profit of a firm charging `q` when all other firms charge `p`. -/
noncomputable def searchProfit (n c u s p q : ℝ) : ℝ :=
  if q ≤ u ∧ q ≤ p + s then (q - c) / n else 0

/-- All firms charging `p` is a **symmetric equilibrium**: no firm gains by deviating. -/
def IsSearchEq (n c u s p : ℝ) : Prop := ∀ q, searchProfit n c u s p q ≤ searchProfit n c u s p p

/-- **The Diamond paradox.** With any positive search cost, all firms charging `p` is an
equilibrium if and only if `p` is the monopoly price `u`. -/
theorem diamond_paradox {n c u s : ℝ} (hn : 0 < n) (hcu : c < u) (hs : 0 < s) (p : ℝ) :
    IsSearchEq n c u s p ↔ p = u := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- Raise the price to `min u (p + s) > p` without losing customers.
      set q := min u (p + s)
      have hq1 : q ≤ u := min_le_left _ _
      have hq2 : q ≤ p + s := min_le_right _ _
      have hpq : p < q := lt_min hlt (by linarith)
      have := h q
      simp only [searchProfit, hq1, hq2, and_self, ↓reduceIte, hlt.le,
        le_add_iff_nonneg_right, hs.le] at this
      have : (q - c) / n ≤ (p - c) / n := this
      have := (div_le_div_iff_of_pos_right hn).1 this
      linarith
    · -- Nobody buys at `p > u`; charging `u` sells.
      have := h u
      have h1 : ¬ (p ≤ u ∧ p ≤ p + s) := fun h' => absurd h'.1 (not_le.2 hgt)
      have h2 : u ≤ p + s := by linarith
      simp only [searchProfit, le_refl, true_and, h1, h2, ↓reduceIte] at this
      have : 0 < (u - c) / n := div_pos (by linarith) hn
      linarith
  · rintro rfl q
    have hp : searchProfit n c p s p p = (p - c) / n := by
      simp [searchProfit, hs.le]
    rw [hp]
    unfold searchProfit
    split_ifs with hq
    · exact div_le_div_of_nonneg_right (by linarith [hq.1]) hn.le
    · exact div_nonneg (by linarith) hn.le

end Econ
