/-
# Inequity aversion in markets: proposer competition

Reference. E. Fehr and K. Schmidt (1999), "A Theory of Fairness,
Competition, and Cooperation", *QJE* 114(3), §III.A and Proposition 2;
experiments by Roth, Prasnikar, Okuno-Fujiwara and Zamir (1991).

**The game.** Two proposers simultaneously offer shares of a surplus of 1 to
a single responder, who accepts the highest offer `s`. Material payoffs:
the winning proposer gets `1 − s`, the losing proposer `0`, the responder
`s`. All three have Fehr–Schmidt preferences (`SocialPreferences.fs`, with
`n = 3`), with envy weight `α ≥ 0` and guilt weight `0 ≤ β < 1`.

Acceptance of the highest offer is assumed, not modelled.

**Result** (`loser_outbids`): if an offer `s ∈ [0, 1)` is accepted, the
losing proposer strictly prefers to outbid it with some `s' ∈ (s, 1]`.
Hence in any equilibrium the accepted offer is `s = 1` (the competitive
outcome), whatever the degree of inequity aversion: competition overwhelms
fairness, as observed in market experiments. Losing leaves the proposer at
the bottom with utility `−α/2` (`loser_utility`), while winning at a price
just above `s` gives strictly more (`win_utility_gt`).
-/
module

public import EconLean.Behavioral.SocialPreferences
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Algebra.Order.Group

@[expose] public section

noncomputable section

namespace Econ

namespace MarketInequity

open SocialPreferences Filter Topology

/-- Material payoffs `(winner, loser, responder)` when the winner's offer `s`
is accepted. -/
def payoffs (s : ℝ) : Fin 3 → ℝ := ![1 - s, 0, s]

/-- The losing proposer (player `1`) outbids with `s'`: now player `1` wins. -/
def deviation (s' : ℝ) : Fin 3 → ℝ := ![0, 1 - s', s']

theorem fs3 (α β : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    fs α β x i = x i - α / 2 * ∑ j, max (x j - x i) 0 - β / 2 * ∑ j, max (x i - x j) 0 := by
  simp only [fs, Fintype.card_fin]; norm_num

/-- The loser's Fehr–Schmidt utility: `−α/2`, envy toward both others. -/
theorem loser_utility (α β : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    fs α β (payoffs s) 1 = -(α / 2) := by
  rw [fs3]
  simp [payoffs, Fin.sum_univ_three, max_eq_left (sub_nonneg.2 hs1), max_eq_left hs0]
  right
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]; norm_num

/-- The deviator's utility after winning at price `s'`. -/
theorem deviation_utility (α β s' : ℝ) (hs' : s' ≤ 1) :
    fs α β (deviation s') 1 =
      (1 - s') - α / 2 * max (2 * s' - 1) 0 - β / 2 * ((1 - s') + max (1 - 2 * s') 0) := by
  rw [fs3]
  simp [deviation, Fin.sum_univ_three, max_eq_left (sub_nonneg.2 hs')]
  rw [max_eq_right (a := s' - 1) (by linarith), show s' - (1 - s') = 2 * s' - 1 by ring,
    show 1 - s' - s' = 1 - 2 * s' by ring]
  ring

theorem continuous_deviation_utility (α β : ℝ) :
    Continuous fun s' : ℝ =>
      (1 - s') - α / 2 * max (2 * s' - 1) 0 - β / 2 * ((1 - s') + max (1 - 2 * s') 0) := by
  fun_prop

/-- At the limit `s' = s`, winning beats losing. -/
theorem win_utility_gt {α β s : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1) (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    -(α / 2) < (1 - s) - α / 2 * max (2 * s - 1) 0 - β / 2 * ((1 - s) + max (1 - 2 * s) 0) := by
  rcases le_or_gt (1 / 2) s with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    nlinarith

/-- **Fehr–Schmidt (1999), Proposition 2 (key step).** If an offer
`s ∈ [0, 1)` is accepted, the losing proposer strictly gains by outbidding
it with some `s' ∈ (s, 1]`. -/
theorem loser_outbids {α β s : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1) (hs0 : 0 ≤ s)
    (hs1 : s < 1) : ∃ s', s < s' ∧ s' ≤ 1 ∧ fs α β (payoffs s) 1 < fs α β (deviation s') 1 := by
  have hc := (continuous_deviation_utility α β).continuousAt (x := s)
  have hev := hc.eventually (lt_mem_nhds (win_utility_gt hα hβ0 hβ hs0 hs1))
  have hev' : ∀ᶠ s' in 𝓝[>] s, s' ≤ 1 ∧ -(α / 2) < _ :=
    (eventually_nhdsWithin_of_eventually_nhds ((gt_mem_nhds hs1).mono fun _ h => h.le)).and
      (eventually_nhdsWithin_of_eventually_nhds hev)
  obtain ⟨s', ⟨h1, h2⟩, h3⟩ := (hev'.and self_mem_nhdsWithin).exists
  refine ⟨s', h3, h1, ?_⟩
  rw [loser_utility α β hs0 hs1.le, deviation_utility α β s' h1]
  exact h2

/-- **Only the competitive offer survives.** In any outcome where an offer
`s ∈ [0, 1]` is accepted and the losing proposer has no profitable
outbidding deviation, `s = 1`. -/
theorem competitive_offer {α β s : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β < 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1)
    (hNE : ∀ s', s < s' → s' ≤ 1 → fs α β (deviation s') 1 ≤ fs α β (payoffs s) 1) : s = 1 := by
  by_contra h
  obtain ⟨s', h1, h2, h3⟩ := loser_outbids hα hβ0 hβ hs0 (lt_of_le_of_ne hs1 h)
  exact absurd (hNE s' h1 h2) (not_le.2 h3)

/-- **The competitive outcome is immune to outbidding.** When the accepted
offer is `s = 1`, raising the offer to any `s' > 1` makes the deviator strictly
worse off. (A deviation to a lower offer loses the sale, leaving the material
payoffs, and hence the deviator's utility, unchanged when the other proposer
also offers `1`.) Together with `competitive_offer`, `s = 1` is the only offer
compatible with no profitable outbidding. Acceptance of the highest offer is
assumed throughout, not modelled. -/
theorem competitive_no_outbid {α β : ℝ} (hα : 0 ≤ α) {s' : ℝ} (hs' : 1 < s') :
    fs α β (deviation s') 1 < fs α β (payoffs 1) 1 := by
  rw [loser_utility α β zero_le_one le_rfl, fs3]
  simp [deviation, Fin.sum_univ_three]
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith)]
  nlinarith

end MarketInequity

end Econ
