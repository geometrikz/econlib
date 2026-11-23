/-
# Collateral constraints and amplification (Kiyotaki–Moore)

Kiyotaki and Moore (1997), "Credit Cycles", JPE, §2–3 (static version of the
amplification mechanism); Brunnermeier–Eisenbach–Sannikov (2013), §2.

**Setting.** Constrained entrepreneurs hold land `k`. They can borrow only
against the value of land, so they buy as much as their net worth allows:
`k = n/d`, where `d > 0` is the down payment per unit of land (the land
price less what can be borrowed against it). Net worth is the value of their
inherited land plus its output, net of debt:
`n = (a + q) K̄ − B`, with productivity `a`, land price `q`, the
entrepreneurs' inherited landholdings `K̄ > 0` (not aggregate land) and debt
`B`. The down payment `d` stands in for the user cost `q − q'/R` of the
dynamic model. The land market clears with unconstrained
users, giving a price that rises with entrepreneurs' demand,
`q = q₀ + φ k` with `φ ≥ 0` (`IsEq`). Stability requires `d > φ K̄`.

**Results.**
* `existsUnique_eq`, `k_eq`: equilibrium holdings are
  `k = (a K̄ + q₀ K̄ − B)/(d − φ K̄)`.
* `response`: a productivity change `Δa` changes holdings by
  `Δk = K̄ Δa/(d − φ K̄)`.
* `kEq_nonneg_iff`: holdings are non-negative iff net worth at the
  fundamental price, `(a + q₀) K̄ − B`, is.
* `amplification` (static, within-period): when the land price responds (`φ > 0`) the response
  exceeds the direct (partial-equilibrium) effect `K̄ Δa/d`: falling land
  prices erode collateral and net worth, which lowers demand further, a
  multiplier `d/(d − φ K̄) > 1`.

**Deviations.** Static, linear version of the collateral feedback; the
dynamic Kiyotaki–Moore persistence (shocks to net worth propagate through
future land prices) is not formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace Econ
namespace KiyotakiMoore

/-- Parameters of the static collateral economy. -/
structure Params where
  d : ℝ
  Kbar : ℝ
  B : ℝ
  q₀ : ℝ
  φ : ℝ
  hK : 0 < Kbar
  hφ : 0 ≤ φ
  hstab : φ * Kbar < d

namespace Params

variable (P : Params)

/-- Equilibrium land holdings `k` and price `q` at productivity `a`. -/
def IsEq (a k q : ℝ) : Prop := P.d * k = (a + q) * P.Kbar - P.B ∧ q = P.q₀ + P.φ * k

theorem den_pos : 0 < P.d - P.φ * P.Kbar := by linarith [P.hstab]

/-- Equilibrium holdings. -/
def kEq (a : ℝ) : ℝ := (a * P.Kbar + P.q₀ * P.Kbar - P.B) / (P.d - P.φ * P.Kbar)

theorem kEq_spec (a : ℝ) :
    P.kEq a * (P.d - P.φ * P.Kbar) = a * P.Kbar + P.q₀ * P.Kbar - P.B :=
  div_mul_cancel₀ _ P.den_pos.ne'

theorem k_eq {a k q : ℝ} (h : P.IsEq a k q) : k = P.kEq a := by
  obtain ⟨h1, h2⟩ := h
  rw [kEq, eq_div_iff P.den_pos.ne']
  rw [h2] at h1
  linear_combination h1

/-- Holdings are feasible (`k ≥ 0`) iff net worth at `q₀` is non-negative. -/
theorem kEq_nonneg_iff (a : ℝ) : 0 ≤ P.kEq a ↔ 0 ≤ (a + P.q₀) * P.Kbar - P.B := by
  rw [kEq, div_nonneg_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · linarith
    · linarith [P.den_pos]
  · intro h; left; exact ⟨by linarith, P.den_pos.le⟩

theorem existsUnique_eq (a : ℝ) : ∃! kq : ℝ × ℝ, P.IsEq a kq.1 kq.2 := by
  refine ⟨(P.kEq a, P.q₀ + P.φ * P.kEq a), ⟨?_, rfl⟩, fun kq hkq => ?_⟩
  · linear_combination P.kEq_spec a
  · have hk := P.k_eq hkq
    exact Prod.ext hk (by rw [hkq.2, hk])

/-- **Response to productivity.** -/
theorem response {a a' k k' q q' : ℝ} (h : P.IsEq a k q) (h' : P.IsEq a' k' q') :
    k' - k = P.Kbar * (a' - a) / (P.d - P.φ * P.Kbar) := by
  rw [P.k_eq h, P.k_eq h', kEq, kEq]
  have := P.den_pos.ne'
  field_simp; ring

/-- **Amplification (static).** With a price feedback (`φ > 0`), the equilibrium
response to a productivity increase `Δa > 0` strictly exceeds the direct
effect at a fixed land price, `K̄ Δa/d`. -/
theorem amplification (hφ : 0 < P.φ) {a a' k k' q q' : ℝ} (ha : a < a')
    (h : P.IsEq a k q) (h' : P.IsEq a' k' q') :
    P.Kbar * (a' - a) / P.d < k' - k := by
  rw [P.response h h']
  have hd0 : 0 < P.d - P.φ * P.Kbar := P.den_pos
  have hd : 0 < P.d := by nlinarith [P.hK]
  apply div_lt_div_of_pos_left (mul_pos P.hK (by linarith)) hd0
  nlinarith [P.hK]

end Params
end KiyotakiMoore
end Econ

end
