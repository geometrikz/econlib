/-
# Risk attitudes under rank-dependent utility

References. M. Yaari (1987), "The Dual Theory of Choice under Risk",
*Econometrica* 55(1); S. Chew, E. Karni and Z. Safra (1987), "Risk Aversion
in the Theory of Expected Utility with Rank Dependent Probabilities", *JET*
42(2); P. Wakker (2010), *Prospect Theory for Risk and Ambiguity*, §6.

Builds on `RankDependent.lean` (grid lotteries, `rdu`, `eu`, layer forms).
Throughout `w` is a probability weighting function with `w 0 = 0` and
`w 1 = 1`.

**Results.**
* `rdu_le_eu_iff` (**pessimism**): `w t ≤ t` for all `t ∈ [0, 1]` iff, for
  every grid size and every utility increasing on the grid, RDU is at most
  expected utility for every lottery. `eu_le_rdu_iff`: the optimistic
  mirror image (`t ≤ w t`).
* `rdu_le_u_mean` (**weak risk aversion**, sufficiency): with monetary
  outcomes `x`, a concave utility `U` (with `U ∘ x` increasing on the grid) and a pessimistic `w`, the RDU of every lottery is
  at most the utility of its mean, `U (E x)`. With `U` linear this is Yaari's
  dual theory, where pessimism is also necessary (`rdu_le_eu_iff` with
  `u = x`).
* `pessimism_of_riskAverse` (**Chew–Karni–Safra**, necessity): if the RDU
  agent with utility `U` is weakly risk averse on two-outcome lotteries near
  some wealth level `x₀` at which `U` is differentiable with `U'(x₀) > 0`,
  then `w t ≤ t` for all `t ∈ [0, 1]` (the stake bound `ε` may depend on
  `t`, and only lotteries with lower outcome `x₀` are used). So under RDU, weak risk aversion forces
  pessimistic probability weighting, whatever the curvature of `U`.
* Examples: `w t = t²` is pessimistic, so its RDU never exceeds expected
  utility (`sq_pessimistic`, `rdu_sq_le_eu`). A weighting function that
  overweights some probability (`t < w t`; e.g. inverse-S weighting for
  small `t`, not formalized here) makes a linear-utility (Yaari) agent
  strictly risk seeking on a two-outcome lottery, violating weak risk
  aversion (`yaari_riskSeeking`).

**Scope.** Strong risk aversion (aversion to mean-preserving spreads, which
under RDU requires convex `w` and concave `U`) is not formalized.
-/
module

public import EconLean.Behavioral.RankDependent
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

namespace Econ

namespace RankDependent

open Finset Filter Topology

/-- The two-outcome lottery on the grid `{0, 1}` paying the better outcome
with probability `t`. -/
noncomputable def binLot (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Lottery 1 where
  p k := if k = 0 then 1 - t else if k = 1 then t else 0
  nonneg k := by split_ifs <;> linarith
  sum_eq_one := by simp [sum_range_succ]
  eq_zero_of_lt k hk := by
    have h0 : k ≠ 0 := by omega
    have h1 : k ≠ 1 := by omega
    simp [h0, h1]

theorem G_binLot (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : G (binLot t ht0 ht1) 1 = t := by
  simp [G, binLot]

theorem rdu_binLot {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) (u : ℕ → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rdu w u (binLot t ht0 ht1) = u 0 + w t * (u 1 - u 0) := by
  rw [rdu_eq_layer hw0 hw1]; simp [G_binLot]

theorem eu_binLot (u : ℕ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eu u (binLot t ht0 ht1) = u 0 + t * (u 1 - u 0) := by
  rw [eu_eq_layer]; simp [G_binLot]

/-- **Pessimism**: `w t ≤ t` on `[0, 1]` iff RDU never exceeds expected
utility (for increasing utilities on any grid). -/
theorem rdu_le_eu_iff {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≤ t) ↔
      ∀ (n : ℕ) (u : ℕ → ℝ), MonotoneOnGrid n u → ∀ p : Lottery n, rdu w u p ≤ eu u p := by
  constructor
  · intro h n u hu p
    rw [rdu_eq_layer hw0 hw1, eu_eq_layer]
    gcongr with k hk
    · exact sub_nonneg.2 (hu k (mem_range.1 hk))
    · exact h _ ⟨G_nonneg p _, G_le_one p _⟩
  · intro h t ht
    have := h 1 (fun k => if k = 0 then 0 else 1) (fun k hk => by
      have : k = 0 := by omega
      subst this; simp) (binLot t ht.1 ht.2)
    rw [rdu_binLot hw0 hw1, eu_binLot] at this
    simpa using this

/-- **Optimism**, the mirror image: `t ≤ w t` on `[0, 1]` iff RDU is never
below expected utility. -/
theorem eu_le_rdu_iff {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, t ≤ w t) ↔
      ∀ (n : ℕ) (u : ℕ → ℝ), MonotoneOnGrid n u → ∀ p : Lottery n, eu u p ≤ rdu w u p := by
  constructor
  · intro h n u hu p
    rw [rdu_eq_layer hw0 hw1, eu_eq_layer]
    gcongr with k hk
    · exact sub_nonneg.2 (hu k (mem_range.1 hk))
    · exact h _ ⟨G_nonneg p _, G_le_one p _⟩
  · intro h t ht
    have := h 1 (fun k => if k = 0 then 0 else 1) (fun k hk => by
      have : k = 0 := by omega
      subst this; simp) (binLot t ht.1 ht.2)
    rw [rdu_binLot hw0 hw1, eu_binLot] at this
    simpa using this

/-- **Weak risk aversion** (sufficiency): pessimistic weighting and a concave
utility of money make the RDU of every lottery at most the utility of its
mean. -/
theorem rdu_le_u_mean {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hpess : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≤ t) {n : ℕ} {x : ℕ → ℝ} {U : ℝ → ℝ}
    (hU : ConcaveOn ℝ Set.univ U) (hUx : MonotoneOnGrid n (U ∘ x)) (p : Lottery n) :
    rdu w (U ∘ x) p ≤ U (eu x p) := by
  refine ((rdu_le_eu_iff hw0 hw1).1 hpess n _ hUx p).trans ?_
  have := hU.le_map_sum (t := range (n + 1)) (w := p.p) (p := x)
    (fun k _ => p.nonneg k) p.sum_eq_one (fun k _ => Set.mem_univ _)
  simpa [eu, smul_eq_mul] using this

/-- **Chew–Karni–Safra: weak risk aversion forces pessimism.** If the RDU
agent with utility of money `U` weakly prefers the mean to every two-outcome
lottery `(x₀, x₀ + h)` with small stakes `h ∈ (0, ε)`, and `U` is
differentiable at `x₀` with `U'(x₀) > 0`, then `w t ≤ t` on `[0, 1]`. -/
theorem pessimism_of_riskAverse {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) {U : ℝ → ℝ}
    {x₀ d : ℝ} (hd : HasDerivAt U d x₀) (hdpos : 0 < d)
    (hRA : ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1), ∃ ε > 0, ∀ h, 0 < h → h < ε →
      rdu w (fun k : ℕ => U (x₀ + k * h)) (binLot t ht0 ht1) ≤
        U (eu (fun k : ℕ => x₀ + k * h) (binLot t ht0 ht1))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≤ t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · simp [hw0]
  obtain ⟨ε, hε, hRA⟩ := hRA t ht.1 ht.2
  have hs : Tendsto (fun h => h⁻¹ • (U (x₀ + h) - U x₀)) (𝓝[>] 0) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope_zero.1 hd).mono_left
      (nhdsWithin_mono _ fun h (hh : 0 < h) => ne_of_gt hh)
  have hmul : Tendsto (fun h : ℝ => t * h) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)),
      eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => mul_pos htpos hh⟩
  have lim1 := hs.const_mul (w t)
  have lim2 := (hs.comp hmul).const_mul t
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), w t * (h⁻¹ • (U (x₀ + h) - U x₀)) ≤
      t * ((fun h => h⁻¹ • (U (x₀ + h) - U x₀)) ∘ (fun h : ℝ => t * h)) h := by
    filter_upwards [Ioo_mem_nhdsGT hε] with h hh
    have key := hRA h hh.1 hh.2
    rw [rdu_binLot hw0 hw1, eu_binLot] at key
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] at key
    have key' : w t * (U (x₀ + h) - U x₀) ≤ U (x₀ + t * h) - U x₀ := by
      have e : x₀ + t * (x₀ + h - x₀) = x₀ + t * h := by ring
      rw [e] at key; linarith
    simp only [Function.comp, smul_eq_mul]
    have hh0 : 0 < h := hh.1
    rw [show t * ((t * h)⁻¹ * (U (x₀ + t * h) - U x₀)) = h⁻¹ * (U (x₀ + t * h) - U x₀) by
      field_simp, show w t * (h⁻¹ * (U (x₀ + h) - U x₀)) = h⁻¹ * (w t * (U (x₀ + h) - U x₀)) by
      ring]
    exact mul_le_mul_of_nonneg_left key' (inv_nonneg.2 hh0.le)
  have := le_of_tendsto_of_tendsto lim1 lim2 hev
  exact le_of_mul_le_mul_right this hdpos

/-- Non-vacuity: `w t = t²` is pessimistic. -/
theorem sq_pessimistic : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ^ 2 ≤ t := fun t ht => by
  nlinarith [ht.1, ht.2]

/-- `w t = t²`: RDU never exceeds expected utility. -/
theorem rdu_sq_le_eu {n : ℕ} {u : ℕ → ℝ} (hu : MonotoneOnGrid n u) (p : Lottery n) :
    rdu (fun t => t ^ 2) u p ≤ eu u p :=
  (rdu_le_eu_iff (by norm_num) (by norm_num)).1 sq_pessimistic n u hu p

/-- **Optimistic weighting makes a Yaari agent risk seeking**: if
`t < w t`, the linear-utility RDU value of the lottery paying `1` with
probability `t` and `0` otherwise strictly exceeds its mean `t`. -/
theorem yaari_riskSeeking {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hover : t < w t) :
    eu (fun k : ℕ => (k : ℝ)) (binLot t ht0 ht1) < rdu w (fun k : ℕ => (k : ℝ)) (binLot t ht0 ht1) := by
  rw [rdu_binLot hw0 hw1, eu_binLot]; simpa using hover

end RankDependent

end Econ
