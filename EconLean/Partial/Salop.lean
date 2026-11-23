/-
# Spatial competition on the circle (Salop 1979)

Salop (1979); Tirole, *The Theory of Industrial Organization*, §7.1.2. A unit mass of
consumers is spread uniformly on a circle of circumference `1`. `n` firms with marginal cost
`c` sit at equal distances `1/n`; a consumer at distance `x` from a firm pays its price plus
transport cost `t x` and buys one unit from the firm with the lowest delivered price.

If both neighbours charge `p` and a firm charges `q` with `|q − p| ≤ t/n`, the consumer
between them at distance `x` from it is indifferent when `q + t x = p + t (1/n − x)`, so the
firm sells to `2x = 1/n + (p − q)/t` consumers (the **local demand**). Further undercutting
(`q < p − t/n`) steals the neighbours' whole market and more; the demand there is not
needed below because, at the equilibrium price, such a `q` is below marginal cost.

Main results:
* `salop_equilibrium`: when its neighbours charge `p* = c + t/n`, a firm's profit is
  maximized at `p*`, against any demand that equals the local demand (truncated at `0`) for
  prices at or above `c` and is nonnegative elsewhere. Equilibrium profit is `t/n²`.
* `salop_free_entry`: with entry cost `F`, profits vanish at `nᵉ = √(t/F)`.
* `salop_social_optimum` and `salop_excess_entry`: total cost `n F + t/(4n)` (entry plus
  transport) is minimized at `n° = √(t/F)/2`, so free entry gives twice the efficient number
  of firms.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

/-- The local demand of a firm charging `q` whose neighbours charge `p`, truncated at `0`. -/
noncomputable def salopLocalDemand (n t p q : ℝ) : ℝ := max 0 (1 / n + (p - q) / t)

/-- **Symmetric equilibrium of the Salop model.** If both neighbours charge `c + t/n`, no
price earns more than `c + t/n` itself, whose profit is `t/n²`. The deviant's demand `D` may
be anything nonnegative below marginal cost (where undercutting steals the neighbours'
markets) and is the local demand at prices `q ≥ c`. -/
theorem salop_equilibrium {n t c : ℝ} (hn : 0 < n) (ht : 0 < t) (D : ℝ → ℝ)
    (hD0 : ∀ q, 0 ≤ D q) (hloc : ∀ q, c ≤ q → D q = salopLocalDemand n t (c + t / n) q) :
    D (c + t / n) = 1 / n ∧ (c + t / n - c) * D (c + t / n) = t / n ^ 2 ∧
      ∀ q, (q - c) * D q ≤ t / n ^ 2 := by
  have hD : D (c + t / n) = 1 / n := by
    rw [hloc _ (by have : 0 < t / n := by positivity
                   linarith), salopLocalDemand, sub_self, zero_div, add_zero]
    exact max_eq_right (by positivity)
  refine ⟨hD, by rw [hD]; field_simp; ring, fun q => ?_⟩
  rcases lt_or_ge q c with hq | hq
  · have : (q - c) * D q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hD0 q)
    exact this.trans (by positivity)
  rw [hloc q hq, salopLocalDemand]
  rcases le_total (1 / n + (c + t / n - q) / t) 0 with h | h
  · rw [max_eq_left h, mul_zero]; positivity
  · rw [max_eq_right h]
    have e : (q - c) * (1 / n + (c + t / n - q) / t) =
        t / n ^ 2 - (q - c - t / n) ^ 2 / t := by field_simp; ring
    rw [e]
    have : 0 ≤ (q - c - t / n) ^ 2 / t := by positivity
    linarith

/-- **Free entry.** With entry cost `F > 0`, equilibrium profit net of entry cost,
`t/n² − F`, is zero for a positive number of firms `n` exactly when `n = √(t/F)`. -/
theorem salop_free_entry {t F n : ℝ} (ht : 0 < t) (hF : 0 < F) (hn : 0 < n) :
    t / n ^ 2 - F = 0 ↔ n = Real.sqrt (t / F) := by
  constructor
  · intro h
    have : n ^ 2 = t / F := by
      field_simp at h ⊢; linarith
    rw [← this, Real.sqrt_sq hn.le]
  · rintro rfl
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    ring

/-- Total transport cost with `n` equally spaced firms: each of the `2n` half-arcs of length
`1/(2n)` between a firm and the midpoint to its neighbour contributes `∫₀^{1/(2n)} t x dx`. -/
noncomputable def salopTransportCost (n t : ℝ) : ℝ :=
  2 * n * ∫ x in (0 : ℝ)..1 / (2 * n), t * x

lemma salopTransportCost_eq {n t : ℝ} (hn : 0 < n) : salopTransportCost n t = t / (4 * n) := by
  simp only [salopTransportCost]
  rw [intervalIntegral.integral_const_mul, integral_id]
  field_simp
  ring

/-- **The efficient number of firms** minimizes entry plus transport cost
`n F + t/(4n)`; it is `√(t/F)/2`. -/
theorem salop_social_optimum {t F : ℝ} (ht : 0 < t) (hF : 0 < F) {m : ℝ} (hm : 0 < m) :
    Real.sqrt (t / F) / 2 * F + salopTransportCost (Real.sqrt (t / F) / 2) t ≤
      m * F + salopTransportCost m t := by
  have hs : 0 < Real.sqrt (t / F) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (t / F) ^ 2 = t / F := Real.sq_sqrt (by positivity)
  rw [salopTransportCost_eq (by positivity), salopTransportCost_eq hm]
  set r := Real.sqrt (t / F)
  have ht' : t = r ^ 2 * F := by rw [hs2]; field_simp
  rw [ht']
  rw [show r / 2 * F + r ^ 2 * F / (4 * (r / 2)) = r * F by field_simp; ring]
  -- `m F + r² F/(4m) − r F = F (2m − r)²/(4m) ≥ 0`.
  have : m * F + r ^ 2 * F / (4 * m) - r * F = F * (2 * m - r) ^ 2 / (4 * m) := by
    field_simp; ring
  have : 0 ≤ F * (2 * m - r) ^ 2 / (4 * m) := by positivity
  linarith

/-- **Excess entry** (Salop 1979): if `nᵉ > 0` is a zero-profit number of firms
(`t / nᵉ² = F`) and `n° > 0` minimizes entry plus transport cost over all positive numbers of
firms, then `nᵉ = 2 n°`. -/
theorem salop_excess_entry {t F ne no : ℝ} (ht : 0 < t) (hF : 0 < F) (hne : 0 < ne)
    (hzero : t / ne ^ 2 = F) (hno : 0 < no)
    (hmin : ∀ m > 0, no * F + salopTransportCost no t ≤ m * F + salopTransportCost m t) :
    ne = 2 * no := by
  set r := Real.sqrt (t / F)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = t / F := Real.sq_sqrt (by positivity)
  -- `nᵉ = r`.
  have hne' : ne = r := by
    have : ne ^ 2 = t / F := by
      rw [← hzero]; field_simp
    rw [← Real.sqrt_sq hne.le, this]
  -- `n° = r / 2`: the cost gap to `r / 2` is `F (2n° − r)² / (4 n°)`.
  have hmin' := hmin (r / 2) (by positivity)
  rw [salopTransportCost_eq hno, salopTransportCost_eq (by positivity)] at hmin'
  have ht' : t = r ^ 2 * F := by rw [hr2]; field_simp
  rw [ht'] at hmin'
  have e1 : r / 2 * F + r ^ 2 * F / (4 * (r / 2)) = r * F := by field_simp; ring
  have e2 : no * F + r ^ 2 * F / (4 * no) - r * F = F * (2 * no - r) ^ 2 / (4 * no) := by
    field_simp; ring
  have h0 : F * (2 * no - r) ^ 2 / (4 * no) ≤ 0 := by linarith
  have h1 : (2 * no - r) ^ 2 = 0 := by
    have hpos : 0 ≤ F * (2 * no - r) ^ 2 / (4 * no) := by positivity
    have : F * (2 * no - r) ^ 2 / (4 * no) = 0 := le_antisymm h0 hpos
    rcases div_eq_zero_iff.1 this with h | h
    · exact (mul_eq_zero.1 h).resolve_left hF.ne'
    · exact absurd h (by positivity)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  linarith

end Econ
