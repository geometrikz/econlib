/-
# The Cobb–Douglas firm of the Aiyagari model

Aiyagari (1994) §II; Ljungqvist–Sargent (LS) ch. 18.2; Acemoglu ch. 2.

A competitive firm rents capital at `r + δ` (interest plus depreciation) and
hires labor at wage `w`, producing `Y = K^α L^{1-α}`. Profit maximization
pins down the capital–labor ratio `k = K / L` from the interest rate:

  `α k^{α-1} = r + δ`, i.e. `k(r) = (α / (r + δ))^{1/(1-α)}`,

and the wage `w(r) = (1 - α) k(r)^α`. Capital demand is `K_d(r) = L k(r)`.

**Results.**
* `foc_capital`, `foc_labor`: the firm's first-order conditions hold at
  `k(r)`, `w(r)`.
* `zero_profit`: factor payments exhaust output,
  `(r + δ) K_d + w L = K_d^α L^{1-α}` (Euler's theorem for CRS).
* `continuousOn_kOfR`, `continuousOn_wage`: continuity on `r > -δ`.
* `strictAntiOn_kOfR`: capital demand falls as the interest rate rises.
* `tendsto_kOfR`, `exists_capDemand_ge`: capital demand diverges as
  `r ↓ -δ`, so any asset cap `k̄` is exceeded at some `r > -δ`. This derives
  the lower boundary condition of the Aiyagari existence argument.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace Econ

open Filter Topology Set

/-- A **Cobb–Douglas firm** `Y = K^α L^{1-α}` with depreciation rate `δ`. -/
structure CDFirm where
  α : ℝ
  δ : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1
  δ_nonneg : 0 ≤ δ

namespace CDFirm

variable (F : CDFirm)

/-- The capital–labor ratio demanded at interest rate `r`:
`k(r) = (α / (r + δ))^{1/(1-α)}`. Meaningful for `r > -δ`. -/
noncomputable def kOfR (r : ℝ) : ℝ := (F.α / (r + F.δ)) ^ (1 / (1 - F.α))

/-- The wage `w(r) = (1 - α) k(r)^α`. -/
noncomputable def wage (r : ℝ) : ℝ := (1 - F.α) * F.kOfR r ^ F.α

/-- Capital demand `K_d(r) = L k(r)` for labor input `L`. -/
noncomputable def capDemand (L r : ℝ) : ℝ := L * F.kOfR r

/-- Output `Y = K^α L^{1-α}`. -/
noncomputable def output (K L : ℝ) : ℝ := K ^ F.α * L ^ (1 - F.α)

theorem one_sub_α_pos : 0 < 1 - F.α := by linarith [F.α_lt_one]

theorem kOfR_pos {r : ℝ} (hr : -F.δ < r) : 0 < F.kOfR r :=
  Real.rpow_pos_of_pos (div_pos F.α_pos (by linarith)) _

theorem wage_pos {r : ℝ} (hr : -F.δ < r) : 0 < F.wage r :=
  mul_pos F.one_sub_α_pos (Real.rpow_pos_of_pos (F.kOfR_pos hr) _)

/-- **Firm FOC for capital**: the marginal product of capital equals the
rental rate, `α k(r)^{α-1} = r + δ`. -/
theorem foc_capital {r : ℝ} (hr : -F.δ < r) : F.α * F.kOfR r ^ (F.α - 1) = r + F.δ := by
  have hx : 0 ≤ F.α / (r + F.δ) := (div_pos F.α_pos (by linarith)).le
  have h1 : F.kOfR r ^ (F.α - 1) = (F.α / (r + F.δ)) ^ (-1 : ℝ) := by
    rw [kOfR, ← Real.rpow_mul hx]
    congr 1
    field_simp [F.one_sub_α_pos.ne']
    ring
  rw [h1, Real.rpow_neg_one, inv_div]
  field_simp [F.α_pos.ne']

/-- **Firm FOC for labor**: the marginal product of labor at ratio `k(r)` is
the wage, `(1 - α) k(r)^α = w(r)`. This holds by definition of `wage`; the
equilibrium version in terms of `K/L` is in `exists_stationary_equilibrium`. -/
theorem foc_labor (r : ℝ) : (1 - F.α) * F.kOfR r ^ F.α = F.wage r := rfl

/-- Output at `K = L k` is `L k^α` (constant returns to scale). -/
theorem output_eq {L k : ℝ} (hL : 0 < L) (hk : 0 < k) : F.output (L * k) L = L * k ^ F.α := by
  rw [output, Real.mul_rpow hL.le hk.le]
  have : L ^ F.α * L ^ (1 - F.α) = L := by
    rw [← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  calc L ^ F.α * k ^ F.α * L ^ (1 - F.α) = (L ^ F.α * L ^ (1 - F.α)) * k ^ F.α := by ring
    _ = L * k ^ F.α := by rw [this]

/-- **Zero profit** (Euler's theorem): at the optimal choices the factor
payments `(r + δ) K_d + w L` exhaust output `K_d^α L^{1-α}`. -/
theorem zero_profit {L r : ℝ} (hL : 0 < L) (hr : -F.δ < r) :
    (r + F.δ) * F.capDemand L r + F.wage r * L = F.output (F.capDemand L r) L := by
  have hk := F.kOfR_pos hr
  rw [capDemand, F.output_eq hL hk, ← F.foc_capital hr, wage]
  have : F.kOfR r ^ (F.α - 1) * F.kOfR r = F.kOfR r ^ F.α := by
    rw [Real.rpow_sub_one hk.ne', div_mul_cancel₀ _ hk.ne']
  linear_combination F.α * L * this

theorem continuousOn_kOfR : ContinuousOn F.kOfR (Ioi (-F.δ)) := by
  refine ContinuousOn.rpow_const (continuousOn_const.div (continuousOn_id.add continuousOn_const)
    fun r hr => ?_) fun _ _ => Or.inr (div_nonneg zero_le_one F.one_sub_α_pos.le)
  have : -F.δ < r := hr
  show r + F.δ ≠ 0
  linarith

theorem continuousOn_wage : ContinuousOn F.wage (Ioi (-F.δ)) :=
  continuousOn_const.mul (F.continuousOn_kOfR.rpow_const fun _ _ => Or.inr F.α_pos.le)

theorem continuousOn_capDemand (L : ℝ) : ContinuousOn (F.capDemand L) (Ioi (-F.δ)) :=
  continuousOn_const.mul F.continuousOn_kOfR

/-- **Capital demand falls with the interest rate.** -/
theorem strictAntiOn_kOfR : StrictAntiOn F.kOfR (Ioi (-F.δ)) := by
  intro r hr r' hr' hlt
  have hr0 : 0 < r + F.δ := by have : -F.δ < r := hr; linarith
  have hr0' : 0 < r' + F.δ := by have : -F.δ < r' := hr'; linarith
  exact Real.rpow_lt_rpow (div_pos F.α_pos hr0').le
    (div_lt_div_of_pos_left F.α_pos hr0 (by linarith)) (div_pos one_pos F.one_sub_α_pos)

/-- **Capital demand diverges as `r ↓ -δ`.** -/
theorem tendsto_kOfR : Tendsto F.kOfR (𝓝[>] (-F.δ)) atTop := by
  have h1 : Tendsto (fun r => r + F.δ) (𝓝[>] (-F.δ)) (𝓝[>] 0) := by
    have hc : Tendsto (fun r => r + F.δ) (𝓝 (-F.δ)) (𝓝 0) := by
      have h : Continuous fun r : ℝ => r + F.δ := by fun_prop
      have := h.tendsto (-F.δ)
      simpa using this
    refine tendsto_nhdsWithin_iff.2 ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    show 0 < r + F.δ
    have : -F.δ < r := hr
    linarith
  have h2 : Tendsto (fun r => F.α / (r + F.δ)) (𝓝[>] (-F.δ)) atTop := by
    simp_rw [div_eq_mul_inv]
    exact (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop F.α_pos
  exact (tendsto_rpow_atTop (div_pos one_pos F.one_sub_α_pos)).comp h2

/-- **Lower boundary condition, derived**: for any bound `B` and labor `L > 0`,
there are interest rates in `(-δ, r₀]` at which capital demand exceeds `B`. -/
theorem exists_capDemand_ge {L : ℝ} (hL : 0 < L) (B : ℝ) {r₀ : ℝ} (hr₀ : -F.δ < r₀) :
    ∃ r, -F.δ < r ∧ r ≤ r₀ ∧ B ≤ F.capDemand L r := by
  have hev := (F.tendsto_kOfR.eventually_ge_atTop (B / L)).and
    (Ioc_mem_nhdsGT hr₀)
  obtain ⟨r, hB, hr1, hr2⟩ := hev.exists
  refine ⟨r, hr1, hr2, ?_⟩
  rw [capDemand]
  rwa [div_le_iff₀' hL] at hB

end CDFirm

end Econ
