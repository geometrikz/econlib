/-
# Gains from trade: the Arkolakis–Costinot–Rodríguez-Clare formula

Arkolakis, Costinot and Rodríguez-Clare (2012), "New Trade Models, Same Old
Gains?", AER; Armington (1969); Costinot–Rodríguez-Clare (2014, Handbook).

**Setting (Armington/CES gravity).** Countries `i, j` in a finite set. Country
`i` produces its good with labour at productivity `Aᵢ > 0` and wage
`wᵢ > 0`; shipping to `j` costs an iceberg factor `τᵢⱼ > 0` with `τⱼⱼ = 1`.
Consumers have CES preferences with elasticity `σ > 1`, so (with `ε = σ − 1`,
the trade elasticity) the price index of `j` is
`Pⱼ = (Σᵢ (τᵢⱼ wᵢ/Aᵢ)^{−ε})^{−1/ε}` and `j`'s expenditure share on its own
good is `λⱼⱼ = (wⱼ/Aⱼ)^{−ε} / Σᵢ (τᵢⱼ wᵢ/Aᵢ)^{−ε}`.

**Results.**
* `realWage_eq`: real income per worker is `wⱼ/Pⱼ = Aⱼ λⱼⱼ^{−1/ε}`: welfare
  depends on trade only through the domestic share and the trade elasticity.
* `acr`: hence the welfare change between any two equilibria (different trade
  costs, wages in other countries, ...) with the same `Aⱼ` is
  `(λ'ⱼⱼ/λⱼⱼ)^{−1/ε}` — the ACR formula.
* `gains_from_trade`: relative to autarky (`λⱼⱼ = 1`), the gains are
  `λⱼⱼ^{−1/ε} ≥ 1`.

**Deviations.** No equilibrium conditions (trade balance, labour-market
clearing) are imposed: wages are free parameters, so `acr` is the ACR
sufficient-statistic identity, valid between any two configurations with the
same `Aⱼ` and `ε`, in particular between equilibria. Armington taste weights
are normalised to one and `τᵢⱼ ≥ 1` is not required.
Armington (perfect competition, one good per country) only;
ACR show the same formula holds for Krugman and Melitz–Pareto models, which
are not formalized. Wages are taken as given (the formula holds for any
wages, in particular equilibrium ones).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

namespace Econ
namespace ACR

open Real Finset

/-- A CES/Armington trade environment. -/
structure World (ι : Type*) [Fintype ι] where
  A : ι → ℝ
  w : ι → ℝ
  τ : ι → ι → ℝ
  /-- Trade elasticity `ε = σ − 1`. -/
  ε : ℝ
  hA : ∀ i, 0 < A i
  hw : ∀ i, 0 < w i
  hτ : ∀ i j, 0 < τ i j
  hτjj : ∀ j, τ j j = 1
  hε : 0 < ε

namespace World

variable {ι : Type*} [Fintype ι] (W : World ι)

/-- `Σᵢ (τᵢⱼ wᵢ/Aᵢ)^{−ε}`. -/
def S (j : ι) : ℝ := ∑ i, (W.τ i j * W.w i / W.A i) ^ (-W.ε)

theorem S_pos (j : ι) : 0 < W.S j := by
  have hj : (W.w j / W.A j) ^ (-W.ε) ≤ W.S j := by
    have := single_le_sum (f := fun i => (W.τ i j * W.w i / W.A i) ^ (-W.ε))
      (fun i _ => (rpow_pos_of_pos (div_pos (mul_pos (W.hτ i j) (W.hw i)) (W.hA i)) _).le)
      (mem_univ j)
    simpa [S, W.hτjj] using this
  exact lt_of_lt_of_le (rpow_pos_of_pos (div_pos (W.hw j) (W.hA j)) _) hj

/-- CES price index. -/
def P (j : ι) : ℝ := W.S j ^ (-W.ε)⁻¹

/-- Domestic expenditure share. -/
def lamjj (j : ι) : ℝ := (W.w j / W.A j) ^ (-W.ε) / W.S j

theorem lamjj_pos (j : ι) : 0 < W.lamjj j :=
  div_pos (rpow_pos_of_pos (div_pos (W.hw j) (W.hA j)) _) (W.S_pos j)

theorem lamjj_le_one (j : ι) : W.lamjj j ≤ 1 := by
  rw [lamjj, div_le_one (W.S_pos j)]
  have := single_le_sum (f := fun i => (W.τ i j * W.w i / W.A i) ^ (-W.ε))
    (fun i _ => (rpow_pos_of_pos (div_pos (mul_pos (W.hτ i j) (W.hw i)) (W.hA i)) _).le)
    (mem_univ j)
  simpa [S, W.hτjj] using this

/-- **Welfare is pinned down by the domestic share.** -/
theorem realWage_eq (j : ι) : W.w j / W.P j = W.A j * W.lamjj j ^ (-W.ε)⁻¹ := by
  have hε : -W.ε ≠ 0 := neg_ne_zero.2 W.hε.ne'
  have hc : 0 < W.w j / W.A j := div_pos (W.hw j) (W.hA j)
  rw [lamjj, div_rpow (rpow_pos_of_pos hc _).le (W.S_pos j).le, rpow_rpow_inv hc.le hε, P]
  have := (W.hA j).ne'
  field_simp

/-- **The ACR formula.** Two equilibria with the same domestic productivity:
the welfare ratio is `(λ'ⱼⱼ/λⱼⱼ)^{−1/ε}`. -/
theorem acr (W' : World ι) (j : ι) (hA : W'.A j = W.A j) (hε : W'.ε = W.ε) :
    (W'.w j / W'.P j) / (W.w j / W.P j) = (W'.lamjj j / W.lamjj j) ^ (-W.ε)⁻¹ := by
  rw [W.realWage_eq, W'.realWage_eq, hA, hε,
    div_rpow (W'.lamjj_pos j).le (W.lamjj_pos j).le]
  have := (W.hA j).ne'
  have := (rpow_pos_of_pos (W.lamjj_pos j) (-W.ε)⁻¹).ne'
  field_simp

/-- **Gains from trade** relative to autarky are at least one. -/
theorem gains_from_trade (j : ι) : W.A j ≤ W.w j / W.P j := by
  rw [W.realWage_eq]
  have : 1 ≤ W.lamjj j ^ (-W.ε)⁻¹ :=
    one_le_rpow_of_pos_of_le_one_of_nonpos (W.lamjj_pos j) (W.lamjj_le_one j)
      (inv_nonpos.2 (neg_nonpos.2 W.hε.le))
  nlinarith [W.hA j]

end World
end ACR
end Econ

end
