/-
# Independent statement review: findings checked in Lean

Machine-checked evidence for the cross-library adversarial review of
2026-11-23 (`Audit/REVIEW-independent.md`). Each item compiles with no `sorry`.
These are diagnostics, not results: each shows a hypothesis that standard
objects fail, or a conclusion weaker than the textbook's.
-/
module

public import EconLean.GE.Examples
public import EconLean.GE.Existence
public import EconLean.Bridges.Aggregation.Examples
public import EconLean.Macro.Growth.Ramsey
public import EconLean.Macro.DP.MarkovChain
public import EconLean.Macro.Labor.HosiosDiscounted

@[expose] public section

open Econ Econ.ExchangeEconomy Econ.GEExamples Econ.AggregationExamples Set Matrix

noncomputable section

namespace Econ.IndependentFindings

/-! ### I1. Existence of equilibrium cannot be applied to the library's own linear economy.
`exists_freeDisposalEquilibrium(_two_goods)` assume a demand selection on the
whole closed price simplex. At a corner price a strongly monotone consumer has
no demand (the free good is wanted without bound), so no selection exists. -/
theorem mem_simplex_e0 : (![1, 0] : Fin 2 → ℝ) ∈ priceSimplex (Fin 2) := by
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · simp [Fin.sum_univ_two]

/-- The linear economy used in the welfare examples has no demand selection on the simplex, so
`exists_freeDisposalEquilibrium(_two_goods)` cannot be applied to it. At p = (1,0), good 1 is
free and demand is empty. -/
theorem linEconomy_no_demandSelection :
    ¬ ∃ d, linEconomy.IsDemandSelection d (priceSimplex (Fin 2)) := by
  rintro ⟨d, hd⟩
  obtain ⟨⟨hx0, hxc⟩, hmax⟩ := hd _ mem_simplex_e0 0
  set x := d 0 ![1, 0] with hxdef
  have hy : x + ![0, 1] ∈ budgetSet ![1, 0] (linEconomy.wealth ![1, 0] 0) := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hx0 0
      · have := hx0 1; simp at this ⊢; linarith
    · rw [cost_add_right]
      have : cost (![1, 0] : Fin 2 → ℝ) ![0, 1] = 0 := by simp [cost, Fin.sum_univ_two]
      linarith
  have hle := hmax _ hy
  change uLin (x + ![0, 1]) ≤ uLin x at hle
  simp [uLin] at hle
  linarith

/-! ### I2. The library's own excess demand `zCD` violates `LawOfDemand` on positive prices.
So `LawOfDemand.excessWARP` is never exercised by the bridge's own example; the
law of demand is only meaningful on normalised prices (e.g. the simplex). -/
example : ¬ LawOfDemand zCD {p | PositivePrices p} := by
  intro h
  have hp : PositivePrices (![1, 3] : Fin 2 → ℝ) := by
    intro i; fin_cases i <;> norm_num
  have hp' : PositivePrices (![1/10, 2/10] : Fin 2 → ℝ) := by
    intro i; fin_cases i <;> norm_num
  have hne : zCD ![1, 3] ≠ zCD ![1/10, 2/10] := by
    intro he
    have := congrFun he 0
    simp [zCD] at this
  have := h _ hp _ hp' hne
  simp [cost, zCD, Fin.sum_univ_two] at this
  norm_num at this

/-! ### I3. RCK: every model's optimal policy fixes k = 0.
`optimal_capital_converges` says only that capital converges to *some* fixed
point of the policy, which is consistent with convergence to 0; the textbook
result is convergence to the modified-golden-rule k* > 0. -/
example (M : RCKModel) (g : M.S → M.S) (hg : ∀ k, M.toDynProg.policy k = {g k}) :
    g ⟨0, le_rfl, M.kbar_pos.le⟩ = ⟨0, le_rfl, M.kbar_pos.le⟩ := by
  have h := M.toDynProg.policy_subset ⟨0, le_rfl, M.kbar_pos.le⟩
  rw [hg] at h
  have hm : g ⟨0, le_rfl, M.kbar_pos.le⟩ ∈ M.Γ ⟨0, le_rfl, M.kbar_pos.le⟩ := h rfl
  have h1 : ((g ⟨0, le_rfl, M.kbar_pos.le⟩ : M.S) : ℝ) ≤ M.f 0 := hm
  rw [M.f_zero] at h1
  exact Subtype.ext (le_antisymm h1 (g ⟨0, le_rfl, M.kbar_pos.le⟩).2.1)

-- Hence the existential `∃ kinf, g kinf = kinf ∧ ...` in `optimal_capital_converges`
-- is already witnessed (for k₀ = 0) by the zero steady state; nothing in the file rules out
-- `kinf = 0` for k₀ > 0. What the textbook asserts and is NOT stated:

/-! ### I4. `doeblin` needs every one-step transition probability ≥ ε > 0.
This ergodic chain (Q² > 0) satisfies Doeblin's condition (SLP Thm 11.4) but
not the library's hypothesis. -/
noncomputable def Q2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1/2, 1/2]

example : IsStochastic Q2 ∧ ¬ ∃ ε > (0 : ℝ), ∀ z z', ε ≤ Q2 z z' := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z z'; fin_cases z <;> fin_cases z' <;> norm_num [Q2]
  · intro z; fin_cases z <;> norm_num [Q2, Fin.sum_univ_two]
  · rintro ⟨ε, hε, h⟩
    have := h 0 0
    norm_num [Q2] at this
    linarith

/-! ### I5. Discrete DMP: `Feasible` allowed a vacancy-filling probability above 1.
In the file's own parameterisation, θ = 1/100 has q(θ) = 5/2. **Fixed:** `Feasible`
and `IsSearchEqm` now require `f(θ) ≤ 1` and `q(θ) ≤ 1`, so this path is no
longer feasible. -/
noncomputable def exD : DMP.Discrete :=
  ⟨⟨1 / 4, 1 / 2, 1 / 10, 1, 1, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩, 9 / 10, by norm_num, by norm_num, by norm_num⟩

-- θ = 1/100 has vacancy-filling rate q(θ) = 5/2 > 1, and is now infeasible.
example : 1 < exD.fillRate (1 / 100) ∧ ¬ exD.Feasible (fun _ => 1 / 100) := by
  have h : ((1 / 100 : ℝ) ^ (1 / 2 : ℝ)) = 1 / 10 := by
    rw [show (1 / 100 : ℝ) = (1 / 10) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h' : ((1 / 100 : ℝ) ^ (-(1 / 2) : ℝ)) = 10 := by
    rw [Real.rpow_neg (by norm_num), h]; norm_num
  have hq : 1 < exD.fillRate (1 / 100) := by
    simp only [DMP.Economy.fillRate, exD]
    norm_num [h']
  exact ⟨hq, fun hf => absurd (hf 0).2.2 (not_le.2 hq)⟩

end Econ.IndependentFindings
