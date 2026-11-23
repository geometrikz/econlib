/-
# Costly state verification: the optimality of standard debt

Townsend (1979), "Optimal Contracts and Competitive Markets with Costly State
Verification", JET; Gale and Hellwig (1985), REStud; the contract underlying
Bernanke–Gertler–Gilchrist (1999).

**Setting.** A project yields a return `ω` in a finite set of states `S`
(with probabilities `p ≥ 0`). The entrepreneur observes `ω`; the lender
observes it only by paying a verification cost. A (deterministic) contract
specifies a set `V` of announced states that trigger verification and a
repayment `R(ω)`. It must satisfy limited liability `R(ω) ≤ ω` and incentive
compatibility (`IsIC`): in no state can the entrepreneur gain by announcing a
different, unverified state `ω'` whose repayment she can afford
(`R(ω') ≤ ω`).

A **standard debt contract** with face value `D` verifies exactly the default
states `ω < D` and repays `min(ω, D)`.

**Results.**
* `debt_isIC`: standard debt is incentive compatible with limited liability.
* `debt_dominates`: for every incentive-compatible contract with limited
  liability in which some state is unverified, standard debt with face value
  equal to the unverified repayment verifies **no more** states and pays the
  lender **at least as much** in every state (Townsend; Gale–Hellwig).
* `debt_dominates_expected`: hence weakly lower expected verification cost
  and weakly higher expected repayment.
* `debt_optimal`: for **every** IC, limited-liability contract (including
  one that verifies all states) some standard debt contract has the same
  expected repayment and weakly lower expected verification cost
  (lowering the face value by the intermediate value theorem).
* `debt_optimal_pc`: so if a contract satisfies the lender's participation
  constraint (net of verification costs), a debt contract does too and gives
  the entrepreneur the same expected payoff: the optimal contract can be
  taken to be standard debt.

**Deviations.** Deterministic verification, risk-neutral parties, finite
state space; the lender bears verification costs. `IsIC` constrains only
reports of unverified states: verification reveals the true state, and a
detected lie is assumed punishable down to the limited-liability bound.
Returns are not required to be non-negative.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.MinMax
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Order.Group.Indicator

@[expose] public section

noncomputable section

namespace Econ
namespace CSV

open Finset

/-- A contract: verification set and repayment schedule. -/
structure Contract where
  V : Set ℝ
  R : ℝ → ℝ

/-- Limited liability on the state space `S`. -/
def LL (S : Finset ℝ) (C : Contract) : Prop := ∀ ω ∈ S, C.R ω ≤ ω

/-- Incentive compatibility: no state gains by announcing an affordable
unverified state. -/
def IsIC (S : Finset ℝ) (C : Contract) : Prop :=
  ∀ ω ∈ S, ∀ ω' ∈ S, ω' ∉ C.V → C.R ω' ≤ ω → C.R ω ≤ C.R ω'

/-- Standard debt with face value `D`. -/
def debt (D : ℝ) : Contract := ⟨{ω | ω < D}, fun ω => min ω D⟩

/-- **Standard debt is incentive compatible** with limited liability. -/
theorem debt_isIC (S : Finset ℝ) (D : ℝ) : LL S (debt D) ∧ IsIC S (debt D) := by
  refine ⟨fun ω _ => min_le_left _ _, fun ω _ ω' _ hω' hpay => ?_⟩
  simp only [debt, Set.mem_ofPred_eq, not_lt] at hω' hpay ⊢
  rw [min_eq_right hω'] at hpay ⊢
  exact min_le_right _ _

/-- **Debt dominates.** Let `C` be IC with limited liability and let `ω₀ ∈ S`
be unverified. With `D = R(ω₀)`, standard debt verifies a subset of `C`'s
verified states and repays at least `R(ω)` in every state. -/
theorem debt_dominates {S : Finset ℝ} {C : Contract} (hLL : LL S C) (hIC : IsIC S C)
    {ω₀ : ℝ} (h₀ : ω₀ ∈ S) (hv : ω₀ ∉ C.V) :
    (∀ ω ∈ S, ω ∈ (debt (C.R ω₀)).V → ω ∈ C.V) ∧
    ∀ ω ∈ S, C.R ω ≤ (debt (C.R ω₀)).R ω := by
  set D := C.R ω₀
  -- all unverified states repay `D`
  have hconst : ∀ ω ∈ S, ω ∉ C.V → C.R ω = D := by
    intro ω hω hωv
    have hLω := hLL ω hω
    have hL₀ := hLL ω₀ h₀
    refine le_antisymm (by_contra fun hlt => ?_) (by_contra fun hlt => ?_)
    · push Not at hlt
      have := hIC ω hω ω₀ h₀ hv (by linarith)
      linarith
    · push Not at hlt
      have := hIC ω₀ h₀ ω hω hωv (by linarith)
      linarith
  refine ⟨fun ω hω hver => ?_, fun ω hω => ?_⟩
  · -- a default state `ω < D` cannot be unverified (it could not pay `D`)
    by_contra hωv
    have := hconst ω hω hωv
    have := hLL ω hω
    simp only [debt, Set.mem_ofPred_eq] at hver
    linarith
  · simp only [debt]
    by_cases hωv : ω ∈ C.V
    · by_cases hωD : D ≤ ω
      · rw [min_eq_right hωD]
        exact hIC ω hω ω₀ h₀ hv hωD
      · push Not at hωD
        rw [min_eq_left hωD.le]; exact hLL ω hω
    · rw [hconst ω hω hωv]
      have := hconst ω hω hωv
      have := hLL ω hω
      exact le_min (by linarith) le_rfl

/-- Expected repayment to the lender. -/
def expRepay (S : Finset ℝ) (p : ℝ → ℝ) (C : Contract) : ℝ := ∑ ω ∈ S, p ω * C.R ω

/-- Expected verification cost, at cost `κ` per verified state. -/
def expVerif (S : Finset ℝ) (p : ℝ → ℝ) (κ : ℝ) (C : Contract) : ℝ :=
  ∑ ω ∈ S, p ω * C.V.indicator (fun _ => κ) ω

/-- The entrepreneur's expected payoff. -/
def entPayoff (S : Finset ℝ) (p : ℝ → ℝ) (C : Contract) : ℝ := ∑ ω ∈ S, p ω * (ω - C.R ω)

/-- The lender's participation constraint: expected repayment net of
verification costs covers the loan `I`. -/
def LenderPC (S : Finset ℝ) (p : ℝ → ℝ) (κ I : ℝ) (C : Contract) : Prop :=
  I ≤ expRepay S p C - expVerif S p κ C

theorem expVerif_le {S : Finset ℝ} {p : ℝ → ℝ} (hp : ∀ ω ∈ S, 0 ≤ p ω) {κ : ℝ} (hκ : 0 ≤ κ)
    {C C' : Contract} (h : ∀ ω ∈ S, ω ∈ C.V → ω ∈ C'.V) :
    expVerif S p κ C ≤ expVerif S p κ C' := by
  refine sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left ?_ (hp ω hω)
  by_cases hv : ω ∈ C.V
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (h ω hω hv)]
  · rw [Set.indicator_of_notMem hv]
    exact Set.indicator_nonneg (fun _ _ => hκ) ω

/-- **Debt dominates in expectation** (given an unverified state). -/
theorem debt_dominates_expected {S : Finset ℝ} (p : ℝ → ℝ) (hp : ∀ ω ∈ S, 0 ≤ p ω) {κ : ℝ}
    (hκ : 0 ≤ κ) {C : Contract} (hLL : LL S C) (hIC : IsIC S C) {ω₀ : ℝ} (h₀ : ω₀ ∈ S)
    (hv : ω₀ ∉ C.V) :
    expVerif S p κ (debt (C.R ω₀)) ≤ expVerif S p κ C ∧
      expRepay S p C ≤ expRepay S p (debt (C.R ω₀)) := by
  obtain ⟨h1, h2⟩ := debt_dominates hLL hIC h₀ hv
  exact ⟨expVerif_le hp hκ h1,
    sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left (h2 ω hω) (hp ω hω)⟩

/-- **Optimality of standard debt** (Townsend; Gale–Hellwig). For every
incentive-compatible contract with limited liability there is a standard debt
contract with the **same** expected repayment and weakly **lower** expected
verification cost. -/
theorem debt_optimal {S : Finset ℝ} (hne : S.Nonempty) {p : ℝ → ℝ} (hp : ∀ ω ∈ S, 0 ≤ p ω)
    {κ : ℝ} (hκ : 0 ≤ κ) {C : Contract} (hLL : LL S C) (hIC : IsIC S C) :
    ∃ D, expRepay S p (debt D) = expRepay S p C ∧ expVerif S p κ (debt D) ≤ expVerif S p κ C := by
  set f : ℝ → ℝ := fun D => expRepay S p (debt D) with hf
  have hmono : Monotone f := fun D D' h =>
    sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left (min_le_min_left _ h) (hp ω hω)
  have hcont : Continuous f :=
    continuous_finsetSum _ fun ω _ => continuous_const.mul (continuous_const.min continuous_id)
  -- a face value whose debt verifies only `C`-verified states and repays at least as much
  obtain ⟨D₀, hV₀, hR₀⟩ : ∃ D₀, (∀ ω ∈ S, ω < D₀ → ω ∈ C.V) ∧ expRepay S p C ≤ f D₀ := by
    by_cases hall : ∃ ω₀ ∈ S, ω₀ ∉ C.V
    · obtain ⟨ω₀, h₀, hv⟩ := hall
      obtain ⟨h1, h2⟩ := debt_dominates hLL hIC h₀ hv
      exact ⟨C.R ω₀, h1, sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left (h2 ω hω) (hp ω hω)⟩
    · push Not at hall
      refine ⟨S.sup' hne id, fun ω hω _ => hall ω hω, sum_le_sum fun ω hω =>
        mul_le_mul_of_nonneg_left ?_ (hp ω hω)⟩
      exact le_min (hLL ω hω) ((hLL ω hω).trans (le_sup' id hω))
  -- a face value whose debt repays at most as much
  set Dl := S.inf' hne C.R
  have hRl : f (min Dl D₀) ≤ expRepay S p C :=
    (hmono (min_le_left _ _)).trans (sum_le_sum fun ω hω =>
      mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (inf'_le _ hω)) (hp ω hω))
  obtain ⟨D, hD, hfD⟩ := intermediate_value_Icc (min_le_right Dl D₀) hcont.continuousOn
    ⟨hRl, hR₀⟩
  refine ⟨D, hfD, expVerif_le hp hκ fun ω hω hlt => hV₀ ω hω (lt_of_lt_of_le hlt hD.2)⟩

/-- **Debt is an optimal contract.** If an IC, limited-liability contract
satisfies the lender's participation constraint, some standard debt contract
also does, and gives the entrepreneur the same expected payoff; since debt
saves verification costs, the optimum can always be taken to be debt. -/
theorem debt_optimal_pc {S : Finset ℝ} (hne : S.Nonempty) {p : ℝ → ℝ} (hp : ∀ ω ∈ S, 0 ≤ p ω)
    {κ I : ℝ} (hκ : 0 ≤ κ) {C : Contract} (hLL : LL S C) (hIC : IsIC S C)
    (hPC : LenderPC S p κ I C) :
    ∃ D, LL S (debt D) ∧ IsIC S (debt D) ∧ LenderPC S p κ I (debt D) ∧
      entPayoff S p (debt D) = entPayoff S p C := by
  obtain ⟨D, h1, h2⟩ := debt_optimal hne hp hκ hLL hIC
  refine ⟨D, (debt_isIC S D).1, (debt_isIC S D).2, ?_, ?_⟩
  · unfold LenderPC at *; linarith
  · simp only [entPayoff, mul_sub, sum_sub_distrib]
    simp only [expRepay] at h1
    rw [h1]

end CSV
end Econ

end
