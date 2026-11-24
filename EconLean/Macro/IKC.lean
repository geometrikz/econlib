/-
# The intertemporal Keynesian cross

Auclert, Rognlie and Straub (2024), "The Intertemporal Keynesian Cross",
JPE; Wolf (2023), "The Missing Intercept"; Kaplan–Moll–Violante (2018).

**Setting.** Time periods (or any finite index set) `t`; the household
sector's response to income is summarized by the matrix of **intertemporal
MPCs** `M`, where `M_{s t}` is the consumption response at date `s` to a unit
of disposable income at date `t`. Given a path of government spending `dG`
and taxes `dT`, demand-determined output solves the intertemporal Keynesian
cross `dY = dG + M (dY − dT)` (`IsEq`). Let `q` be the present-value
weights (`q_t = (1 + r)^{−t}`); household intertemporal budget constraints
say `qᵀ M = qᵀ`: every unit of income is eventually spent in present value.

**Results.**
* `isEq_iff`: `dY` is an equilibrium iff `(I − M) dY = dG − M dT`.
* `isEq_iff_inv`, `existsUnique_eq`: if `I − M` is invertible the
  equilibrium is unique, `dY = (I − M)⁻¹ (dG − M dT)`.
* `balanced_budget_isEq`, `balanced_budget_iff`: with `dT = dG`, `dY = dG`
  is **always** an equilibrium, for any iMPC matrix; the other equilibria
  differ from it by an element of `ker(I − M)`. `balanced_budget`: when the
  equilibrium is unique the **balanced-budget multiplier is one**.
* `pv_budget`: if `qᵀ M = qᵀ`, an equilibrium exists only if the government
  respects its intertemporal budget, `q · dG = q · dT`.
* `not_isUnit_of_pv`: but then (`q ≠ 0`) `I − M` is singular, so in finite
  dimensions the PV-consistent cross never has a unique solution; ARS select
  the bounded solution in infinite horizon. The invertible case covers
  truncated matrices (e.g. static MPCs, below).
* `static_cross`: with `M = μ I` (a static MPC `μ ≠ 1`) the cross reduces to
  `dY = (dG − μ dT)/(1 − μ)`: the textbook multiplier `1/(1 − μ)` for
  deficit-financed spending.

**Deviations.** Partial equilibrium demand block with fixed real rates (no
monetary policy response), as in ARS's baseline; the iMPC matrix is taken as
primitive rather than derived from a heterogeneous-agent model.
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace Econ
namespace IKC

open Matrix Finset

variable {ι : Type*} [Fintype ι]

/-- The intertemporal Keynesian cross. -/
def IsEq (M : Matrix ι ι ℝ) (dG dT dY : ι → ℝ) : Prop := dY = dG + M *ᵥ (dY - dT)

theorem isEq_iff (M : Matrix ι ι ℝ) (dG dT dY : ι → ℝ) :
    IsEq M dG dT dY ↔ dY - M *ᵥ dY = dG - M *ᵥ dT := by
  simp only [IsEq, mulVec_sub]
  constructor
  · intro h; funext t
    have := congrFun h t
    simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
    linarith
  · intro h; funext t
    have := congrFun h t
    simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
    linarith

/-- With `I − M` invertible, `dY` is an equilibrium iff
`dY = (I − M)⁻¹ (dG − M dT)`. -/
theorem isEq_iff_inv [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : IsUnit (1 - M).det)
    (dG dT dY : ι → ℝ) : IsEq M dG dT dY ↔ dY = (1 - M)⁻¹ *ᵥ (dG - M *ᵥ dT) := by
  rw [isEq_iff, show dY - M *ᵥ dY = (1 - M) *ᵥ dY by rw [sub_mulVec, one_mulVec]]
  constructor
  · intro h; rw [← h, mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  · intro h; rw [h, mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]

/-- **Existence and uniqueness** when `I − M` is invertible. -/
theorem existsUnique_eq [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : IsUnit (1 - M).det)
    (dG dT : ι → ℝ) : ∃! dY, IsEq M dG dT dY :=
  ⟨_, (isEq_iff_inv M hM dG dT _).2 rfl, fun _ h => (isEq_iff_inv M hM dG dT _).1 h⟩

/-- **The present-value condition makes `I − M` singular.** If
`qᵀ M = qᵀ` for some `q ≠ 0`, then `I − M` is not invertible: in finite
dimensions the cross has a nontrivial kernel, and a selection rule (ARS:
boundedness in infinite horizon) is needed for uniqueness. -/
theorem not_isUnit_of_pv [DecidableEq ι] (M : Matrix ι ι ℝ) {q : ι → ℝ} (hq0 : q ≠ 0)
    (hq : q ᵥ* M = q) : ¬ IsUnit (1 - M).det := by
  have : (1 - M).det = 0 :=
    exists_vecMul_eq_zero_iff.1 ⟨q, hq0, by rw [vecMul_sub, vecMul_one, hq, sub_self]⟩
  rw [this]; exact not_isUnit_zero

/-- **Balanced budgets: `dY = dG` is always an equilibrium**, for every iMPC
matrix (including those satisfying the present-value condition). -/
theorem balanced_budget_isEq (M : Matrix ι ι ℝ) (dG : ι → ℝ) : IsEq M dG dG dG := by
  simp [IsEq]

/-- All balanced-budget equilibria: `dY` is one iff `dY − dG` lies in the
kernel of `I − M`. -/
theorem balanced_budget_iff (M : Matrix ι ι ℝ) (dG dY : ι → ℝ) :
    IsEq M dG dG dY ↔ (dY - dG) - M *ᵥ (dY - dG) = 0 := by
  rw [isEq_iff, mulVec_sub]
  constructor
  · intro h; rw [show dY - dG - (M *ᵥ dY - M *ᵥ dG) = (dY - M *ᵥ dY) - (dG - M *ᵥ dG) by abel,
      h, sub_self]
  · intro h; rw [← sub_eq_zero, ← h]; abel

/-- **The balanced-budget multiplier is one** whenever the equilibrium is
unique (`I − M` invertible). -/
theorem balanced_budget [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : IsUnit (1 - M).det)
    {dG dY : ι → ℝ} (h : IsEq M dG dG dY) : dY = dG :=
  (existsUnique_eq M hM dG dG).unique h (balanced_budget_isEq M dG)

/-- **The present-value budget is necessary.** If households spend every
unit of income in present value (`qᵀ M = qᵀ`), an equilibrium exists only
if `q · dG = q · dT`. -/
theorem pv_budget (M : Matrix ι ι ℝ) (q : ι → ℝ) (hq : q ᵥ* M = q)
    {dG dT dY : ι → ℝ} (h : IsEq M dG dT dY) : q ⬝ᵥ dG = q ⬝ᵥ dT := by
  have h' := congrArg (fun v => q ⬝ᵥ v) h
  simp only [dotProduct_add, dotProduct_mulVec, hq, dotProduct_sub] at h'
  linarith

/-- **The static Keynesian cross.** -/
theorem static_cross {μ : ℝ} (hμ : μ ≠ 1) (dG dT dY : ι → ℝ) [DecidableEq ι] :
    IsEq (μ • (1 : Matrix ι ι ℝ)) dG dT dY ↔ dY = (1 / (1 - μ)) • (dG - μ • dT) := by
  have h1 : 1 - μ ≠ 0 := sub_ne_zero.2 (Ne.symm hμ)
  simp only [IsEq, smul_mulVec, one_mulVec]
  constructor
  · intro h; funext t
    have := congrFun h t
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    field_simp
    linarith
  · intro h; funext t
    have := congrFun h t
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    rw [this]
    field_simp
    ring


/-- With a static MPC `μ ≠ 1`, `I − M` is invertible, so `existsUnique_eq`
and `balanced_budget` apply. -/
theorem static_isUnit [DecidableEq ι] {μ : ℝ} (hμ : μ ≠ 1) :
    IsUnit (1 - μ • (1 : Matrix ι ι ℝ)).det := by
  rw [show (1 : Matrix ι ι ℝ) - μ • 1 = (1 - μ) • 1 by rw [sub_smul, one_smul], det_smul, det_one,
    mul_one]
  exact (isUnit_iff_ne_zero.2 (sub_ne_zero.2 (Ne.symm hμ))).pow _

end IKC
end Econ

end
