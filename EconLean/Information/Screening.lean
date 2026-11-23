/-
# Monopolistic screening with two types

MWG §14.C (Prop. 14.C.6 and the two-type analysis leading to it); Mussa–Rosen (1978),
Maskin–Riley (1984). A principal (seller) offers a menu of contracts `(q, t)`: quantity `q`
for payment `t`. The agent's type is `θL` with probability `pL` or `θH > θL` with probability
`pH`; type `θ` gets utility `θ v(q) − t`, and the principal earns `t − c q`.

A menu `(qL, tL), (qH, tH)` is **feasible** if it is individually rational (each type gets
at least `0`) and incentive compatible (each type prefers its own contract). Write the
**virtual surplus**
`VS(qL, qH) = pH (θH v(qH) − c qH) + pL (θL v(qL) − c qL) − pH (θH − θL) v(qL)`.

Main results:
* `screeningProfit_le`: every feasible menu earns at most `VS(qL, qH)`; the low type's
  participation constraint and the high type's incentive constraint are what bind.
* `bindingMenu_feasible`, `screeningProfit_bindingMenu`: if `v(qL) ≥ 0` and `v(qH) ≥ v(qL)`,
  the menu where those two constraints bind is feasible and earns exactly `VS(qL, qH)`.
* `IsOptimalMenu.noDistortionAtTop` (MWG Prop. 14.C.6): if the virtual surplus has
  maximizers `qL*`, `qH*` with `0 ≤ v(qL*) ≤ v(qH*)`, then in every optimal menu `qH`
  maximizes the high type's surplus `θH v(q) − c q` (it is efficient), `qL` maximizes the
  distorted surplus `pL (θL v(q) − c q) − pH (θH − θL) v(q)`, the low type gets no rent, and
  the high type's incentive constraint binds.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ

/-- A two-type screening problem. -/
structure ScreeningModel where
  θL : ℝ
  θH : ℝ
  pL : ℝ
  pH : ℝ
  c : ℝ
  v : ℝ → ℝ

namespace ScreeningModel

variable (M : ScreeningModel)

/-- A menu is **feasible**: nonnegative quantities, participation (IR) and incentive
compatibility (IC) for both types. -/
def Feasible (qL tL qH tH : ℝ) : Prop :=
  0 ≤ qL ∧ 0 ≤ qH ∧
    0 ≤ M.θL * M.v qL - tL ∧ 0 ≤ M.θH * M.v qH - tH ∧
    M.θL * M.v qH - tH ≤ M.θL * M.v qL - tL ∧ M.θH * M.v qL - tL ≤ M.θH * M.v qH - tH

/-- The principal's expected profit. -/
def profit (qL tL qH tH : ℝ) : ℝ := M.pL * (tL - M.c * qL) + M.pH * (tH - M.c * qH)

/-- Surplus from the high type. -/
def surplusH (q : ℝ) : ℝ := M.θH * M.v q - M.c * q

/-- Virtual surplus from the low type: its surplus minus the information rent conceded to
the high type. -/
def virtualL (q : ℝ) : ℝ := M.pL * (M.θL * M.v q - M.c * q) - M.pH * (M.θH - M.θL) * M.v q

/-- Virtual surplus of the quantity pair. -/
def VS (qL qH : ℝ) : ℝ := M.pH * M.surplusH qH + M.virtualL qL

/-- **Profit bound.** Every feasible menu earns at most the virtual surplus of its
quantities. -/
theorem screeningProfit_le {qL tL qH tH : ℝ} (h : M.Feasible qL tL qH tH) (hpL : 0 ≤ M.pL)
    (hpH : 0 ≤ M.pH) : M.profit qL tL qH tH ≤ M.VS qL qH := by
  obtain ⟨-, -, hIRL, -, -, hICH⟩ := h
  simp only [profit, VS, surplusH, virtualL]
  -- `tL ≤ θL v(qL)` and `tH ≤ θH v(qH) − (θH − θL) v(qL)`.
  nlinarith [mul_le_mul_of_nonneg_left (show tL ≤ M.θL * M.v qL by linarith) hpL,
    mul_le_mul_of_nonneg_left
      (show tH ≤ M.θH * M.v qH - (M.θH - M.θL) * M.v qL by linarith) hpH]

/-- Payments with the low type's IR and the high type's IC binding. -/
def tLBind (qL : ℝ) : ℝ := M.θL * M.v qL

/-- Payments with the low type's IR and the high type's IC binding. -/
def tHBind (qL qH : ℝ) : ℝ := M.θH * M.v qH - (M.θH - M.θL) * M.v qL

theorem bindingMenu_feasible {qL qH : ℝ} (hlt : M.θL ≤ M.θH) (hqL : 0 ≤ qL) (hqH : 0 ≤ qH)
    (hvL : 0 ≤ M.v qL) (hmono : M.v qL ≤ M.v qH) :
    M.Feasible qL (M.tLBind qL) qH (M.tHBind qL qH) := by
  simp only [Feasible, tLBind, tHBind]
  refine ⟨hqL, hqH, by linarith, by nlinarith, by nlinarith, by linarith⟩

theorem screeningProfit_bindingMenu (qL qH : ℝ) :
    M.profit qL (M.tLBind qL) qH (M.tHBind qL qH) = M.VS qL qH := by
  simp only [profit, VS, surplusH, virtualL, tLBind, tHBind]
  ring

/-- A feasible menu is **optimal** if no feasible menu earns more. -/
def IsOptimalMenu (qL tL qH tH : ℝ) : Prop :=
  M.Feasible qL tL qH tH ∧
    ∀ qL' tL' qH' tH', M.Feasible qL' tL' qH' tH' → M.profit qL' tL' qH' tH' ≤ M.profit qL tL qH tH

/-- **The binding menu at the virtual-surplus maximizers is optimal.** -/
theorem isOptimalMenu_binding {qL qH : ℝ} (hlt : M.θL ≤ M.θH) (hpL : 0 ≤ M.pL)
    (hpH : 0 ≤ M.pH) (hqL : 0 ≤ qL) (hqH : 0 ≤ qH) (hvL : 0 ≤ M.v qL)
    (hmono : M.v qL ≤ M.v qH) (hmaxH : ∀ q, 0 ≤ q → M.surplusH q ≤ M.surplusH qH)
    (hmaxL : ∀ q, 0 ≤ q → M.virtualL q ≤ M.virtualL qL) :
    M.IsOptimalMenu qL (M.tLBind qL) qH (M.tHBind qL qH) := by
  refine ⟨M.bindingMenu_feasible hlt hqL hqH hvL hmono, fun qL' tL' qH' tH' h' => ?_⟩
  rw [screeningProfit_bindingMenu]
  refine (M.screeningProfit_le h' hpL hpH).trans ?_
  simp only [VS]
  nlinarith [hmaxH qH' h'.2.1, hmaxL qL' h'.1, mul_le_mul_of_nonneg_left (hmaxH qH' h'.2.1) hpH]

/-- **No distortion at the top** (MWG Prop. 14.C.6). Suppose the virtual surplus has
maximizers `qL*`, `qH*` with `0 ≤ v(qL*) ≤ v(qH*)`, and `pH > 0`. Then every optimal menu
gives the high type an efficient quantity, gives the low type a quantity maximizing the
distorted surplus, leaves the low type no rent, and makes the high type's IC bind. -/
theorem IsOptimalMenu.noDistortionAtTop {qL tL qH tH qL₀ qH₀ : ℝ}
    (hopt : M.IsOptimalMenu qL tL qH tH) (hlt : M.θL ≤ M.θH) (hpL : 0 ≤ M.pL)
    (hpH : 0 < M.pH) (hqL₀ : 0 ≤ qL₀) (hqH₀ : 0 ≤ qH₀) (hvL₀ : 0 ≤ M.v qL₀)
    (hmono₀ : M.v qL₀ ≤ M.v qH₀) (hmaxH : ∀ q, 0 ≤ q → M.surplusH q ≤ M.surplusH qH₀)
    (hmaxL : ∀ q, 0 ≤ q → M.virtualL q ≤ M.virtualL qL₀) :
    (∀ q, 0 ≤ q → M.surplusH q ≤ M.surplusH qH) ∧
      (∀ q, 0 ≤ q → M.virtualL q ≤ M.virtualL qL) ∧
      tL = M.θL * M.v qL ∧ M.θH * M.v qH - tH = M.θH * M.v qL - tL := by
  obtain ⟨hfeas, hbest⟩ := hopt
  have hb := hbest _ _ _ _ (M.bindingMenu_feasible hlt hqL₀ hqH₀ hvL₀ hmono₀)
  rw [screeningProfit_bindingMenu] at hb
  have hle := M.screeningProfit_le hfeas hpL hpH.le
  have hH := hmaxH qH hfeas.2.1
  have hL := hmaxL qL hfeas.1
  -- `VS(qL₀, qH₀) ≤ profit ≤ VS(qL, qH) ≤ VS(qL₀, qH₀)`: all equalities.
  simp only [VS] at hb hle
  have hHeq : M.surplusH qH = M.surplusH qH₀ := by nlinarith
  have hLeq : M.virtualL qL = M.virtualL qL₀ := by nlinarith
  obtain ⟨-, -, hIRL, -, -, hICH⟩ := hfeas
  refine ⟨fun q hq => hHeq ▸ hmaxH q hq, fun q hq => hLeq ▸ hmaxL q hq, ?_, ?_⟩
  · -- profit equals the bound, so both slack terms vanish.
    simp only [profit, surplusH, virtualL] at hb hle hHeq hLeq
    nlinarith
  · simp only [profit, surplusH, virtualL] at hb hle hHeq hLeq
    nlinarith

/-- **Witness.** `v(q) = q − q²/2`, `θL = 1`, `θH = 2`, `pL = 3/4`, `pH = 1/4`, `c = 1/2`: the
efficient high-type quantity is `3/4`, the low type's quantity is distorted down to `1/4`
(its efficient quantity would be `1/2`), and the binding menu is optimal. -/
example : (ScreeningModel.mk 1 2 (3 / 4) (1 / 4) (1 / 2) fun q => q - q ^ 2 / 2).IsOptimalMenu
    (1 / 4) ((ScreeningModel.mk 1 2 (3 / 4) (1 / 4) (1 / 2) fun q => q - q ^ 2 / 2).tLBind (1 / 4))
    (3 / 4)
    ((ScreeningModel.mk 1 2 (3 / 4) (1 / 4) (1 / 2) fun q => q - q ^ 2 / 2).tHBind (1 / 4) (3 / 4)) := by
  refine isOptimalMenu_binding _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun q _ => ?_) (fun q _ => ?_)
  · simp only [surplusH]; nlinarith [sq_nonneg (q - 3 / 4)]
  · simp only [virtualL]; nlinarith [sq_nonneg (q - 1 / 4)]

end ScreeningModel

end Econ
