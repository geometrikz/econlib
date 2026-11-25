/-
# Job-market signaling (Spence)

MWG §13.C (Lemmas 13.C.1, Props. 13.C.1–13.C.2); Spence (1973). A worker is of low or high
productivity `θL < θH`, high with prior probability `pH`. The worker chooses education `e ≥ 0`
at cost `c e θ`; education is unproductive. Competitive firms observe `e`, form a belief
`μ e` that the worker is of high type, and pay the expected productivity
`wage μ e = θL + μ e (θH − θL)`.

A pure-strategy **perfect Bayesian equilibrium** (`IsSpencePBE`) is a pair of education
choices `(eL, eH)` and a belief function `μ` such that beliefs are probabilities, beliefs on
the equilibrium path follow Bayes' rule (`0` and `1` if the types separate, `pH` if they pool),
and each type's education maximizes its wage net of cost. Off-path beliefs are free, as in
MWG.

Main results:
* `IsSpencePBE.separating_eL` (MWG Lemma 13.C.1): in a separating equilibrium the low type
  gets no education.
* `IsSpencePBE.separating_bounds`: in a separating equilibrium the high type's education
  satisfies `c eH θH − c 0 θH ≤ θH − θL ≤ c eH θL − c 0 θL`: high types are willing to pay for it, low types
  are not willing to mimic.
* `isSpencePBE_separating` (MWG Prop. 13.C.2): conversely every such `eH` is supported by
  threshold beliefs.
* `IsSpencePBE.pooling_bound`, `isSpencePBE_pooling` (MWG Prop. 13.C.1): a pooling level
  `e*` requires that the low type prefer it at the average wage to no education at
  the low wage; with nondecreasing costs and single crossing at `e*` this also suffices.
* Witness: with `c e θ = e / θ`, every `eH ∈ [θL(θH − θL), θH(θH − θL)]` is separating.

The intuitive criterion, selecting the least-cost separating equilibrium, is in
`Information/IntuitiveCriterion`.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

namespace Econ

/-- Wage paid after education `e` when firms believe the worker is of high type with
probability `μ e`. -/
def spenceWage (θL θH : ℝ) (μ : ℝ → ℝ) (e : ℝ) : ℝ := θL + μ e * (θH - θL)

/-- **Perfect Bayesian equilibrium** of the Spence game in pure strategies: types choose
`eL` and `eH`, firms hold beliefs `μ`. -/
def IsSpencePBE (θL θH pH : ℝ) (c : ℝ → ℝ → ℝ) (eL eH : ℝ) (μ : ℝ → ℝ) : Prop :=
  0 ≤ eL ∧ 0 ≤ eH ∧ (∀ e, 0 ≤ μ e ∧ μ e ≤ 1) ∧
    (eL ≠ eH → μ eL = 0 ∧ μ eH = 1) ∧ (eL = eH → μ eL = pH) ∧
    (∀ e, 0 ≤ e → spenceWage θL θH μ e - c e θL ≤ spenceWage θL θH μ eL - c eL θL) ∧
    (∀ e, 0 ≤ e → spenceWage θL θH μ e - c e θH ≤ spenceWage θL θH μ eH - c eH θH)

variable {θL θH pH : ℝ} {c : ℝ → ℝ → ℝ} {eL eH : ℝ} {μ : ℝ → ℝ}

/-- **MWG Lemma 13.C.1.** In a separating equilibrium the low type chooses no education,
if education is costly for it (`c e θL > c 0 θL` for `e > 0`). -/
theorem IsSpencePBE.separating_eL (h : IsSpencePBE θL θH pH c eL eH μ) (hsep : eL ≠ eH)
    (hlt : θL < θH) (hcost : ∀ e, 0 < e → c 0 θL < c e θL) : eL = 0 := by
  obtain ⟨heL, -, hμ, hbayes, -, hICL, -⟩ := h
  by_contra hne
  have hpos : 0 < eL := lt_of_le_of_ne heL (Ne.symm hne)
  -- Deviating to `e = 0` gives at least the low wage at a strictly lower cost.
  have hdev := hICL 0 le_rfl
  have hμ0 := (hμ 0).1
  simp only [spenceWage, (hbayes hsep).1, zero_mul, add_zero] at hdev
  have := hcost eL hpos
  nlinarith

/-- **Separating equilibria: incentive bounds.** If `eL = 0` and the types separate, the
high type's education `eH` makes mimicking unattractive for the low type,
`θH − θL ≤ c eH θL − c 0 θL`, and is worth its cost to the high type,
`c eH θH − c 0 θH ≤ θH − θL`. -/
theorem IsSpencePBE.separating_bounds (h : IsSpencePBE θL θH pH c 0 eH μ) (hsep : (0 : ℝ) ≠ eH) :
    θH - θL ≤ c eH θL - c 0 θL ∧ c eH θH - c 0 θH ≤ θH - θL := by
  obtain ⟨-, heH, hμ, hbayes, -, hICL, hICH⟩ := h
  obtain ⟨h0, h1⟩ := hbayes hsep
  have hL := hICL eH heH
  have hH := hICH 0 le_rfl
  simp only [spenceWage, h0, h1, zero_mul, add_zero, one_mul] at hL hH
  constructor <;> linarith

/-- **MWG Prop. 13.C.2 (construction).** Suppose education costs are nondecreasing in `e`
for both types. Any `eH > 0` with `c eH θH − c 0 θH ≤ θH − θL ≤ c eH θL − c 0 θL` is the high
type's education in a separating equilibrium with `eL = 0`, supported by the threshold
belief "high type iff `e ≥ eH`". -/
theorem isSpencePBE_separating (pH : ℝ)
    (hmL : MonotoneOn (fun e => c e θL) (Set.Ici 0))
    (hmH : MonotoneOn (fun e => c e θH) (Set.Ici 0)) (heH : 0 < eH)
    (hL : θH - θL ≤ c eH θL - c 0 θL) (hH : c eH θH - c 0 θH ≤ θH - θL) :
    IsSpencePBE θL θH pH c 0 eH (fun e => if eH ≤ e then 1 else 0) := by
  refine ⟨le_rfl, heH.le, fun e => ?_, fun _ => ?_, fun h => absurd h heH.ne, ?_, ?_⟩
  · simp only; split_ifs <;> norm_num
  · simp [not_le.2 heH]
  · intro e he
    simp only [spenceWage, not_le.2 heH, ite_false]
    split_ifs with hee
    · have := hmL (Set.mem_Ici.2 heH.le) (Set.mem_Ici.2 he) hee
      simp only at this
      linarith
    · have := hmL (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 he) he
      simp only at this
      linarith
  · intro e he
    simp only [spenceWage, le_refl, ite_true]
    split_ifs with hee
    · have := hmH (Set.mem_Ici.2 heH.le) (Set.mem_Ici.2 he) hee
      simp only at this
      linarith
    · have := hmH (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 he) he
      simp only at this
      linarith

/-- **Pooling equilibria: necessary condition** (MWG Prop. 13.C.1). If both types choose
`e*`, the low type must prefer `e*` at the average wage to no education at the lowest
possible wage `θL`: `θL ≤ pHθH + (1−pH)θL − (c e* θL − c 0 θL)`. -/
theorem IsSpencePBE.pooling_bound {e : ℝ} (h : IsSpencePBE θL θH pH c e e μ) (hlt : θL < θH) :
    θL ≤ θL + pH * (θH - θL) - (c e θL - c 0 θL) := by
  obtain ⟨-, -, hμ, -, hpool, hICL, -⟩ := h
  have hd := hICL 0 le_rfl
  have hμ0 := (hμ 0).1
  simp only [spenceWage, hpool rfl] at hd
  nlinarith

/-- **Pooling equilibria: construction** (MWG Prop. 13.C.1). If costs are nondecreasing in
`e` and the low type weakly prefers `e* ≥ 0` at the average wage to no education at wage `θL`,
then pooling at `e*` is an equilibrium, supported by the pessimistic belief `μ = 0` off the
path. (The high type then prefers it too, by single crossing `c e* θH − c 0 θH ≤
c e* θL − c 0 θL`.) -/
theorem isSpencePBE_pooling {e : ℝ} (hpH0 : 0 ≤ pH) (hpH1 : pH ≤ 1)
    (hmL : MonotoneOn (fun e => c e θL) (Set.Ici 0))
    (hmH : MonotoneOn (fun e => c e θH) (Set.Ici 0)) (he : 0 ≤ e)
    (hL : θL ≤ θL + pH * (θH - θL) - (c e θL - c 0 θL))
    (hsc : c e θH - c 0 θH ≤ c e θL - c 0 θL) :
    IsSpencePBE θL θH pH c e e (fun x => if x = e then pH else 0) := by
  refine ⟨he, he, fun x => ?_, fun h => absurd rfl h, fun _ => by simp, ?_, ?_⟩
  · simp only; split_ifs <;> constructor <;> linarith
  · intro x hx
    simp only [spenceWage, ite_true]
    split_ifs with hxe
    · rw [hxe]
    · have := hmL (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
      simp only at this
      linarith
  · intro x hx
    simp only [spenceWage, ite_true]
    split_ifs with hxe
    · rw [hxe]
    · have := hmH (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
      simp only at this
      linarith

/-- **Witness: linear costs `c e θ = e / θ`.** With `θL = 1`, `θH = 2`, the high type's
education `eH = 3/2 ∈ [θL(θH − θL), θH(θH − θL)] = [1, 2]` is a separating equilibrium. -/
example : IsSpencePBE 1 2 (1 / 2) (fun e θ => e / θ) 0 (3 / 2)
    (fun e => if (3 / 2 : ℝ) ≤ e then 1 else 0) := by
  refine isSpencePBE_separating (1 / 2) (fun x _ y _ hxy => ?_) (fun x _ y _ hxy => ?_)
    (by norm_num) (by norm_num) (by norm_num)
  · simp only; linarith
  · simp only; linarith

end Econ
