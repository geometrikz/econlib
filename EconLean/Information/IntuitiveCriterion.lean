/-
# The intuitive criterion in the Spence signaling model (Cho–Kreps 1987)

Cho and Kreps (1987), "Signaling games and stable equilibria", QJE; MWG §13.C (pp. 469–473,
the intuitive criterion); Riley (1979). The model is the two-type Spence game of
`Information/Signaling`.

With two types the intuitive criterion takes a simple form. Fix a PBE with equilibrium payoffs
`u*_L`, `u*_H`. An education level `e` off the equilibrium path is **equilibrium-dominated** for
type `θ` if even the most favorable wage `θH` leaves `θ` below `u*_θ`. The equilibrium **fails
the intuitive criterion** (`FailsIntuitive`) if some off-path `e` is equilibrium-dominated for
the low type but gives the high type strictly more than `u*_H` when paid `θH` (the wage
firms must pay once they put probability `0` on the low type). The symmetric case (the high type
equilibrium-dominated, the low type gaining at wage `θL`) is omitted: it never applies when the
low type can get `θL − c 0 θL` in equilibrium, as with costs nondecreasing in `e`.

The theorems use subsets of the following assumptions (each states exactly what it uses):
education costs strictly increasing in `e`, and strict single crossing
(`c e θH − c e' θH < c e θL − c e' θL` for `e' < e`).

* `intuitive_separating`: a separating PBE that passes the criterion is the **Riley outcome**:
  `eL = 0` and `eH = eR`, where `eR` makes the low type indifferent to mimicking,
  `c eR θL − c 0 θL = θH − θL`.
* `intuitive_pooling`: with continuous costs (and `pH < 1`, and the low type's extra cost
  eventually at least `θH − θL`, a convenient sufficient condition),
  every pooling PBE fails the criterion.
* `riley_passes`: the Riley separating PBE supported by threshold beliefs passes it.
* Witness: `c e θ = e/θ`, `θL = 1`, `θH = 2`: the Riley outcome `eR = 1` passes, and pooling
  at `0` fails.

Not formalized: the general definition for more than two types and mixed strategies, and the
stronger refinements (D1, divinity, stability).
-/
module

public import EconLean.Information.Signaling
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

namespace Econ

open Set

variable {θL θH pH : ℝ} {c : ℝ → ℝ → ℝ} {eL eH : ℝ} {μ : ℝ → ℝ}

/-- The PBE `(eL, eH, μ)` **fails the intuitive criterion**: some off-path education level is
equilibrium-dominated for the low type and strictly profitable for the high type at the wage
`θH`. -/
def FailsIntuitive (θL θH : ℝ) (c : ℝ → ℝ → ℝ) (eL eH : ℝ) (μ : ℝ → ℝ) : Prop :=
  ∃ e, 0 ≤ e ∧ e ≠ eL ∧ e ≠ eH ∧
    θH - c e θL < spenceWage θL θH μ eL - c eL θL ∧
    spenceWage θL θH μ eH - c eH θH < θH - c e θH

/-- **Intuitive criterion, separating equilibria** (Cho–Kreps 1987; MWG §13.C): a separating
PBE that passes the intuitive criterion has `eL = 0` and `eH = eR`, where `eR` (given as a
hypothesis) makes the low type indifferent to mimicking, i.e. is the least education that
deters it. -/
theorem intuitive_separating (h : IsSpencePBE θL θH pH c eL eH μ) (hsep : eL ≠ eH)
    (hlt : θL < θH) (hcL : StrictMonoOn (fun e => c e θL) (Ici 0))
    (hcH : StrictMonoOn (fun e => c e θH) (Ici 0)) {eR : ℝ} (heR : 0 < eR)
    (hR : c eR θL - c 0 θL = θH - θL) (hpass : ¬ FailsIntuitive θL θH c eL eH μ) :
    eL = 0 ∧ eH = eR := by
  have heL : eL = 0 := h.separating_eL hsep hlt fun e he =>
    hcL (mem_Ici.2 le_rfl) (mem_Ici.2 he.le) he
  subst heL
  refine ⟨rfl, ?_⟩
  have heH0 : 0 ≤ eH := h.2.1
  obtain ⟨hb1, -⟩ := h.separating_bounds hsep
  -- `eR ≤ eH`: the low type must not want to mimic
  have hle : eR ≤ eH := by
    by_contra hlt'; push Not at hlt'
    have := hcL (mem_Ici.2 heH0) (mem_Ici.2 heR.le) hlt'
    simp only at this
    linarith
  -- `eH ≤ eR`: otherwise an education level between them breaks the equilibrium
  by_contra hne
  have hlt' : eR < eH := lt_of_le_of_ne hle (Ne.symm hne)
  apply hpass
  obtain ⟨-, -, hμ, hbayes, -, -, -⟩ := h
  obtain ⟨h0, h1⟩ := hbayes hsep
  refine ⟨(eR + eH) / 2, by linarith, by linarith, by linarith, ?_, ?_⟩
  · have := hcL (mem_Ici.2 heR.le) (mem_Ici.2 (by linarith : (0 : ℝ) ≤ (eR + eH) / 2))
      (by linarith : eR < (eR + eH) / 2)
    simp only at this
    simp only [spenceWage, h0, zero_mul, add_zero]
    linarith
  · have := hcH (mem_Ici.2 (by linarith : (0 : ℝ) ≤ (eR + eH) / 2)) (mem_Ici.2 heH0)
      (by linarith : (eR + eH) / 2 < eH)
    simp only at this
    simp only [spenceWage, h1, one_mul]
    linarith

/-- **Intuitive criterion, pooling equilibria** (Cho–Kreps 1987; MWG §13.C): with continuous
costs, the low type's strictly increasing, and strict single crossing, no pooling PBE passes the intuitive
criterion (provided `pH < 1` and the low type's cost eventually exceeds `θH − θL`). -/
theorem intuitive_pooling {e : ℝ} (h : IsSpencePBE θL θH pH c e e μ) (hlt : θL < θH)
    (hpH : pH < 1) (hcL : StrictMonoOn (fun e => c e θL) (Ici 0))
    (hcontL : ContinuousOn (fun e => c e θL) (Ici 0))
    (hcontH : ContinuousOn (fun e => c e θH) (Ici 0))
    (hsc : ∀ e' e, 0 ≤ e' → e' < e → c e θH - c e' θH < c e θL - c e' θL)
    (hbig : ∃ e₁, e ≤ e₁ ∧ θH - θL ≤ c e₁ θL - c e θL) :
    FailsIntuitive θL θH c e e μ := by
  obtain ⟨he0, -, hμ, -, hpool, -, -⟩ := h
  have hμe := hpool rfl
  have hpH0 : 0 ≤ pH := hμe ▸ (hμ e).1
  obtain ⟨e₁, he₁, hbig⟩ := hbig
  set D := (1 - pH) * (θH - θL) with hD
  have hDpos : 0 < D := mul_pos (by linarith) (by linarith)
  have hDle : D ≤ θH - θL := by nlinarith
  -- the low type's extra cost reaches `D` at some `e₀ > e`
  have hcont : ContinuousOn (fun x => c x θL - c e θL) (Icc e e₁) :=
    (hcontL.mono fun x (hx : x ∈ Icc e e₁) => mem_Ici.2 (he0.trans hx.1)).sub continuousOn_const
  obtain ⟨e₀, he₀, hge₀⟩ := intermediate_value_Icc he₁ hcont
    (show D ∈ Icc ((fun x => c x θL - c e θL) e) ((fun x => c x θL - c e θL) e₁) by
      simp only [sub_self]; exact ⟨hDpos.le, hDle.trans hbig⟩)
  simp only at hge₀
  have hee₀ : e < e₀ := by
    rcases eq_or_lt_of_le he₀.1 with heq | hlt₀
    · rw [← heq, sub_self] at hge₀; linarith
    · exact hlt₀
  have he₀0 : 0 ≤ e₀ := he0.trans hee₀.le
  -- the high type's extra cost at `e₀` is below `D`; by continuity also slightly above `e₀`
  have hH₀ : c e₀ θH - c e θH < D := by have := hsc e e₀ he0 hee₀; linarith
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1
    (hcontH.continuousWithinAt (mem_Ici.2 he₀0)) (D - (c e₀ θH - c e θH)) (by linarith)
  obtain ⟨e', he'def⟩ : ∃ e' : ℝ, e' = e₀ + δ / 2 := ⟨_, rfl⟩
  have he'0 : 0 ≤ e' := by rw [he'def]; positivity
  have hH' : c e' θH - c e θH < D := by
    have := hδc (mem_Ici.2 he'0) (by
      rw [Real.dist_eq, show e' - e₀ = δ / 2 by rw [he'def]; ring, abs_of_pos (by positivity)]
      linarith)
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  have hL' : D < c e' θL - c e θL := by
    have := hcL (mem_Ici.2 he₀0) (mem_Ici.2 he'0) (by linarith : e₀ < e')
    simp only at this
    linarith
  refine ⟨e', he'0, by linarith, by linarith, ?_, ?_⟩
  · simp only [spenceWage, hμe]; nlinarith
  · simp only [spenceWage, hμe]; nlinarith

/-- **The Riley outcome passes** the intuitive criterion: the separating PBE with `eL = 0`,
`eH = eR` and threshold beliefs exists and is not eliminated. -/
theorem riley_passes (pH : ℝ) (hcL : StrictMonoOn (fun e => c e θL) (Ici 0))
    (hcH : StrictMonoOn (fun e => c e θH) (Ici 0))
    (hsc : ∀ e' e, 0 ≤ e' → e' < e → c e θH - c e' θH < c e θL - c e' θL)
    {eR : ℝ} (heR : 0 < eR) (hR : c eR θL - c 0 θL = θH - θL) :
    IsSpencePBE θL θH pH c 0 eR (fun e => if eR ≤ e then 1 else 0) ∧
      ¬ FailsIntuitive θL θH c 0 eR (fun e => if eR ≤ e then 1 else 0) := by
  refine ⟨isSpencePBE_separating pH hcL.monotoneOn hcH.monotoneOn heR hR.ge
    (by have := hsc 0 eR le_rfl heR; linarith), ?_⟩
  rintro ⟨e, he0, he0', heR', hL, hH⟩
  simp only [spenceWage, not_le.2 heR, ite_false, zero_mul, add_zero, le_refl, ite_true,
    one_mul] at hL hH
  rcases lt_or_gt_of_ne heR' with hlt | hgt
  · have := hcL (mem_Ici.2 he0) (mem_Ici.2 heR.le) hlt
    simp only at this
    linarith
  · have := hcH (mem_Ici.2 heR.le) (mem_Ici.2 he0) hgt
    simp only at this
    linarith

/-! ### Witness: `c e θ = e / θ`, `θL = 1`, `θH = 2` -/

lemma witness_strictMono (θ : ℝ) (hθ : 0 < θ) :
    StrictMonoOn (fun e : ℝ => e / θ) (Ici 0) :=
  fun _ _ _ _ h => div_lt_div_of_pos_right h hθ

example : ¬ FailsIntuitive 1 2 (fun e θ => e / θ) 0 1 (fun e => if 1 ≤ e then 1 else 0) :=
  (riley_passes (1 / 2) (witness_strictMono 1 one_pos) (witness_strictMono 2 two_pos)
    (fun e' e _ h => by linarith) one_pos (by norm_num)).2

example : FailsIntuitive 1 2 (fun e θ => e / θ) 0 0 (fun x => if x = 0 then 1 / 2 else 0) := by
  refine intuitive_pooling (pH := 1 / 2) ?_ (by norm_num) (by norm_num)
    (witness_strictMono 1 one_pos) (by fun_prop) (by fun_prop)
    (fun e' e _ h => by linarith) ⟨1, by norm_num, by norm_num⟩
  exact isSpencePBE_pooling (by norm_num) (by norm_num)
    (witness_strictMono 1 one_pos).monotoneOn (witness_strictMono 2 two_pos).monotoneOn le_rfl
    (by norm_num) (by norm_num)

end Econ
