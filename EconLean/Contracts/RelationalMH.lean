/-
# Relational contracts with hidden effort: stationary contracts and one-step bonuses (Levin 2003)

Levin (2003), "Relational incentive contracts", AER 93(3), the moral-hazard case. Effort `e` is
private; it generates a publicly observed output `y ∈ Y` (finitely many) with probabilities
`f e y` (nonnegativity of `f` is never used; only `Σ_y f e y = 1`), whose value to the principal is `v y`; the agent bears cost `c e`. Both parties are
risk neutral, outside options are `0`, and the discount factor is `δ ∈ (0,1)`.

A **stationary relational contract** pays a court-enforced wage `w` and, after output `y`, a
discretionary bonus `b y` (of either sign), and asks for the same effort every period. Because
effort is hidden, a deviation in effort is not detected, so the agent's incentive constraint is
static; a refusal to pay the bonus is observed and ends the relationship.
(`IsStatContract`: incentive compatibility, participation, and the two payment constraints
with continuation values `u/(1 − δ)`, `π/(1 − δ)`.)

* `statContract_iff_range` (stationary-contract version of Levin's dynamic-enforcement
  constraint): effort `e` is
  sustained by a stationary contract iff some incentive-compatible bonus schedule has range
  at most `δ/(1 − δ)` times the per-period surplus `s e = E_e[v] − c e`.
* `one_step_bound`: against a single alternative distribution, a bonus with range at most `D`
  raises the agent's expected pay difference by at most `D · Σ_y (f_H y − f_L y)⁺`, and the
  **one-step bonus** paying `D` exactly when `f_H y > f_L y` attains it.
* `two_effort_iff` (the two-effort specialization; Levin's own
  one-step result is for a continuum of efforts under MLRP and CDFC): with two efforts, the high
  effort is sustainable iff `s_H ≥ 0` and `c_H − c_L ≤ δ/(1 − δ) · s_H · Σ_y (f_H y − f_L y)⁺`;
  the proof builds the contract from a one-step bonus.
* Witness: success/failure output; high effort is sustainable at `δ = 2/3` (with slack) but
  not at `δ = 1/3`.

Not formalized: Levin's theorem that stationary contracts are optimal among all
(non-stationary, history-dependent) relational contracts under imperfect public monitoring;
the observable-effort version of that theorem is in `Contracts/Relational`. Also not
formalized: more than two efforts (one-step optimality there needs MLRP and the first-order
approach), limited liability, subjective performance evaluation and adverse selection.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

open Finset

variable {E Y : Type*} [Fintype Y]

/-- Expectation of `g` under the output distribution of effort `e`. -/
def expAt (f : E → Y → ℝ) (e : E) (g : Y → ℝ) : ℝ := ∑ y, f e y * g y

/-- **Stationary relational contract** with hidden effort `e`, wage `w` and bonus schedule
`b`: incentive compatibility against every effort, participation, and the two bonus-payment
constraints (the payer prefers paying to losing the relationship). -/
structure IsStatContract (f : E → Y → ℝ) (v : Y → ℝ) (c : E → ℝ) (δ : ℝ) (e : E) (w : ℝ)
    (b : Y → ℝ) : Prop where
  ic : ∀ e', expAt f e' b - c e' ≤ expAt f e b - c e
  irU : 0 ≤ w + expAt f e b - c e
  irP : 0 ≤ expAt f e v - w - expAt f e b
  payP : ∀ y, b y ≤ δ / (1 - δ) * (expAt f e v - w - expAt f e b)
  payU : ∀ y, -b y ≤ δ / (1 - δ) * (w + expAt f e b - c e)

omit [Fintype Y] in
lemma expAt_add_const [Fintype Y] {f : E → Y → ℝ} {e : E} (hf : ∑ y, f e y = 1) (g : Y → ℝ)
    (k : ℝ) : expAt f e (fun y => g y + k) = expAt f e g + k := by
  unfold expAt
  simp only [mul_add, sum_add_distrib, ← sum_mul, hf, one_mul]

/-- **Dynamic enforcement** (stationary-contract version of Levin 2003): effort `e` is sustained by a stationary relational
contract iff some incentive-compatible bonus schedule has range at most `δ/(1 − δ)` times the
per-period surplus. -/
theorem statContract_iff_range [Nonempty Y] {f : E → Y → ℝ} {v : Y → ℝ} {c : E → ℝ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hf : ∀ e, ∑ y, f e y = 1) (e : E) :
    (∃ w b, IsStatContract f v c δ e w b) ↔
      ∃ b : Y → ℝ, (∀ e', expAt f e' b - c e' ≤ expAt f e b - c e) ∧
        ∀ y y', b y - b y' ≤ δ / (1 - δ) * (expAt f e v - c e) := by
  constructor
  · rintro ⟨w, b, h⟩
    refine ⟨b, h.ic, fun y y' => ?_⟩
    have h1 := h.payP y
    have h2 := h.payU y'
    have : δ / (1 - δ) * (expAt f e v - w - expAt f e b) +
        δ / (1 - δ) * (w + expAt f e b - c e) = δ / (1 - δ) * (expAt f e v - c e) := by ring
    linarith
  · rintro ⟨b, hic, hrange⟩
    -- shift the bonus so that its minimum is `0`, and give the agent zero rent
    obtain ⟨y₀, -, hy₀⟩ := (univ : Finset Y).exists_min_image b univ_nonempty
    set m := b y₀
    set b' : Y → ℝ := fun y => b y + -m
    have hE : ∀ e', expAt f e' b' = expAt f e' b + -m := fun e' => expAt_add_const (hf e') b _
    have hk : 0 ≤ δ / (1 - δ) := div_nonneg hδ0.le (by linarith)
    refine ⟨c e - expAt f e b', b', ⟨fun e' => ?_, ?_, ?_, fun y => ?_, fun y => ?_⟩⟩
    · rw [hE, hE]; linarith [hic e']
    · linarith
    · have := hrange y₀ y₀
      have hs : 0 ≤ expAt f e v - c e := by
        by_contra hneg; push Not at hneg
        have : δ / (1 - δ) * (expAt f e v - c e) < 0 :=
          mul_neg_of_pos_of_neg (div_pos hδ0 (by linarith)) hneg
        linarith
      linarith
    · have := hrange y y₀
      have e1 : expAt f e v - (c e - expAt f e b') - expAt f e b' = expAt f e v - c e := by ring
      rw [e1]; simp only [b']; linarith
    · have : 0 ≤ b' y := by simp only [b', m]; linarith [hy₀ y (mem_univ y)]
      have e2 : c e - expAt f e b' + expAt f e b' - c e = 0 := by ring
      rw [e2, mul_zero]; linarith

omit [Fintype Y] in
/-- **One-step bonuses are optimal against a single deviation**: if `f_H` and `f_L` have the
same total mass, a bonus with range at most `D` yields an expected-pay difference at most
`D · Σ (f_H − f_L)⁺`; the one-step bonus `D · 1[f_H > f_L]` attains it. -/
theorem one_step_bound [Fintype Y] [Nonempty Y] {fH fL : Y → ℝ} (hsum : ∑ y, fH y = ∑ y, fL y)
    (D : ℝ) :
    (∀ b : Y → ℝ, (∀ y y', b y - b y' ≤ D) →
      ∑ y, (fH y - fL y) * b y ≤ D * ∑ y, max (fH y - fL y) 0) ∧
    ∑ y, (fH y - fL y) * (if fL y < fH y then D else 0) = D * ∑ y, max (fH y - fL y) 0 := by
  have hz : ∑ y, (fH y - fL y) = 0 := by rw [sum_sub_distrib, hsum, sub_self]
  constructor
  · intro b hb
    obtain ⟨y₀, -, hy₀⟩ := (univ : Finset Y).exists_min_image b univ_nonempty
    have hshift : ∑ y, (fH y - fL y) * b y = ∑ y, (fH y - fL y) * (b y - b y₀) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hz, zero_mul, sub_zero]
    rw [hshift, mul_sum]
    refine sum_le_sum fun y _ => ?_
    have h0 : 0 ≤ b y - b y₀ := by linarith [hy₀ y (mem_univ y)]
    have h1 : b y - b y₀ ≤ D := hb y y₀
    rcases le_or_gt (fH y - fL y) 0 with hneg | hpos
    · rw [max_eq_right hneg]; nlinarith
    · rw [max_eq_left hpos.le]; nlinarith
  · rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    by_cases h : fL y < fH y
    · simp only [h, ↓reduceIte]; rw [max_eq_left (by linarith)]; ring
    · simp only [h, ↓reduceIte]; rw [max_eq_right (by linarith)]; ring

/-- **Two efforts** (two-effort specialization of Levin's one-step bonuses): if the only
efforts are `eH` and `eL`, then `eH` is sustained by a stationary relational contract iff its
surplus `s(eH) = E_{eH}[v] − c eH` is nonnegative and
`c eH − c eL ≤ δ/(1 − δ) · s(eH) · Σ_y (f eH y − f eL y)⁺`. -/
theorem two_effort_iff [Nonempty Y] {f : E → Y → ℝ} {v : Y → ℝ} {c : E → ℝ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hf : ∀ e, ∑ y, f e y = 1) {eH eL : E}
    (hE : ∀ e, e = eH ∨ e = eL) :
    (∃ w b, IsStatContract f v c δ eH w b) ↔ 0 ≤ expAt f eH v - c eH ∧
      c eH - c eL ≤ δ / (1 - δ) * (expAt f eH v - c eH) * ∑ y, max (f eH y - f eL y) 0 := by
  rw [statContract_iff_range hδ0 hδ1 hf]
  have hsum : ∑ y, f eH y = ∑ y, f eL y := by rw [hf, hf]
  have hdiff : ∀ b : Y → ℝ, expAt f eH b - expAt f eL b = ∑ y, (f eH y - f eL y) * b y := by
    intro b; unfold expAt; rw [← sum_sub_distrib]; exact sum_congr rfl fun y _ => by ring
  constructor
  · rintro ⟨b, hic, hr⟩
    set D := δ / (1 - δ) * (expAt f eH v - c eH)
    have h1 := (one_step_bound hsum D).1 b hr
    have h2 := hic eL
    have := hdiff b
    refine ⟨?_, by linarith⟩
    have h0 := hr (Classical.arbitrary Y) (Classical.arbitrary Y)
    have hk : 0 < δ / (1 - δ) := div_pos hδ0 (by linarith)
    by_contra hneg; push Not at hneg
    have : D < 0 := mul_neg_of_pos_of_neg hk hneg
    linarith
  · rintro ⟨hs, h⟩
    set D := δ / (1 - δ) * (expAt f eH v - c eH)
    have hD : 0 ≤ D := mul_nonneg (div_nonneg hδ0.le (by linarith)) hs
    refine ⟨fun y => if f eL y < f eH y then D else 0, fun e' => ?_, fun y y' => ?_⟩
    · rcases hE e' with he | he <;> rw [he]
      · have := hdiff (fun y => if f eL y < f eH y then D else 0)
        have h2 := (one_step_bound hsum D).2
        linarith
    · dsimp only; split_ifs <;> linarith

/-! ### Witness: success/failure output -/

/-- High effort (`true`) succeeds with probability `3/4`, low effort with `1/4`. -/
noncomputable def mhF : Bool → Bool → ℝ := fun e y =>
  if e then (if y then 3 / 4 else 1 / 4) else (if y then 1 / 4 else 3 / 4)
/-- Success is worth `4`. -/
noncomputable def mhV : Bool → ℝ := fun y => if y then 4 else 0
/-- High effort costs `1`. -/
noncomputable def mhC : Bool → ℝ := fun e => if e then 1 else 0

example : ∃ w b, IsStatContract mhF mhV mhC (2 / 3) true w b := by
  rw [two_effort_iff (E := Bool) (eH := true) (eL := false) (by norm_num) (by norm_num)
    (fun e => by cases e <;> simp [mhF] <;> norm_num)
    (fun e => by cases e <;> simp)]
  simp [expAt, mhF, mhV, mhC]
  norm_num

example : ¬ ∃ w b, IsStatContract mhF mhV mhC (1 / 3) true w b := by
  rw [two_effort_iff (E := Bool) (eH := true) (eL := false) (by norm_num) (by norm_num)
    (fun e => by cases e <;> simp [mhF] <;> norm_num)
    (fun e => by cases e <;> simp)]
  simp [expAt, mhF, mhV, mhC]
  norm_num

end Econ
