/-
# Frozen statements: behavioral round 7

Headline statements of `Behavioral/LimitedAttention.lean` (sufficiency),
`Behavioral/MultiplierPreferences.lean`, `BoundedRationality/NoRegret.lean`
and `BoundedRationality/ESS.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-7.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.Behavioral.LimitedAttention
public import EconLean.Behavioral.MultiplierPreferences
public import EconLean.BoundedRationality.NoRegret
public import EconLean.BoundedRationality.ESS

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralVII

section LimitedAttention
open Econ.LimitedAttention
variable {X : Type*} [DecidableEq X] {c : Finset X → X} {u : X → ℕ} {Γ : Finset X → Finset X}

theorem frozen_exists_undominated (h : WARPLA c) {S : Finset X} (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, ¬ RevPref c y x := by
  first
  | exact @Econ.LimitedAttention.exists_undominated ..
  | (apply @Econ.LimitedAttention.exists_undominated <;> assumption)

theorem frozen_exists_rank (h : WARPLA c) (S : Finset X) :
    ∃ u : X → ℕ, Set.InjOn u S ∧ ∀ x ∈ S, ∀ y ∈ S, RevPref c x y → u y < u x := by
  first
  | exact @Econ.LimitedAttention.exists_rank ..
  | (apply @Econ.LimitedAttention.exists_rank <;> assumption)

theorem frozen_cla_of_warpLA [Fintype X] (hc : ∀ S : Finset X, S.Nonempty → c S ∈ S)
    (h : WARPLA c) : ∃ u, IsCLA c u (revealedAttention c) := by
  first
  | exact @Econ.LimitedAttention.cla_of_warpLA ..
  | (apply @Econ.LimitedAttention.cla_of_warpLA <;> assumption)

theorem frozen_cla_iff_warpLA [Fintype X] (hc : ∀ S : Finset X, S.Nonempty → c S ∈ S) :
    (∃ u Γ, IsCLA c u Γ) ↔ WARPLA c := by
  first
  | exact @Econ.LimitedAttention.cla_iff_warpLA ..
  | (apply @Econ.LimitedAttention.cla_iff_warpLA <;> assumption)

theorem frozen_revPref_ranked (h : IsCLA c u Γ) {x y : X} (hP : RevPref c x y) : u y < u x := by
  first
  | exact @Econ.LimitedAttention.revPref_ranked ..
  | (apply @Econ.LimitedAttention.revPref_ranked <;> assumption)

end LimitedAttention

section MultiplierPreferences
open Econ.Multiplier Finset Real Econ.Logit Econ.RationalInattention
variable {S : Type*} [Fintype S] [Nonempty S] {θ : ℝ} {p u : S → ℝ}

theorem frozen_worstCase_isProb (hp : ∀ s, 0 < p s) : IsProb (worstCase θ p u) := by
  first
  | exact @Econ.Multiplier.worstCase_isProb ..
  | (apply @Econ.Multiplier.worstCase_isProb <;> assumption)

theorem frozen_mult_eq_at_worstCase (hθ : 0 < θ) (hp : ∀ s, 0 < p s) :
    penalized θ p u (worstCase θ p u) = mult θ p u := by
  first
  | exact @Econ.Multiplier.mult_eq_at_worstCase ..
  | (apply @Econ.Multiplier.mult_eq_at_worstCase <;> assumption)

theorem frozen_mult_le_penalized (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {q : S → ℝ} (hq : IsProb q) :
    mult θ p u ≤ penalized θ p u q := by
  first
  | exact @Econ.Multiplier.mult_le_penalized ..
  | (apply @Econ.Multiplier.mult_le_penalized <;> assumption)

theorem frozen_isLeast_mult (hθ : 0 < θ) (hp : ∀ s, 0 < p s) :
    IsLeast {x | ∃ q, IsProb q ∧ x = penalized θ p u q} (mult θ p u) := by
  first
  | exact @Econ.Multiplier.isLeast_mult ..
  | (apply @Econ.Multiplier.isLeast_mult <;> assumption)

theorem frozen_eq_worstCase_of_min (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {q : S → ℝ} (hq : IsProb q)
    (hmin : penalized θ p u q ≤ mult θ p u) : q = worstCase θ p u := by
  first
  | exact @Econ.Multiplier.eq_worstCase_of_min ..
  | (apply @Econ.Multiplier.eq_worstCase_of_min <;> assumption)

theorem frozen_worstCase_tilts (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {s s' : S} (h : u s < u s') :
    worstCase θ p u s' / p s' < worstCase θ p u s / p s := by
  first
  | exact @Econ.Multiplier.worstCase_tilts ..
  | (apply @Econ.Multiplier.worstCase_tilts <;> assumption)

theorem frozen_mult_le_eu (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (hp1 : ∑ s, p s = 1) :
    mult θ p u ≤ ∑ s, p s * u s := by
  first
  | exact @Econ.Multiplier.mult_le_eu ..
  | (apply @Econ.Multiplier.mult_le_eu <;> assumption)

theorem frozen_min_le_mult (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (hp1 : ∑ s, p s = 1) {m : ℝ}
    (hm : ∀ s, m ≤ u s) : m ≤ mult θ p u := by
  first
  | exact @Econ.Multiplier.min_le_mult ..
  | (apply @Econ.Multiplier.min_le_mult <;> assumption)

theorem frozen_mult_add_const (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (k : ℝ) :
    mult θ p (fun s => u s + k) = mult θ p u + k := by
  first
  | exact @Econ.Multiplier.mult_add_const ..
  | (apply @Econ.Multiplier.mult_add_const <;> assumption)

theorem frozen_mult_mono (hθ : 0 < θ) (hp : ∀ s, 0 < p s) {u' : S → ℝ} (h : ∀ s, u s ≤ u' s) :
    mult θ p u ≤ mult θ p u' := by
  first
  | exact @Econ.Multiplier.mult_mono ..
  | (apply @Econ.Multiplier.mult_mono <;> assumption)

theorem frozen_mult_concave (hθ : 0 < θ) (hp : ∀ s, 0 < p s) (u' : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    α * mult θ p u + (1 - α) * mult θ p u' ≤ mult θ p (fun s => α * u s + (1 - α) * u' s) := by
  first
  | exact @Econ.Multiplier.mult_concave ..
  | (apply @Econ.Multiplier.mult_concave <;> assumption)

end MultiplierPreferences

section NoRegret
open Econ.NoRegret Function Finset Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {T : ℕ}

theorem frozen_isCE_zero_iff (u : I → (∀ j, S j) → ℝ) (μ : (∀ j, S j) → ℝ) :
    IsCE u 0 μ ↔ IsCorrelatedEq u μ := by
  first
  | exact @Econ.NoRegret.isCE_zero_iff ..
  | (apply @Econ.NoRegret.isCE_zero_iff <;> assumption)

theorem frozen_isCCE_of_isCorrelatedEq {u : I → (∀ j, S j) → ℝ} {μ : (∀ j, S j) → ℝ}
    (h : IsCorrelatedEq u μ) : IsCCE u 0 μ := by
  first
  | exact @Econ.NoRegret.isCCE_of_isCorrelatedEq ..
  | (apply @Econ.NoRegret.isCCE_of_isCorrelatedEq <;> assumption)

theorem frozen_emp_mem (hT : 0 < T) (h : Fin T → ∀ j, S j) : emp h ∈ lotteries (∀ j, S j) := by
  first
  | exact @Econ.NoRegret.emp_mem ..
  | (apply @Econ.NoRegret.emp_mem <;> assumption)

theorem frozen_extRegret_eq (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (i : I) (t' : S i) :
    extRegret u h i t' = cceGain u (emp h) i t' := by
  first
  | exact @Econ.NoRegret.extRegret_eq ..
  | (apply @Econ.NoRegret.extRegret_eq <;> assumption)

theorem frozen_intRegret_eq (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (i : I) (t t' : S i) :
    intRegret u h i t t' = obedienceGain u (emp h) i t t' := by
  first
  | exact @Econ.NoRegret.intRegret_eq ..
  | (apply @Econ.NoRegret.intRegret_eq <;> assumption)

theorem frozen_isCCE_emp_iff (hT : 0 < T) (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j) (ε : ℝ) :
    IsCCE u ε (emp h) ↔ ∀ i (t' : S i), extRegret u h i t' ≤ ε := by
  first
  | exact @Econ.NoRegret.isCCE_emp_iff ..
  | (apply @Econ.NoRegret.isCCE_emp_iff <;> assumption)

theorem frozen_isCorrelatedEq_emp_iff (hT : 0 < T) (u : I → (∀ j, S j) → ℝ) (h : Fin T → ∀ j, S j)
    (ε : ℝ) : IsCE u ε (emp h) ↔ ∀ i (t t' : S i), intRegret u h i t t' ≤ ε := by
  first
  | exact @Econ.NoRegret.isCorrelatedEq_emp_iff ..
  | (apply @Econ.NoRegret.isCorrelatedEq_emp_iff <;> assumption)

theorem frozen_isCorrelatedEq_of_limit (u : I → (∀ j, S j) → ℝ) {Tn : ℕ → ℕ} (hT : ∀ n, 0 < Tn n)
    (h : ∀ n, Fin (Tn n) → ∀ j, S j) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hreg : ∀ n i (t t' : S i), intRegret u (h n) i t t' ≤ ε n) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => emp (h n)) atTop (𝓝 μ)) : IsCorrelatedEq u μ := by
  first
  | exact @Econ.NoRegret.isCorrelatedEq_of_limit ..
  | (apply @Econ.NoRegret.isCorrelatedEq_of_limit <;> assumption)

theorem frozen_isCCE_of_limit (u : I → (∀ j, S j) → ℝ) {Tn : ℕ → ℕ} (hT : ∀ n, 0 < Tn n)
    (h : ∀ n, Fin (Tn n) → ∀ j, S j) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hreg : ∀ n i (t' : S i), extRegret u (h n) i t' ≤ ε n) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => emp (h n)) atTop (𝓝 μ)) : IsCCE u 0 μ := by
  first
  | exact @Econ.NoRegret.isCCE_of_limit ..
  | (apply @Econ.NoRegret.isCCE_of_limit <;> assumption)

end NoRegret

section ESS
open Econ.ESS Finset
variable {n : ℕ}

theorem frozen_isNash_of_isESS {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (h : IsESS A x) :
    Econ.ESS.IsNash A x := by
  first
  | exact @Econ.ESS.isNash_of_isESS ..
  | (apply @Econ.ESS.isNash_of_isESS <;> assumption)

theorem frozen_isESS_of_strict {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (hx : x ∈ lotteries (Fin n))
    (h : ∀ y ∈ lotteries (Fin n), y ≠ x → E A y x < E A x x) : IsESS A x := by
  first
  | exact @Econ.ESS.isESS_of_strict ..
  | (apply @Econ.ESS.isESS_of_strict <;> assumption)

theorem frozen_advantage_eq (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (ε : ℝ) :
    E A x (fun j => (1 - ε) * x j + ε * y j) - E A y (fun j => (1 - ε) * x j + ε * y j) =
      (1 - ε) * (E A x x - E A y x) + ε * (E A x y - E A y y) := by
  first
  | exact @Econ.ESS.advantage_eq ..
  | (apply @Econ.ESS.advantage_eq <;> assumption)

theorem frozen_isESS_iff_invasion (A : Fin n → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : x ∈ lotteries (Fin n)) :
    IsESS A x ↔ ∀ y ∈ lotteries (Fin n), y ≠ x → ∃ εbar > 0, ∀ ε, 0 < ε → ε < εbar →
      E A y (fun j => (1 - ε) * x j + ε * y j) < E A x (fun j => (1 - ε) * x j + ε * y j) := by
  first
  | exact @Econ.ESS.isESS_iff_invasion ..
  | (apply @Econ.ESS.isESS_iff_invasion <;> assumption)

theorem frozen_hawkDove_isESS {V C : ℝ} (hV : 0 < V) (hVC : V < C) :
    IsESS (hawkDove V C) (hdMix (V / C)) := by
  first
  | exact @Econ.ESS.hawkDove_isESS ..
  | (apply @Econ.ESS.hawkDove_isESS <;> assumption)

theorem frozen_hawk_not_nash {V C : ℝ} (hVC : V < C) : ¬ Econ.ESS.IsNash (hawkDove V C) (hdMix 1) := by
  first
  | exact @Econ.ESS.hawk_not_nash ..
  | (apply @Econ.ESS.hawk_not_nash <;> assumption)

end ESS

end Econ.Audit.BehavioralVII
