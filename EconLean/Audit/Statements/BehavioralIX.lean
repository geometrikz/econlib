/-
# Frozen statements: behavioral round 9

Headline statements of `BoundedRationality/ConditionalRegret.lean`,
`BoundedRationality/Replicator.lean` (convergence), `BoundedRationality/Cursed.lean`
and `BoundedRationality/Analogy.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-9.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.ConditionalRegret
public import EconLean.BoundedRationality.Replicator
public import EconLean.BoundedRationality.Cursed
public import EconLean.BoundedRationality.Analogy

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralIX

section ConditionalRegret
open Econ.RegretMatching Econ.NoRegret Function Finset Filter Topology Matrix
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

theorem frozen_crm_balance (D : A → A → ℝ) (k : A) :
    ∑ j, crm D j * max (D j k) 0 = crm D k * ∑ l, max (D k l) 0 := by
  first
  | exact @Econ.RegretMatching.crm_balance ..
  | (apply @Econ.RegretMatching.crm_balance <;> assumption)

theorem frozen_crm_orth (D : A → A → ℝ) (g : A → ℝ) :
    ∑ jk : A × A, max (D jk.1 jk.2) 0 * (crm D jk.1 * (g jk.2 - g jk.1)) = 0 := by
  first
  | exact @Econ.RegretMatching.crm_orth ..
  | (apply @Econ.RegretMatching.crm_orth <;> assumption)

theorem frozen_condRegrets_eq (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (j k : S i) :
    condRegrets u T i j k = T * obedienceGain u (condAvg u T) i j k := by
  first
  | exact @Econ.RegretMatching.condRegrets_eq ..
  | (apply @Econ.RegretMatching.condRegrets_eq <;> assumption)

theorem frozen_obedienceGain_condAvg_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {T : ℕ} (hT : 0 < T) (i : I) (j k : S i) :
    obedienceGain u (condAvg u T) i j k ≤ 2 * B * Fintype.card (S i) / Real.sqrt T := by
  first
  | exact @Econ.RegretMatching.obedienceGain_condAvg_le ..
  | (apply @Econ.RegretMatching.obedienceGain_condAvg_le <;> assumption)

theorem frozen_eventually_isCE (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ T in atTop, IsCE u ε (condAvg u T) := by
  first
  | exact @Econ.RegretMatching.eventually_isCE ..
  | (apply @Econ.RegretMatching.eventually_isCE <;> assumption)

theorem frozen_isCorrelatedEq_of_tendsto (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => condAvg u (φ n)) atTop (𝓝 μ)) : IsCorrelatedEq u μ := by
  first
  | exact @Econ.RegretMatching.isCorrelatedEq_of_tendsto ..
  | (apply @Econ.RegretMatching.isCorrelatedEq_of_tendsto <;> assumption)

end ConditionalRegret

section ConditionalRegret
open Econ.RegretMatching Function Finset Matrix
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem frozen_condMatrix_isStochastic (D : A → A → ℝ) : IsStochastic (condMatrix D) := by
  first
  | exact @Econ.RegretMatching.condMatrix_isStochastic ..
  | (apply @Econ.RegretMatching.condMatrix_isStochastic <;> assumption)

end ConditionalRegret

section Replicator
open Econ.ESS Finset Real Econ.Logit Econ.RationalInattention
variable {n : ℕ}

theorem frozen_le_coord {xs y : Fin n → ℝ} (hxs : ∀ i, 0 ≤ xs i) (hy : ∀ i, 0 < y i)
    (hy1 : ∀ i, y i ≤ 1) {k : Fin n} (hk : 0 < xs k) {V0 : ℝ} (hV : kl xs y ≤ V0) :
    exp (-(V0 + ent xs) / xs k) ≤ y k := by
  first
  | exact @Econ.ESS.le_coord ..
  | (apply @Econ.ESS.le_coord <;> assumption)

theorem frozen_tendsto_ess [NeZero n] {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsESS A xs)
    (hpos : ∀ i, 0 < xs i) {x : ℝ → Fin n → ℝ} (hx : IsReplicatorPath A x) :
    Filter.Tendsto x Filter.atTop (nhds xs) := by
  first
  | exact @Econ.ESS.tendsto_ess ..
  | (apply @Econ.ESS.tendsto_ess <;> assumption)

end Replicator

section Cursed
open Econ.Cursed Function Finset
variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : I → Type*}

theorem frozen_cursedInterim_eq (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    (p : (∀ j, Θ j) → ℝ) (s : ∀ i, Θ i → A i) (i : I) (θi : Θ i) (a : A i) :
    cursedInterim χ u p s i θi a = interim (cursedPayoff χ u p) p s i θi a := by
  first
  | exact @Econ.Cursed.cursedInterim_eq ..
  | (apply @Econ.Cursed.cursedInterim_eq <;> assumption)

theorem frozen_isCursedEq_iff_isBNE {χ : ℝ} {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} {s : ∀ i, Θ i → A i} :
    IsCursedEq χ u p s ↔ IsBNE (cursedPayoff χ u p) p s := by
  first
  | exact @Econ.Cursed.isCursedEq_iff_isBNE ..
  | (apply @Econ.Cursed.isCursedEq_iff_isBNE <;> assumption)

theorem frozen_isCursedEq_zero_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    {s : ∀ i, Θ i → A i} : IsCursedEq 0 u p s ↔ IsBNE u p s := by
  first
  | exact @Econ.Cursed.isCursedEq_zero_iff ..
  | (apply @Econ.Cursed.isCursedEq_zero_iff <;> assumption)

theorem frozen_lemons_buyer_offer (χ : ℝ) :
    cursedInterim χ lemonsPayoff lemonsPrior offerPlay false false true =
      (2 * χ - 1) * (3 / 2) := by
  first
  | exact @Econ.Cursed.lemons_buyer_offer ..
  | (apply @Econ.Cursed.lemons_buyer_offer <;> assumption)

theorem frozen_lemons_cursed_iff {χ : ℝ} :
    IsCursedEq χ lemonsPayoff lemonsPrior offerPlay ↔ 1 / 2 ≤ χ := by
  first
  | exact @Econ.Cursed.lemons_cursed_iff ..
  | (apply @Econ.Cursed.lemons_cursed_iff <;> assumption)

theorem frozen_lemons_not_bne : ¬ IsBNE lemonsPayoff lemonsPrior offerPlay := by
  first
  | exact @Econ.Cursed.lemons_not_bne ..
  | (apply @Econ.Cursed.lemons_not_bne <;> assumption)

end Cursed

section Analogy
open Econ.Cursed Function Finset
variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : I → Type*} {C : I → Type*} [∀ i, DecidableEq (C i)]

theorem frozen_analogyInterim_eq {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) (s : ∀ i, Θ i → A i)
    (i : I) (θi : Θ i) (a : A i) :
    analogyInterim u p cls s i θi a = interim (classPayoff u p cls) p s i θi a := by
  first
  | exact @Econ.Cursed.analogyInterim_eq ..
  | (apply @Econ.Cursed.analogyInterim_eq <;> assumption)

theorem frozen_isABEE_iff_isBNE {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ} {s : ∀ i, Θ i → A i} :
    IsABEE u p cls s ↔ IsBNE (classPayoff u p cls) p s := by
  first
  | exact @Econ.Cursed.isABEE_iff_isBNE ..
  | (apply @Econ.Cursed.isABEE_iff_isBNE <;> assumption)

theorem frozen_isABEE_id_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    {s : ∀ i, Θ i → A i} :
    IsABEE u p (fun _ θ => θ) s ↔ IsBNE u p s := by
  first
  | exact @Econ.Cursed.isABEE_id_iff ..
  | (apply @Econ.Cursed.isABEE_id_iff <;> assumption)

theorem frozen_isABEE_own_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    {s : ∀ i, Θ i → A i} :
    IsABEE u p (C := Θ) (fun i θ => θ i) s ↔ IsCursedEq 1 u p s := by
  first
  | exact @Econ.Cursed.isABEE_own_iff ..
  | (apply @Econ.Cursed.isABEE_own_iff <;> assumption)

theorem frozen_lemons_abee : IsABEE lemonsPayoff lemonsPrior (C := fun _ => Bool) (fun i θ => θ i)
    offerPlay ∧ ¬ IsBNE lemonsPayoff lemonsPrior offerPlay := by
  first
  | exact @Econ.Cursed.lemons_abee ..
  | (apply @Econ.Cursed.lemons_abee <;> assumption)

end Analogy

end Econ.Audit.BehavioralIX
