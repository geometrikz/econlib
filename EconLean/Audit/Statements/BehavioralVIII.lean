/-
# Frozen statements: behavioral round 8

Headline statements of `BoundedRationality/RegretMatching.lean`,
`BoundedRationality/SelfConfirming.lean` and `BoundedRationality/Replicator.lean`,
copied verbatim after the adversarial review (2026-11-23, record in
`Audit/REVIEW-behavioral-8.md`). Each is closed by the library theorem, so if a
library statement is ever weakened this file stops compiling (a stand-in for
`leanprover/comparator`). Do not edit a statement here without a new review.
-/
module

public import EconLean.BoundedRationality.RegretMatching
public import EconLean.BoundedRationality.RegretMatching
public import EconLean.BoundedRationality.SelfConfirming
public import EconLean.BoundedRationality.Replicator

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Econ.Audit.BehavioralVIII

section RegretMatching
open Econ.RegretMatching Econ.NoRegret Function Finset Filter Topology
variable {A : Type*} [Fintype A] [Nonempty A] {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

theorem frozen_rm_mem (x : A → ℝ) : rm x ∈ lotteries A := by
  first
  | exact @Econ.RegretMatching.rm_mem ..
  | (apply @Econ.RegretMatching.rm_mem <;> assumption)

theorem frozen_rm_orth (x g : A → ℝ) :
    ∑ a, max (x a) 0 * (g a - ∑ b, rm x b * g b) = 0 := by
  first
  | exact @Econ.RegretMatching.rm_orth ..
  | (apply @Econ.RegretMatching.rm_orth <;> assumption)

theorem frozen_avgDist_mem (u : I → (∀ j, S j) → ℝ) {T : ℕ} (hT : 0 < T) :
    avgDist u T ∈ lotteries (∀ j, S j) := by
  first
  | exact @Econ.RegretMatching.avgDist_mem ..
  | (apply @Econ.RegretMatching.avgDist_mem <;> assumption)

theorem frozen_regrets_eq (u : I → (∀ j, S j) → ℝ) (T : ℕ) (i : I) (a : S i) :
    regrets u T i a = T * cceGain u (avgDist u T) i a := by
  first
  | exact @Econ.RegretMatching.regrets_eq ..
  | (apply @Econ.RegretMatching.regrets_eq <;> assumption)

theorem frozen_cceGain_avgDist_le (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {T : ℕ} (hT : 0 < T) (i : I) (a : S i) :
    cceGain u (avgDist u T) i a ≤
      2 * B * Real.sqrt (Fintype.card (S i)) / Real.sqrt T := by
  first
  | exact @Econ.RegretMatching.cceGain_avgDist_le ..
  | (apply @Econ.RegretMatching.cceGain_avgDist_le <;> assumption)

theorem frozen_eventually_isCCE (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ T in atTop, IsCCE u ε (avgDist u T) := by
  first
  | exact @Econ.RegretMatching.eventually_isCCE ..
  | (apply @Econ.RegretMatching.eventually_isCCE <;> assumption)

theorem frozen_isCCE_of_tendsto (u : I → (∀ j, S j) → ℝ) {B : ℝ} (hB : ∀ i s, |u i s| ≤ B)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {μ : (∀ j, S j) → ℝ}
    (hμ : Tendsto (fun n => avgDist u (φ n)) atTop (𝓝 μ)) : IsCCE u 0 μ := by
  first
  | exact @Econ.RegretMatching.isCCE_of_tendsto ..
  | (apply @Econ.RegretMatching.isCCE_of_tendsto <;> assumption)

end RegretMatching

section RegretMatching
open Econ.RegretMatching Function Finset
variable {A : Type*} [Fintype A]

theorem frozen_potential_le {R r : ℕ → A → ℝ} {M : ℝ} (h0 : R 0 = 0)
    (hR : ∀ t, R (t + 1) = R t + r t) (horth : ∀ t, ∑ a, max (R t a) 0 * r t a ≤ 0)
    (hb : ∀ t a, |r t a| ≤ M) (T : ℕ) :
    potential (R T) ≤ T * Fintype.card A * M ^ 2 := by
  first
  | exact @Econ.RegretMatching.potential_le ..
  | (apply @Econ.RegretMatching.potential_le <;> assumption)

theorem frozen_regret_le {R r : ℕ → A → ℝ} {M : ℝ} (hM : 0 ≤ M) (h0 : R 0 = 0)
    (hR : ∀ t, R (t + 1) = R t + r t) (horth : ∀ t, ∑ a, max (R t a) 0 * r t a ≤ 0)
    (hb : ∀ t a, |r t a| ≤ M) (T : ℕ) (a : A) :
    R T a ≤ M * Real.sqrt (Fintype.card A * T) := by
  first
  | exact @Econ.RegretMatching.regret_le ..
  | (apply @Econ.RegretMatching.regret_le <;> assumption)

end RegretMatching

section SelfConfirming
open Econ.SelfConfirming Function Finset
variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {O : I → Type*}

theorem frozen_isSCE_of_isNash {u : I → (∀ j, S j) → ℝ} (y : ∀ i, (∀ j, S j) → O i)
    {s : ∀ j, S j} (h : Econ.SelfConfirming.IsNash u s) : IsSCE u y s := by
  first
  | exact @Econ.SelfConfirming.isSCE_of_isNash ..
  | (apply @Econ.SelfConfirming.isSCE_of_isNash <;> assumption)

theorem frozen_isNash_of_isSCE {u : I → (∀ j, S j) → ℝ} {y : ∀ i, (∀ j, S j) → O i}
    (hy : ∀ i (s s' : ∀ j, S j), s i = s' i → y i s = y i s' → s = s')
    {s : ∀ j, S j} (h : IsSCE u y s) : Econ.SelfConfirming.IsNash u s := by
  first
  | exact @Econ.SelfConfirming.isNash_of_isSCE ..
  | (apply @Econ.SelfConfirming.isNash_of_isSCE <;> assumption)

theorem frozen_sce_not_nash : IsSCE matchPayoff blindFeedback miss ∧ ¬ Econ.SelfConfirming.IsNash matchPayoff miss := by
  first
  | exact @Econ.SelfConfirming.sce_not_nash ..
  | (apply @Econ.SelfConfirming.sce_not_nash <;> assumption)

theorem frozen_ownPayoff_observed (i : Fin 2) (s s' : Fin 2 → Bool) (h0 : s i = s' i)
    (hy : riskyFeedback i s = riskyFeedback i s') : riskyPayoff i s = riskyPayoff i s' := by
  first
  | exact @Econ.SelfConfirming.ownPayoff_observed ..
  | (apply @Econ.SelfConfirming.ownPayoff_observed <;> assumption)

theorem frozen_sce_not_nash_ownPayoff :
    IsSCE riskyPayoff riskyFeedback safeL ∧ ¬ Econ.SelfConfirming.IsNash riskyPayoff safeL := by
  first
  | exact @Econ.SelfConfirming.sce_not_nash_ownPayoff ..
  | (apply @Econ.SelfConfirming.sce_not_nash_ownPayoff <;> assumption)

end SelfConfirming

section Replicator
open Econ.ESS Finset Real Econ.Logit Econ.RationalInattention
variable {n : ℕ}

theorem frozen_fit_eq_of_interior_nash {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (h : Econ.ESS.IsNash A x)
    (hpos : ∀ i, 0 < x i) (i : Fin n) : fit A x i = E A x x := by
  first
  | exact @Econ.ESS.fit_eq_of_interior_nash ..
  | (apply @Econ.ESS.fit_eq_of_interior_nash <;> assumption)

theorem frozen_interior_ess_superior {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (h : IsESS A x)
    (hpos : ∀ i, 0 < x i) {y : Fin n → ℝ} (hy : y ∈ lotteries (Fin n)) (hyx : y ≠ x) :
    E A y y < E A x y := by
  first
  | exact @Econ.ESS.interior_ess_superior ..
  | (apply @Econ.ESS.interior_ess_superior <;> assumption)

theorem frozen_isReplicatorPath_const {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : Econ.ESS.IsNash A xs)
    (hpos : ∀ i, 0 < xs i) : IsReplicatorPath A fun _ => xs := by
  first
  | exact @Econ.ESS.isReplicatorPath_const ..
  | (apply @Econ.ESS.isReplicatorPath_const <;> assumption)

theorem frozen_hasDerivAt_lyapunov {A : Fin n → Fin n → ℝ} {x : ℝ → Fin n → ℝ}
    (hx : IsReplicatorPath A x) {xs : Fin n → ℝ} (hxs : ∑ i, xs i = 1) (t : ℝ) :
    HasDerivAt (fun t => kl xs (x t)) (-(E A xs (x t) - E A (x t) (x t))) t := by
  first
  | exact @Econ.ESS.hasDerivAt_lyapunov ..
  | (apply @Econ.ESS.hasDerivAt_lyapunov <;> assumption)

theorem frozen_lyapunov_nonneg {xs y : Fin n → ℝ} [NeZero n] (hxs : xs ∈ lotteries (Fin n))
    (hy : y ∈ lotteries (Fin n)) (hpos : ∀ i, 0 < y i) : 0 ≤ kl xs y := by
  first
  | exact @Econ.ESS.lyapunov_nonneg ..
  | (apply @Econ.ESS.lyapunov_nonneg <;> assumption)

theorem frozen_lyapunov_eq_zero_iff {xs y : Fin n → ℝ} [NeZero n] (hxs : xs ∈ lotteries (Fin n))
    (hy : y ∈ lotteries (Fin n)) (hpos : ∀ i, 0 < y i) : kl xs y = 0 ↔ xs = y := by
  first
  | exact @Econ.ESS.lyapunov_eq_zero_iff ..
  | (apply @Econ.ESS.lyapunov_eq_zero_iff <;> assumption)

theorem frozen_lyapunov_antitone {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsESS A xs)
    (hpos : ∀ i, 0 < xs i) {x : ℝ → Fin n → ℝ} (hx : IsReplicatorPath A x) :
    Antitone fun t => kl xs (x t) := by
  first
  | exact @Econ.ESS.lyapunov_antitone ..
  | (apply @Econ.ESS.lyapunov_antitone <;> assumption)

theorem frozen_lyapunov_strictAnti {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsESS A xs)
    (hpos : ∀ i, 0 < xs i) {x : ℝ → Fin n → ℝ} (hx : IsReplicatorPath A x)
    (hne : ∀ t, x t ≠ xs) : StrictAnti fun t => kl xs (x t) := by
  first
  | exact @Econ.ESS.lyapunov_strictAnti ..
  | (apply @Econ.ESS.lyapunov_strictAnti <;> assumption)

end Replicator

end Econ.Audit.BehavioralVIII
