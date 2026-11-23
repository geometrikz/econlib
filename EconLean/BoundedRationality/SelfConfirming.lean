/-
# Self-confirming equilibrium

References. D. Fudenberg and D. K. Levine (1993), "Self-Confirming
Equilibrium", *Econometrica* 61(3); E. Battigalli (1987) ("conjectural
equilibrium"); D. Fudenberg and D. K. Levine (1998), *The Theory of Learning in
Games*, ch. 6.

A finite normal-form game with payoffs `u i : (∀ j, S j) → ℝ` and, for each
player, a **feedback function** `y i : (∀ j, S j) → O i` describing what `i`
observes after play. A pure profile `s*` is a (unitary) **self-confirming
equilibrium** if each player `i` has a belief `ν` (a probability distribution
over profiles) such that
* `s* i` is a best reply to `ν`: it maximizes `Σ_s ν(s) uᵢ(a, s₋ᵢ)`, and
* `ν` is confirmed by what `i` sees: every profile `s` in the support of `ν`
  produces, together with `i`'s own action `s* i`, the same observation as the
  actual play, `yᵢ(s* i, s₋ᵢ) = yᵢ(s*)`.

Beliefs about what is never observed are unrestricted: that is how
self-confirming equilibria can sustain non-Nash outcomes.

**Results.**
* `isSCE_of_isNash`: every pure Nash equilibrium is self-confirming (take the
  correct belief).
* `isNash_of_isSCE`: with **perfect feedback** (for a fixed own action, `y i`
  reveals the whole profile, e.g. `y i s = s₋ᵢ` or `y i = id`) every
  self-confirming equilibrium is a Nash equilibrium.
* `sce_not_nash`: with uninformative feedback the inclusion is strict: in a
  coordination problem where player `0` never observes player `1`'s action,
  miscoordination is self-confirming but not Nash.
* `sce_not_nash_ownPayoff`: the inclusion stays strict when players observe
  their own payoffs (the Fudenberg–Levine assumption, `ownPayoff_observed`):
  a player who never tries the risky action keeps a pessimistic belief about
  what it would face.

Fudenberg–Levine work with extensive forms and terminal-node feedback; the
normal form with feedback functions used here is Battigalli's conjectural
equilibrium (see also Fudenberg–Kamada 2015). Only pure profiles and unitary
beliefs (one belief per player) are treated;
the heterogeneous-belief and mixed versions and the extensive-form setting are
not formalized.
-/
module

public import EconLean.Games.Mixed

@[expose] public section

noncomputable section

namespace Econ

namespace SelfConfirming

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {O : I → Type*}

/-- Expected payoff of `i` from playing `a` when it believes profiles are
distributed according to `ν` (only the others' actions matter). -/
def belPayoff (u : I → (∀ j, S j) → ℝ) (ν : (∀ j, S j) → ℝ) (i : I) (a : S i) : ℝ :=
  ∑ s, ν s * u i (update s i a)

/-- Pure Nash equilibrium. -/
def IsNash (u : I → (∀ j, S j) → ℝ) (s : ∀ j, S j) : Prop :=
  ∀ i (a : S i), u i (update s i a) ≤ u i s

/-- `ν` is confirmed for player `i` at `s*` under feedback `y`. -/
def Confirmed (y : ∀ i, (∀ j, S j) → O i) (s : ∀ j, S j) (i : I) (ν : (∀ j, S j) → ℝ) :
    Prop :=
  ∀ s', ν s' ≠ 0 → y i (update s' i (s i)) = y i s

/-- **Self-confirming equilibrium** (unitary, pure). -/
def IsSCE (u : I → (∀ j, S j) → ℝ) (y : ∀ i, (∀ j, S j) → O i) (s : ∀ j, S j) : Prop :=
  ∀ i, ∃ ν ∈ lotteries (∀ j, S j), Confirmed y s i ν ∧
    ∀ a : S i, belPayoff u ν i a ≤ belPayoff u ν i (s i)

theorem belPayoff_degenerate (u : I → (∀ j, S j) → ℝ) (s : ∀ j, S j) (i : I) (a : S i) :
    belPayoff u (degenerate s) i a = u i (update s i a) := by
  simp [belPayoff, degenerate]

/-- **Nash equilibria are self-confirming.** -/
theorem isSCE_of_isNash {u : I → (∀ j, S j) → ℝ} (y : ∀ i, (∀ j, S j) → O i)
    {s : ∀ j, S j} (h : IsNash u s) : IsSCE u y s := by
  intro i
  refine ⟨degenerate s, degenerate_mem s, fun s' hs' => ?_, fun a => ?_⟩
  · have : s = s' := by
      by_contra hne; exact hs' (by simp [degenerate, hne])
    subst this; rw [update_eq_self]
  · rw [belPayoff_degenerate, belPayoff_degenerate, update_eq_self]
    exact h i a

omit [∀ i, DecidableEq (S i)] in
/-- **With perfect feedback, self-confirming equilibria are Nash.** Perfect
feedback: given its own action, player `i`'s observation identifies the
profile. -/
theorem isNash_of_isSCE {u : I → (∀ j, S j) → ℝ} {y : ∀ i, (∀ j, S j) → O i}
    (hy : ∀ i (s s' : ∀ j, S j), s i = s' i → y i s = y i s' → s = s')
    {s : ∀ j, S j} (h : IsSCE u y s) : IsNash u s := by
  intro i a
  obtain ⟨ν, hν, hconf, hbr⟩ := h i
  -- on the support of `ν`, the others play exactly as in `s`
  have key : ∀ b : S i, belPayoff u ν i b = u i (update s i b) := by
    intro b
    unfold belPayoff
    have : ∀ s', ν s' * u i (update s' i b) = ν s' * u i (update s i b) := by
      intro s'
      by_cases h0 : ν s' = 0
      · simp [h0]
      · have he : update s' i (s i) = s := hy i _ _ (by simp) (hconf s' h0)
        have : update s' i b = update s i b := by
          rw [← he, update_idem]
        rw [this]
    rw [sum_congr rfl fun s' _ => this s', ← sum_mul, hν.2, one_mul]
  have := hbr a
  rw [key, key, update_eq_self] at this
  exact this

/-! ### A self-confirming equilibrium that is not Nash -/

/-- Two players with actions `Bool`; player `0` wants to match player `1`;
player `1` is indifferent. -/
def matchPayoff (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  if i = 0 then (if s 0 = s 1 then 1 else 0) else 0

/-- Player `0` observes nothing; player `1` observes the whole profile. -/
def blindFeedback (i : Fin 2) (s : Fin 2 → Bool) : Fin 2 → Bool :=
  if i = 0 then fun _ => false else s

/-- Miscoordination: `0` plays `true`, `1` plays `false`. -/
def miss : Fin 2 → Bool := ![true, false]

/-- **Self-confirming but not Nash.** -/
theorem sce_not_nash : IsSCE matchPayoff blindFeedback miss ∧ ¬ IsNash matchPayoff miss := by
  classical
  refine ⟨fun i => ?_, fun h => ?_⟩
  · fin_cases i
    · -- player `0` wrongly believes `1` plays `true`; nothing contradicts it
      refine ⟨degenerate ![true, true], degenerate_mem _, fun s' _ => by simp [blindFeedback],
        fun a => ?_⟩
      rw [belPayoff_degenerate, belPayoff_degenerate]
      cases a <;> simp [matchPayoff, miss, update]
    · -- player `1` holds the correct belief
      refine ⟨degenerate miss, degenerate_mem _, fun s' hs' => ?_, fun a => ?_⟩
      · have : miss = s' := by
          by_contra hne; exact hs' (by simp [degenerate, hne])
        subst this; simp
      · rw [belPayoff_degenerate, belPayoff_degenerate]; simp [matchPayoff]
  · have := h 0 false
    simp [matchPayoff, miss, update] at this
    norm_num at this

/-! ### With own payoffs observed -/

/-- Player `0` chooses `false` = Safe (payoff `1`) or `true` = Risky (payoff `2`
if player `1` plays `true` = L, `0` if `false` = R); player `1` is indifferent. -/
def riskyPayoff (i : Fin 2) (s : Fin 2 → Bool) : ℝ :=
  if i = 0 then (if s 0 then (if s 1 then 2 else 0) else 1) else 0

/-- Player `0` sees player `1`'s action only after Risky; player `1` sees
everything. -/
def riskyFeedback (i : Fin 2) (s : Fin 2 → Bool) : Fin 2 → Bool :=
  if i = 0 then (fun _ => s 0 && s 1) else s

/-- Safe, with player `1` playing L. -/
def safeL : Fin 2 → Bool := ![false, true]

/-- In this game each player's own action and observation determine its payoff. -/
theorem ownPayoff_observed (i : Fin 2) (s s' : Fin 2 → Bool) (h0 : s i = s' i)
    (hy : riskyFeedback i s = riskyFeedback i s') : riskyPayoff i s = riskyPayoff i s' := by
  fin_cases i
  · have := congrFun hy 0
    simp only [riskyFeedback, riskyPayoff] at this h0 ⊢
    simp at h0 this ⊢
    cases hs0 : s 0 <;> cases hs1 : s 1 <;> cases hs0' : s' 0 <;> cases hs1' : s' 1 <;>
      simp_all
  · simp [riskyPayoff]

/-- **Self-confirming but not Nash, with own payoffs observed.** -/
theorem sce_not_nash_ownPayoff :
    IsSCE riskyPayoff riskyFeedback safeL ∧ ¬ IsNash riskyPayoff safeL := by
  classical
  refine ⟨fun i => ?_, fun h => ?_⟩
  · fin_cases i
    · -- player `0` believes `1` would play R, which Safe never contradicts
      refine ⟨degenerate ![false, false], degenerate_mem _, fun s' hs' => ?_, fun a => ?_⟩
      · have : ![false, false] = s' := by
          by_contra hne; exact hs' (by simp [degenerate, hne])
        subst this; funext k; simp [riskyFeedback, safeL]
      · rw [belPayoff_degenerate, belPayoff_degenerate]
        cases a <;> simp [riskyPayoff, safeL, update]
    · refine ⟨degenerate safeL, degenerate_mem _, fun s' hs' => ?_, fun a => ?_⟩
      · have : safeL = s' := by
          by_contra hne; exact hs' (by simp [degenerate, hne])
        subst this; simp
      · rw [belPayoff_degenerate, belPayoff_degenerate]; simp [riskyPayoff]
  · have := h 0 true
    simp [riskyPayoff, safeL, update] at this

end SelfConfirming

end Econ
