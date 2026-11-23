/-
# Analogy-based expectation equilibrium

References. P. Jehiel (2005), "Analogy-Based Expectation Equilibrium", *JET*
123; P. Jehiel and F. Koessler (2008), "Revisiting Games of Incomplete
Information with Analogy-Based Expectations", *GEB* 62 (the Bayesian-game
version used here).

In a finite Bayesian game, player `i` groups type profiles into **analogy
classes** `clsᵢ : (∀ j, Θ j) → Cᵢ`, each class fixing `i`'s own type
(`IsAnalogyPartition`). It knows only the *average* behavior of the others in
each class: when the true profile is `θ`, it believes the others' actions are
those of a profile `θ'` drawn from the prior restricted to `θ`'s class. The
(prior-weighted) interim payoff of type `θᵢ` choosing `a` is
(`analogyInterim`)

    Σ_{θ : θᵢ fixed} p(θ) Σ_{θ' ~ θ} p(θ')/p(class θ) · uᵢ(a, s₋ᵢ(θ'₋ᵢ), θ),

and `s` is an **analogy-based expectation equilibrium** (ABEE) if every
type's action maximizes it (`IsABEE`).

**Results.**
* `analogyInterim_eq`, `isABEE_iff_isBNE` (Jehiel–Koessler): an ABEE is a
  Bayesian Nash equilibrium of the game whose payoffs are averaged within
  classes, `E[uᵢ(a, ·) | clsᵢ(θ)]` (`classPayoff`).
* `isABEE_id_iff`: with the finest analogy partition (`clsᵢ = id`), ABEE is
  Bayesian Nash equilibrium.
* `isABEE_own_iff`: with the private-information analogy partition (each
  class is one own type, `clsᵢ θ = θᵢ`, the coarsest partition that fixes the
  own type), ABEE is fully cursed (`χ = 1`) equilibrium.
* `lemons_abee`: in the lemons market of `Cursed.lean`, a buyer who pools the
  seller's types offers in ABEE although offering is not Bayesian Nash.

Jehiel–Koessler allow general partitions; requiring each class to fix the own
type is a modeling restriction here. Only pure type-contingent strategies are
treated (Jehiel–Koessler allow mixed strategies, and a pure ABEE need not
exist).
-/
module

public import EconLean.BoundedRationality.Cursed

@[expose] public section

noncomputable section

namespace Econ

namespace Cursed

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)] {A : I → Type*} {C : I → Type*} [∀ i, DecidableEq (C i)]

/-- Analogy classes of player `i` fix `i`'s own type. -/
def IsAnalogyPartition (cls : ∀ i, (∀ j, Θ j) → C i) : Prop :=
  ∀ i (θ θ' : ∀ j, Θ j), cls i θ = cls i θ' → θ i = θ' i

/-- Prior probability of the class of `θ`. -/
def classProb (p : (∀ j, Θ j) → ℝ) (cls : ∀ i, (∀ j, Θ j) → C i) (i : I)
    (θ : ∀ j, Θ j) : ℝ :=
  ∑ θ', if cls i θ' = cls i θ then p θ' else 0

/-- Payoffs averaged over the analogy class: `E[uᵢ(a, ·) | clsᵢ(θ)]`. -/
def classPayoff (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (cls : ∀ i, (∀ j, Θ j) → C i) : I → (∀ j, A j) → (∀ j, Θ j) → ℝ :=
  fun i a θ => (∑ θ', if cls i θ' = cls i θ then p θ' * u i a θ' else 0) / classProb p cls i θ

/-- The analogy-based interim payoff of type `θᵢ` choosing `a`. -/
def analogyInterim (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (cls : ∀ i, (∀ j, Θ j) → C i) (s : ∀ i, Θ i → A i) (i : I) (θi : Θ i) (a : A i) : ℝ :=
  ∑ θ, if θ i = θi then p θ * ∑ θ', (if cls i θ' = cls i θ then p θ' / classProb p cls i θ
    else 0) * u i (update (play s θ') i a) θ else 0

/-- **Analogy-based expectation equilibrium.** -/
def IsABEE (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (cls : ∀ i, (∀ j, Θ j) → C i) (s : ∀ i, Θ i → A i) : Prop :=
  p ∈ lotteries (∀ j, Θ j) ∧
    ∀ i θi a, analogyInterim u p cls s i θi a ≤ analogyInterim u p cls s i θi (s i θi)

/-- **The analogy-based interim payoff is the interim payoff of the
class-averaged game.** -/
theorem analogyInterim_eq {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) (s : ∀ i, Θ i → A i)
    (i : I) (θi : Θ i) (a : A i) :
    analogyInterim u p cls s i θi a = interim (classPayoff u p cls) p s i θi a := by
  simp only [analogyInterim, interim, classPayoff]
  have lhs : ∀ θ, (if θ i = θi then p θ * ∑ θ', (if cls i θ' = cls i θ then
      p θ' / classProb p cls i θ else 0) * u i (update (play s θ') i a) θ else 0) =
      ∑ θ', (if θ i = θi ∧ cls i θ' = cls i θ then p θ * p θ' / classProb p cls i θ *
        u i (update (play s θ') i a) θ else 0) := fun θ => by
    split_ifs with h
    · rw [mul_sum]
      refine sum_congr rfl fun θ' _ => ?_
      by_cases hc : cls i θ' = cls i θ
      · simp only [hc, ite_true, and_self, h]; ring
      · simp [hc]
    · simp [h]
  have rhs : ∀ θ', (if θ' i = θi then p θ' * ((∑ θ, if cls i θ = cls i θ' then
      p θ * u i (update (play s θ') i a) θ else 0) / classProb p cls i θ') else 0) =
      ∑ θ, (if θ i = θi ∧ cls i θ' = cls i θ then p θ * p θ' / classProb p cls i θ *
        u i (update (play s θ') i a) θ else 0) := fun θ' => by
    split_ifs with h
    · rw [sum_div, mul_sum]
      refine sum_congr rfl fun θ _ => ?_
      by_cases hc : cls i θ = cls i θ'
      · have hθ : θ i = θi := (hcls i θ θ' hc).trans h
        have hP : classProb p cls i θ = classProb p cls i θ' := by
          simp only [classProb, hc]
        simp only [hc, ite_true, hθ, true_and, hP]; ring
      · have : ¬ (θ i = θi ∧ cls i θ' = cls i θ) := fun h' => hc h'.2.symm
        simp [hc, this]
    · refine (sum_eq_zero fun θ _ => ?_).symm
      have : ¬ (θ i = θi ∧ cls i θ' = cls i θ) := fun h' =>
        h ((hcls i θ' θ h'.2).trans h'.1)
      simp [this]
  rw [sum_congr rfl fun θ _ => lhs θ, sum_congr rfl fun θ' _ => rhs θ', sum_comm]

/-- **Jehiel–Koessler.** An ABEE is a Bayesian Nash equilibrium of the game with
class-averaged payoffs. -/
theorem isABEE_iff_isBNE {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ} {s : ∀ i, Θ i → A i} :
    IsABEE u p cls s ↔ IsBNE (classPayoff u p cls) p s := by
  constructor
  · rintro ⟨hp, h⟩
    rw [isBNE_iff_interim hp]
    intro i θi a
    rw [← analogyInterim_eq hcls, ← analogyInterim_eq hcls]
    exact h i θi a
  · intro h
    refine ⟨h.1, fun i θi a => ?_⟩
    rw [analogyInterim_eq hcls, analogyInterim_eq hcls]
    exact (isBNE_iff_interim h.1).1 h i θi a

/-- Two payoff functions that agree wherever the prior is positive give the
same interim payoffs. -/
theorem interim_congr {u v : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    (h : ∀ i a θ, p θ ≠ 0 → u i a θ = v i a θ) (s : ∀ i, Θ i → A i) (i : I) (θi : Θ i)
    (a : A i) : interim u p s i θi a = interim v p s i θi a := by
  unfold interim
  refine sum_congr rfl fun θ _ => ?_
  split_ifs
  · by_cases hp : p θ = 0
    · simp [hp]
    · rw [h i _ θ hp]
  · rfl

/-- **Finest analogy partition: ABEE = Bayesian Nash equilibrium.** -/
theorem isABEE_id_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    {s : ∀ i, Θ i → A i} :
    IsABEE u p (fun _ θ => θ) s ↔ IsBNE u p s := by
  have hcls : IsAnalogyPartition (C := fun _ => ∀ j, Θ j) (fun _ θ => θ) :=
    fun i θ θ' h => by simp only at h; rw [h]
  have hu : ∀ i a θ, p θ ≠ 0 → classPayoff u p (fun _ θ => θ) i a θ = u i a θ := by
    intro i a θ hp
    simp [classPayoff, classProb, hp]
  rw [isABEE_iff_isBNE hcls]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have := (isBNE_iff_interim h.1).1 h
    refine ((isBNE_iff_interim h.1).2 fun i θi a => ?_).2
    rw [← interim_congr hu, ← interim_congr hu]
    exact this i θi a
  · intro h
    refine ⟨h.1, ?_⟩
    have := (isBNE_iff_interim h.1).1 h
    refine ((isBNE_iff_interim h.1).2 fun i θi a => ?_).2
    rw [interim_congr hu, interim_congr hu]
    exact this i θi a

/-- **Coarsest analogy partition: ABEE = fully cursed equilibrium.** -/
theorem isABEE_own_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    {s : ∀ i, Θ i → A i} :
    IsABEE u p (C := Θ) (fun i θ => θ i) s ↔ IsCursedEq 1 u p s := by
  have hcls : IsAnalogyPartition (C := Θ) (fun i θ => θ i) := fun i θ θ' h => h
  have e : classPayoff u p (C := Θ) (fun i θ => θ i) = cursedPayoff 1 u p := by
    funext i a θ
    simp [classPayoff, classProb, cursedPayoff, condPayoff, marg]
  rw [isABEE_iff_isBNE hcls, isCursedEq_iff_isBNE, e]

/-- Non-vacuity: in the lemons market, offering is an ABEE when the buyer
pools the seller's types into one analogy class, but not a Bayesian Nash
equilibrium. -/
theorem lemons_abee : IsABEE lemonsPayoff lemonsPrior (C := fun _ => Bool) (fun i θ => θ i)
    offerPlay ∧ ¬ IsBNE lemonsPayoff lemonsPrior offerPlay :=
  ⟨isABEE_own_iff.2 (lemons_cursed_iff.2 (by norm_num)), lemons_not_bne⟩

end Cursed

end Econ
