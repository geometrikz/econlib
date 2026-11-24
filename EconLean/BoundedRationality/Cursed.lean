/-
# Cursed equilibrium

Reference. E. Eyster and M. Rabin (2005), "Cursed Equilibrium",
*Econometrica* 73(5) (definition of `χ`-cursed equilibrium; the reduction to
Bayesian Nash equilibrium of a modified game is stated here in our own form).

A finite Bayesian game (`Games/Bayesian.lean`): players `i`, types `θᵢ`,
common prior `p`, actions `aᵢ`, payoffs `uᵢ(a, θ)`. A **`χ`-cursed** player
of type `θᵢ` correctly predicts the distribution of the others' actions, but
with weight `χ` neglects how those actions depend on the others' types: it
evaluates each action profile by the payoff averaged over the others' types
given its own, `E[uᵢ(a, θ) | θᵢ]` (`condPayoff`). With pure type-contingent
strategies `s`, its (prior-weighted) interim payoff is (`cursedInterim`)

    (1 − χ) Σ_θ p(θ) uᵢ(a, s₋ᵢ(θ₋ᵢ), θ) + χ Σ_θ p(θ) E[uᵢ(a, s₋ᵢ(θ₋ᵢ), ·) | θᵢ]

(sums over `θ` with `θᵢ` fixed). `s` is a **`χ`-cursed equilibrium** if every
type's action maximizes it (`IsCursedEq`).

**Results.**
* `cursedInterim_eq`, `isCursedEq_iff_isBNE` (Eyster–Rabin): `s` is a
  `χ`-cursed equilibrium iff it is a Bayesian Nash equilibrium of the game
  with payoffs `(1 − χ) uᵢ(a, θ) + χ E[uᵢ(a, ·) | θᵢ]` (`cursedPayoff`).
* `isCursedEq_zero_iff`: `0`-cursed equilibrium is Bayesian Nash equilibrium.
* `exists_mixed_cursed`: the modified game has a mixed (plan-level) Bayesian
  Nash equilibrium over plans. Eyster–Rabin's behavioral-strategy cursed
  equilibrium, its reduction and its existence are in `CursedMixed.lean`.
* **Adverse selection** (`lemons_*`): a seller knows whether a car is a lemon
  (worth `0` to it, `3` to the buyer) or a peach (`10` and `15`), each with
  probability `1/2`; the buyer offers `6` or nothing, and the seller accepts
  `6` exactly when it has a lemon. Offering loses money (`−3/2`), so it is not
  a Bayesian Nash equilibrium (`lemons_not_bne`), but a `χ`-cursed buyer, who
  ignores that only lemons are sold, offers in equilibrium iff `χ ≥ 1/2`
  (`lemons_cursed_iff`): the winner's curse. (Definitions accept any real
  `χ`; only `χ ∈ [0, 1]` is economically meaningful.)

Only pure type-contingent strategies are treated in this file; behavioral
mixed strategies are in `CursedMixed.lean`.
-/
module

public import EconLean.Games.Bayesian

@[expose] public section

noncomputable section

namespace Econ

namespace Cursed

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)] {A : I → Type*}

/-- Marginal probability of type `θᵢ`. -/
def marg (p : (∀ j, Θ j) → ℝ) (i : I) (θi : Θ i) : ℝ := ∑ θ, if θ i = θi then p θ else 0

/-- `E[uᵢ(a, θ) | θᵢ]`: the payoff of the action profile `a` averaged over the
others' types given `θᵢ`. -/
def condPayoff (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) (i : I)
    (a : ∀ j, A j) (θi : Θ i) : ℝ :=
  (∑ θ, if θ i = θi then p θ * u i a θ else 0) / marg p i θi

/-- The Eyster–Rabin modified payoffs. -/
def cursedPayoff (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) :
    I → (∀ j, A j) → (∀ j, Θ j) → ℝ :=
  fun i a θ => (1 - χ) * u i a θ + χ * condPayoff u p i a (θ i)

/-- The prior-weighted interim payoff of a `χ`-cursed type `θᵢ` choosing `a`. -/
def cursedInterim (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (s : ∀ i, Θ i → A i) (i : I) (θi : Θ i) (a : A i) : ℝ :=
  (1 - χ) * interim u p s i θi a +
    χ * ∑ θ, if θ i = θi then p θ * condPayoff u p i (update (play s θ) i a) θi else 0

/-- **`χ`-cursed equilibrium** (pure strategies). -/
def IsCursedEq (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (s : ∀ i, Θ i → A i) : Prop :=
  p ∈ lotteries (∀ j, Θ j) ∧
    ∀ i θi a, cursedInterim χ u p s i θi a ≤ cursedInterim χ u p s i θi (s i θi)

/-- The cursed interim payoff is the ordinary interim payoff of the modified
game. -/
theorem cursedInterim_eq (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    (p : (∀ j, Θ j) → ℝ) (s : ∀ i, Θ i → A i) (i : I) (θi : Θ i) (a : A i) :
    cursedInterim χ u p s i θi a = interim (cursedPayoff χ u p) p s i θi a := by
  simp only [cursedInterim, interim, cursedPayoff, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun θ _ => ?_
  split_ifs with h
  · rw [h]; ring
  · ring

/-- **Eyster–Rabin.** A `χ`-cursed equilibrium is exactly a Bayesian Nash
equilibrium of the game with payoffs `(1 − χ) uᵢ + χ E[uᵢ | θᵢ]`. -/
theorem isCursedEq_iff_isBNE {χ : ℝ} {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} {s : ∀ i, Θ i → A i} :
    IsCursedEq χ u p s ↔ IsBNE (cursedPayoff χ u p) p s := by
  constructor
  · rintro ⟨hp, h⟩
    rw [isBNE_iff_interim hp]
    intro i θi a
    rw [← cursedInterim_eq, ← cursedInterim_eq]
    exact h i θi a
  · intro h
    refine ⟨h.1, fun i θi a => ?_⟩
    rw [cursedInterim_eq, cursedInterim_eq]
    exact (isBNE_iff_interim h.1).1 h i θi a

/-- **`0`-cursed equilibrium is Bayesian Nash equilibrium.** -/
theorem isCursedEq_zero_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ}
    {s : ∀ i, Θ i → A i} : IsCursedEq 0 u p s ↔ IsBNE u p s := by
  have : cursedPayoff 0 u p = u := by
    funext i a θ; simp [cursedPayoff]
  rw [isCursedEq_iff_isBNE, this]

/-- **Existence** (mixed plans): the modified game has a mixed Bayesian Nash
equilibrium. -/
theorem exists_mixed_cursed [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    (p : (∀ j, Θ j) → ℝ) :
    ∃ σ : ∀ i, (Θ i → A i) → ℝ, IsMixedNash (exAnte (cursedPayoff χ u p) p) σ :=
  exists_mixed_BNE _ p

/-! ### Adverse selection and the winner's curse

Players are `Bool`: `false` is the buyer, `true` the seller. Every player's
type is a `Bool`; the buyer's type is always `false`, the seller's type is
`true` for a peach and `false` for a lemon. Actions are `Bool`: the buyer
offers `6` (`true`) or nothing; the seller accepts (`true`) or not. -/

/-- The prior: buyer type `false`; lemon or peach with probability `1/2`. -/
def lemonsPrior (θ : Bool → Bool) : ℝ := if θ false = false then 1 / 2 else 0

/-- Payoffs: on trade at price `6`, the buyer gets `15 − 6` (peach) or
`3 − 6` (lemon), the seller `6 − 10` or `6 − 0`. -/
def lemonsPayoff (i : Bool) (a : Bool → Bool) (θ : Bool → Bool) : ℝ :=
  if a false && a true then
    (if i then 6 - (if θ true then 10 else 0) else (if θ true then 15 else 3) - 6)
  else 0

/-- The buyer offers; the seller sells exactly the lemon. -/
def offerPlay (i : Bool) (θi : Bool) : Bool := if i then !θi else true

theorem lemonsPrior_mem : lemonsPrior ∈ lotteries (Bool → Bool) := by
  refine ⟨fun θ => by unfold lemonsPrior; split_ifs <;> norm_num, ?_⟩
  rw [sum_bool_arrow_bool]; simp [lemonsPrior]; norm_num

/-- The buyer's `χ`-cursed interim payoff from offering is `(2χ − 1)·3/2`
(the marginal of the buyer's type is `1`): `(1 − χ)(−3/2)` from the true
lemon-only sales plus `χ · 3/2` from the type-blind belief. -/
theorem lemons_buyer_offer (χ : ℝ) :
    cursedInterim χ lemonsPayoff lemonsPrior offerPlay false false true =
      (2 * χ - 1) * (3 / 2) := by
  simp only [cursedInterim, interim, condPayoff, marg, sum_bool_arrow_bool, lemonsPrior,
    lemonsPayoff, offerPlay, play, update]
  norm_num
  ring

theorem lemons_buyer_none (χ : ℝ) :
    cursedInterim χ lemonsPayoff lemonsPrior offerPlay false false false = 0 := by
  simp only [cursedInterim, interim, condPayoff, marg, sum_bool_arrow_bool, lemonsPrior,
    lemonsPayoff, offerPlay, play, update]
  norm_num

/-- **The winner's curse.** Offering (with the seller selling only lemons) is a
`χ`-cursed equilibrium iff `χ ≥ 1/2`. -/
theorem lemons_cursed_iff {χ : ℝ} :
    IsCursedEq χ lemonsPayoff lemonsPrior offerPlay ↔ 1 / 2 ≤ χ := by
  constructor
  · rintro ⟨-, h⟩
    have := h false false false
    rw [lemons_buyer_none, show offerPlay false false = true from rfl,
      lemons_buyer_offer] at this
    linarith
  · intro hχ
    refine ⟨lemonsPrior_mem, fun i θi a => ?_⟩
    cases i <;> cases θi <;> cases a <;>
      simp only [cursedInterim, interim, condPayoff, marg, sum_bool_arrow_bool, lemonsPrior,
        lemonsPayoff, offerPlay, play, update] <;> norm_num <;> nlinarith

/-- Offering is not a Bayesian Nash equilibrium: a rational buyer foresees that
only lemons are sold. -/
theorem lemons_not_bne : ¬ IsBNE lemonsPayoff lemonsPrior offerPlay := by
  rw [← isCursedEq_zero_iff, lemons_cursed_iff]
  norm_num

end Cursed

end Econ
