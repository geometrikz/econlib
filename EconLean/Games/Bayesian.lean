/-
# Bayesian games

MWG §8.E (Defs. 8.E.1–8.E.2, Prop. 8.E.1); Harsanyi (1967–68). Each player `i` privately
learns a type `θᵢ ∈ Θ i`; types are drawn from a common prior `p` on type profiles. A pure
strategy maps types to actions, `sᵢ : Θ i → A i`. Payoffs `uᵢ(a, θ)` depend on the action
profile and on the type profile.

* `exAnte u p i s = ∑_θ p(θ) uᵢ(s(θ), θ)`: player `i`'s ex-ante expected payoff.
* `IsBNE u p s`: a **Bayesian Nash equilibrium** is a Nash equilibrium of the ex-ante game
  whose strategies are the type-contingent plans (MWG Def. 8.E.1).
* `interim u p s i θᵢ a`: the (unnormalized) interim payoff of type `θᵢ` choosing `a` while
  the others follow `s`: `∑_{θ : θᵢ fixed} p(θ) uᵢ(a, s₋ᵢ(θ₋ᵢ), θ)`. Dividing by the
  marginal probability of `θᵢ` gives the conditional expected payoff; leaving it
  unnormalized makes types of probability zero impose no condition, as in MWG.

Main results:
* `isBNE_iff_interim` (MWG Prop. 8.E.1): `s` is a BNE iff every type of every player
  chooses an action that maximizes its interim payoff.
* `exists_mixed_BNE`: every finite Bayesian game has a Bayesian Nash equilibrium in mixed
  strategies over type-contingent plans (Nash's theorem applied to the ex-ante game).
-/
module

public import EconLean.Games.Mixed

@[expose] public section

namespace Econ

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)] {A : I → Type*}

/-- The action profile when types are `θ` and players follow `s`. -/
def play (s : ∀ i, Θ i → A i) (θ : ∀ i, Θ i) : ∀ i, A i := fun i => s i (θ i)

/-- Player `i`'s ex-ante expected payoff from the strategy profile `s`. -/
def exAnte (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) (i : I)
    (s : ∀ i, Θ i → A i) : ℝ :=
  ∑ θ, p θ * u i (play s θ) θ

/-- **Bayesian Nash equilibrium** (MWG Def. 8.E.1): the prior is a probability
distribution on type profiles, and `s` is a Nash equilibrium of the game whose strategies
are type-contingent plans and whose payoffs are ex-ante expectations. -/
def IsBNE (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (s : ∀ i, Θ i → A i) : Prop :=
  p ∈ lotteries (∀ j, Θ j) ∧ IsNash (exAnte u p) s

/-- Interim payoff (weighted by the prior) of type `θᵢ` of player `i` choosing `a`. -/
def interim (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (s : ∀ i, Θ i → A i) (i : I) (θi : Θ i) (a : A i) : ℝ :=
  ∑ θ, if θ i = θi then p θ * u i (update (play s θ) i a) θ else 0

omit [Fintype I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] in
theorem play_update (s : ∀ i, Θ i → A i) (i : I) (r : Θ i → A i) (θ : ∀ i, Θ i) :
    play (update s i r) θ = update (play s θ) i (r (θ i)) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [play]
  · simp [play, update_of_ne hj]

/-- **Ex-ante = sum of interim.** If `i` switches to the plan `r`, its ex-ante payoff is the
sum over its types of the interim payoff of the action `r` prescribes. -/
theorem exAnte_update (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (s : ∀ i, Θ i → A i) (i : I) (r : Θ i → A i) :
    exAnte u p i (update s i r) = ∑ θi, interim u p s i θi (r θi) := by
  simp only [exAnte, interim, play_update]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Finset.sum_ite_eq univ (θ i)]
  simp

theorem exAnte_eq_sum_interim (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (s : ∀ i, Θ i → A i) (i : I) :
    exAnte u p i s = ∑ θi, interim u p s i θi (s i θi) := by
  conv_lhs => rw [← update_eq_self i s]
  exact exAnte_update u p s i (s i)

/-- **MWG Prop. 8.E.1.** A profile of type-contingent strategies is a Bayesian Nash
equilibrium iff, for every player and every type, the prescribed action maximizes the
interim expected payoff given the others' strategies. -/
theorem isBNE_iff_interim {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} (hp : p ∈ lotteries (∀ j, Θ j)) {s : ∀ i, Θ i → A i} :
    IsBNE u p s ↔ ∀ i θi a, interim u p s i θi a ≤ interim u p s i θi (s i θi) := by
  rw [IsBNE, and_iff_right hp]
  constructor
  · intro h i θi a
    -- Deviate only at type `θᵢ`.
    have hdev := h i (update (s i) θi a)
    rw [exAnte_update, exAnte_eq_sum_interim, ← Finset.add_sum_erase _ _ (mem_univ θi),
      ← Finset.add_sum_erase _ _ (mem_univ θi), update_self] at hdev
    have hrest : ∑ x ∈ univ.erase θi, interim u p s i x (update (s i) θi a x) =
        ∑ x ∈ univ.erase θi, interim u p s i x (s i x) :=
      Finset.sum_congr rfl fun x hx => by rw [update_of_ne (ne_of_mem_erase hx)]
    linarith
  · intro h i r
    rw [exAnte_update, exAnte_eq_sum_interim]
    exact Finset.sum_le_sum fun θi _ => h i θi (r θi)

/-- **Existence of Bayesian Nash equilibrium** in mixed strategies for finite Bayesian
games: Nash's theorem applied to the ex-ante game. A mixed strategy here is a lottery over
whole plans `Θ i → A i`, chosen before the type is drawn; by Kuhn's theorem this is
outcome-equivalent to type-by-type randomization, which is not formalized. Holds for any
prior (the theorem does not need `p` to be a probability). -/
theorem exists_mixed_BNE [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) :
    ∃ σ : ∀ i, (Θ i → A i) → ℝ, IsMixedNash (exAnte u p) σ :=
  exists_isMixedNash (exAnte u p)

end Econ
