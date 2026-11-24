/-
# Behavioral-strategy Bayesian and cursed equilibrium

References. J. Harsanyi (1967–68); E. Eyster and M. Rabin (2005), "Cursed
Equilibrium", *Econometrica* 73(5), §2 (Definition 1, behavioral
strategies); R. Selten (1975) for the agent normal form.

Finite Bayesian game as in `Games/Bayesian.lean`. A **behavioral strategy**
gives each type `θᵢ` a lottery `βᵢ(θᵢ) ∈ Δ(Aᵢ)` (`IsBehavProfile`). Given types
`θ`, the action profile `a` has probability `Π_j β_j(θ_j)(a_j)` (`actProb`).
Type `θᵢ`'s (prior-weighted) interim payoff from action `c` is
`Σ_{θ : θᵢ fixed} p(θ) Σ_a P(a | θ; βᵢ ↦ c) uᵢ(a, θ)` (`behavInterim`), and
`β` is a **behavioral Bayesian Nash equilibrium** if no type gains by a pure
deviation from its lottery (`IsBehavBNE`).

A **`χ`-cursed** type (Eyster–Rabin Definition 1) believes the others play
the *average* strategy `σ̄₋ᵢ(a₋ᵢ | θᵢ) = Σ_{θ₋ᵢ} p(θ₋ᵢ | θᵢ) σ₋ᵢ(a₋ᵢ | θ₋ᵢ)`
with weight `χ` and the true type-contingent strategy with weight `1 − χ`
(`avgProb`, `behavCursedInterim`); `IsBehavCursedEq` is the best-response
condition for these beliefs.

**Results.**
* `behavCursedInterim_eq`, `isBehavCursedEq_iff`: a behavioral profile is a
  `χ`-cursed equilibrium iff it is a behavioral BNE of the game with payoffs
  `(1 − χ) uᵢ(a, θ) + χ E[uᵢ(a, ·) | θᵢ]` (`cursedPayoff`, from `Cursed.lean`),
  extending `isCursedEq_iff_isBNE` from pure to behavioral strategies;
  `isBehavCursedEq_zero_iff`: `0`-cursed equilibrium is behavioral BNE.
* `pureDev_agentPay` (agent normal form): treating every type `(i, θᵢ)` as a
  separate player with payoff `behavInterim`, mixed strategies of the agents
  are behavioral strategies and pure deviations coincide.
* `exists_isBehavBNE`: every finite Bayesian game with a common prior has a
  Bayesian Nash equilibrium in behavioral strategies (Harsanyi), by Nash's
  theorem for the agent normal form.
* `exists_isBehavCursedEq` (Eyster–Rabin): for every `χ`, a `χ`-cursed
  equilibrium in behavioral strategies exists.
* `behavAnalogyInterim_eq`, `isBehavABEE_iff`, `exists_isBehavABEE`
  (Jehiel–Koessler): the same for analogy-based expectation equilibrium with
  behavioral strategies (`IsBehavABEE`, analogy partitions as in
  `Analogy.lean`): it is a behavioral BNE of the class-averaged game, and so
  it always exists (a pure ABEE need not; no counterexample is formalized).
  Analogy classes partition type profiles for each player, as in
  `Analogy.lean`; Jehiel–Koessler's bundling of different opponents is not
  covered.

**Conventions.** Interim payoffs are weighted by the prior, as in
`Games/Bayesian.lean` (MWG): a type of prior probability zero faces no
condition, so these are ex-ante (Harsanyi) equilibria; they coincide with
the interim notion when every type has positive probability, as Eyster and
Rabin assume. Definitions accept any real `χ`; only `χ ∈ [0, 1]` gives
beliefs that are probabilities, and the results hold for every `χ`.
-/
module

public import EconLean.BoundedRationality.Analogy

@[expose] public section

noncomputable section

namespace Econ

namespace Cursed

open Function Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)] {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- A behavioral strategy profile: every type plays a lottery. -/
def IsBehavProfile (β : ∀ i, Θ i → A i → ℝ) : Prop := ∀ i θi, β i θi ∈ lotteries (A i)

/-- Probability of the action profile `a` given the type profile `θ`. -/
def actProb (β : ∀ i, Θ i → A i → ℝ) (θ : ∀ i, Θ i) (a : ∀ i, A i) : ℝ := ∏ j, β j (θ j) (a j)

/-- Player `i` deviates to the pure action `c` (whatever its type). -/
def devTo (β : ∀ i, Θ i → A i → ℝ) (i : I) (c : A i) : ∀ j, Θ j → A j → ℝ :=
  update β i (fun _ => degenerate c)

/-- Prior-weighted interim payoff of type `θᵢ` choosing `c`. -/
def behavInterim (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (β : ∀ i, Θ i → A i → ℝ) (i : I) (θi : Θ i) (c : A i) : ℝ :=
  ∑ θ, if θ i = θi then p θ * ∑ a, actProb (devTo β i c) θ a * u i a θ else 0

/-- **Bayesian Nash equilibrium in behavioral strategies**: no type gains by a
pure deviation from its lottery. -/
def IsBehavBNE (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (β : ∀ i, Θ i → A i → ℝ) : Prop :=
  p ∈ lotteries (∀ j, Θ j) ∧ IsBehavProfile β ∧
    ∀ i θi (c : A i), behavInterim u p β i θi c ≤ ∑ c', β i θi c' * behavInterim u p β i θi c'

/-- The cursed belief: the others' action distribution averaged over their
types given `θᵢ` (with player `i` playing `c`). -/
def avgProb (p : (∀ j, Θ j) → ℝ) (β : ∀ i, Θ i → A i → ℝ) (i : I) (θi : Θ i) (c : A i)
    (a : ∀ j, A j) : ℝ :=
  (∑ θ', if θ' i = θi then p θ' * actProb (devTo β i c) θ' a else 0) / marg p i θi

/-- Prior-weighted interim payoff of a `χ`-cursed type `θᵢ` choosing `c`. -/
def behavCursedInterim (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (β : ∀ i, Θ i → A i → ℝ) (i : I) (θi : Θ i) (c : A i) : ℝ :=
  ∑ θ, if θ i = θi then
    p θ * ∑ a, ((1 - χ) * actProb (devTo β i c) θ a + χ * avgProb p β i θi c a) * u i a θ
  else 0

/-- **`χ`-cursed equilibrium in behavioral strategies** (Eyster–Rabin Def. 1). -/
def IsBehavCursedEq (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (β : ∀ i, Θ i → A i → ℝ) : Prop :=
  p ∈ lotteries (∀ j, Θ j) ∧ IsBehavProfile β ∧
    ∀ i θi (c : A i), behavCursedInterim χ u p β i θi c ≤
      ∑ c', β i θi c' * behavCursedInterim χ u p β i θi c'

/-- The cursed interim payoff is the interim payoff of the modified game. -/
theorem behavCursedInterim_eq (χ : ℝ) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    (p : (∀ j, Θ j) → ℝ) (β : ∀ i, Θ i → A i → ℝ) (i : I) (θi : Θ i) (c : A i) :
    behavCursedInterim χ u p β i θi c = behavInterim (cursedPayoff χ u p) p β i θi c := by
  set F := univ.filter fun θ : ∀ j, Θ j => θ i = θi
  set P := actProb (devTo β i c)
  set m := marg p i θi
  have hm : m = ∑ θ ∈ F, p θ := by simp only [m, marg, F, sum_filter]
  have hc : ∀ a, condPayoff u p i a θi = (∑ θ' ∈ F, p θ' * u i a θ') / m := fun a => by
    simp only [condPayoff, F, sum_filter]; rfl
  have hR : behavInterim (cursedPayoff χ u p) p β i θi c = ∑ θ ∈ F, p θ * ∑ a, P θ a *
      ((1 - χ) * u i a θ + χ * ((∑ θ' ∈ F, p θ' * u i a θ') / m)) := by
    simp only [behavInterim, ← sum_filter]
    refine sum_congr rfl fun θ hθ => ?_
    simp only [cursedPayoff, (mem_filter.1 hθ).2, hc]; rfl
  have hL : behavCursedInterim χ u p β i θi c = ∑ θ ∈ F, p θ * ∑ a,
      ((1 - χ) * P θ a + χ * ((∑ θ' ∈ F, p θ' * P θ' a) / m)) * u i a θ := by
    simp only [behavCursedInterim, avgProb, F, sum_filter]; rfl
  rw [hL, hR]
  simp only [add_mul, mul_add, sum_add_distrib, mul_sum, div_eq_mul_inv, sum_mul]
  congr 1
  · refine sum_congr rfl fun θ _ => sum_congr rfl fun a _ => by ring
  · rw [sum_comm]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun θ _ => sum_congr rfl fun θ' _ => by ring

/-- **Eyster–Rabin reduction (behavioral strategies).** -/
theorem isBehavCursedEq_iff {χ : ℝ} {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} {β : ∀ i, Θ i → A i → ℝ} :
    IsBehavCursedEq χ u p β ↔ IsBehavBNE (cursedPayoff χ u p) p β := by
  simp only [IsBehavCursedEq, IsBehavBNE, behavCursedInterim_eq]

theorem isBehavCursedEq_zero_iff {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ}
    {p : (∀ j, Θ j) → ℝ} {β : ∀ i, Θ i → A i → ℝ} :
    IsBehavCursedEq 0 u p β ↔ IsBehavBNE u p β := by
  have : cursedPayoff 0 u p = u := by
    funext i a θ; simp [cursedPayoff]
  rw [isBehavCursedEq_iff, this]

/-! ### The agent normal form -/

/-- Payoff of agent `(i, θᵢ)` in the agent normal form, at a pure profile
`b` of the agents' actions. -/
def agentPay (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) :
    (Σ i, Θ i) → (∀ k : Σ i, Θ i, A k.1) → ℝ :=
  fun k b => ∑ θ, if θ k.1 = k.2 then p θ * u k.1 (fun j => b ⟨j, θ j⟩) θ else 0

/-- The behavioral profile of an agent-form mixed profile. -/
def toBehav (τ : ∀ k : Σ i, Θ i, A k.1 → ℝ) : ∀ i, Θ i → A i → ℝ := fun i θi => τ ⟨i, θi⟩

/-- **Marginalization**: agents who are not the realized types integrate out. -/
theorem sum_agent_marginal (τ : ∀ k : Σ i, Θ i, A k.1 → ℝ)
    (hτ : ∀ k, ∑ x, τ k x = 1) (θ : ∀ i, Θ i) (g : (∀ j, A j) → ℝ) :
    ∑ b : (∀ k : Σ i, Θ i, A k.1), (∏ k, τ k (b k)) * g (fun j => b ⟨j, θ j⟩) =
      ∑ a : (∀ j, A j), (∏ j, τ ⟨j, θ j⟩ (a j)) * g a := by
  -- write `g (b ∘ ι)` as a sum over `a` with an indicator
  have h1 : ∀ b : (∀ k : Σ i, Θ i, A k.1), g (fun j => b ⟨j, θ j⟩) =
      ∑ a : (∀ j, A j), g a * ∏ k : Σ i, Θ i,
        (if k.2 = θ k.1 then (if b k = a k.1 then (1 : ℝ) else 0) else 1) := by
    intro b
    have e : ∀ a : (∀ j, A j), (∏ k : Σ i, Θ i,
        (if k.2 = θ k.1 then (if b k = a k.1 then (1 : ℝ) else 0) else 1)) =
          if (fun j => b ⟨j, θ j⟩) = a then 1 else 0 := by
      intro a
      rw [Fintype.prod_sigma]
      simp only
      rw [prod_congr rfl fun j _ => Fintype.prod_ite_eq' (θ j)
        (fun t => if b ⟨j, t⟩ = a j then (1 : ℝ) else 0)]
      rw [Fintype.prod_boole]
      congr 1
      exact propext ⟨fun h => funext h, fun h j => congrFun h j⟩
    simp only [e, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq]
    simp
  simp only [h1, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  have h2 : ∑ b : (∀ k : Σ i, Θ i, A k.1), (∏ k, τ k (b k)) * (g a * ∏ k : Σ i, Θ i,
        (if k.2 = θ k.1 then (if b k = a k.1 then (1 : ℝ) else 0) else 1)) =
      g a * ∏ k : Σ i, Θ i, ∑ x, τ k x *
        (if k.2 = θ k.1 then (if x = a k.1 then (1 : ℝ) else 0) else 1) := by
    rw [Fintype.prod_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [prod_mul_distrib]; ring
  rw [h2]
  have h3 : ∀ k : Σ i, Θ i, ∑ x, τ k x *
      (if k.2 = θ k.1 then (if x = a k.1 then (1 : ℝ) else 0) else 1) =
        if k.2 = θ k.1 then τ k (a k.1) else 1 := by
    intro k
    split_ifs
    · simp only [mul_ite, mul_one, mul_zero]; rw [sum_ite_eq']; simp
    · simp only [mul_one]; exact hτ k
  simp only [h3]
  rw [Fintype.prod_sigma]
  simp only
  rw [prod_congr rfl fun j _ => Fintype.prod_ite_eq' (θ j) (fun t => τ ⟨j, t⟩ (a j))]
  ring

/-- **Agent normal form**: pure deviations of agent `(i, θᵢ)` earn the interim
payoff of type `θᵢ` against the induced behavioral profile. -/
theorem pureDev_agentPay (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    {τ : ∀ k : Σ i, Θ i, A k.1 → ℝ} (hτ : IsMixedProfile τ) (i : I) (θi : Θ i) (c : A i) :
    pureDev (agentPay u p) τ ⟨i, θi⟩ c = behavInterim u p (toBehav τ) i θi c := by
  set τ' := update τ ⟨i, θi⟩ (degenerate c)
  have hτ' : ∀ k, ∑ x, τ' k x = 1 := by
    intro k
    by_cases hk : k = ⟨i, θi⟩
    · subst hk; simp only [τ', update_self]; exact (degenerate_mem c).2
    · simp only [τ', update_of_ne hk]; exact (hτ k).2
  simp only [pureDev, mixedPayoff, profileProb, agentPay, behavInterim, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun θ _ => ?_
  split_ifs with hθ
  · have := sum_agent_marginal τ' hτ' θ (fun a => p θ * u i a θ)
    rw [this]
    refine sum_congr rfl fun a _ => ?_
    have hp : (∏ j, τ' ⟨j, θ j⟩ (a j)) = actProb (devTo (toBehav τ) i c) θ a := by
      refine prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; subst hθ
        simp [τ', devTo]
      · have hne : (⟨j, θ j⟩ : Σ i, Θ i) ≠ ⟨i, θi⟩ := fun h => hj (congrArg Sigma.fst h)
        simp only [τ', devTo, toBehav, update_of_ne hne, update_of_ne hj]
    rw [hp]; ring
  · simp

/-- **Existence of Bayesian Nash equilibrium in behavioral strategies**
(Harsanyi): Nash's theorem applied to the agent normal form. -/
theorem exists_isBehavBNE [∀ i, Nonempty (A i)] (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    {p : (∀ j, Θ j) → ℝ} (hp : p ∈ lotteries (∀ j, Θ j)) :
    ∃ β : ∀ i, Θ i → A i → ℝ, IsBehavBNE u p β := by
  obtain ⟨τ, hτ⟩ := exists_isMixedNash (agentPay u p)
  refine ⟨toBehav τ, hp, fun i θi => hτ.1 ⟨i, θi⟩, fun i θi c => ?_⟩
  have h := (isMixedNash_iff_pure hτ.1).1 hτ ⟨i, θi⟩ c
  rw [mixedPayoff_eq_sum_pureDev] at h
  simp only [pureDev_agentPay u p hτ.1] at h
  exact h

/-- **Existence of cursed equilibrium in behavioral strategies**
(Eyster–Rabin). -/
theorem exists_isBehavCursedEq [∀ i, Nonempty (A i)] (χ : ℝ)
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) {p : (∀ j, Θ j) → ℝ}
    (hp : p ∈ lotteries (∀ j, Θ j)) :
    ∃ β : ∀ i, Θ i → A i → ℝ, IsBehavCursedEq χ u p β := by
  obtain ⟨β, hβ⟩ := exists_isBehavBNE (cursedPayoff χ u p) hp
  exact ⟨β, isBehavCursedEq_iff.2 hβ⟩

/-! ### Analogy-based expectation equilibrium in behavioral strategies -/

section ABEE

variable {C : I → Type*} [∀ i, DecidableEq (C i)]

/-- The analogy-based interim payoff of type `θᵢ` choosing `c` when the others
follow the behavioral profile `β`: the others' action distribution is averaged
over the analogy class of the true type profile. -/
def behavAnalogyInterim (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (cls : ∀ i, (∀ j, Θ j) → C i) (β : ∀ i, Θ i → A i → ℝ) (i : I) (θi : Θ i) (c : A i) : ℝ :=
  ∑ θ, if θ i = θi then p θ * ∑ θ', (if cls i θ' = cls i θ then p θ' / classProb p cls i θ
    else 0) * ∑ a, actProb (devTo β i c) θ' a * u i a θ else 0

/-- **ABEE in behavioral strategies** (Jehiel–Koessler). -/
def IsBehavABEE (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ)
    (cls : ∀ i, (∀ j, Θ j) → C i) (β : ∀ i, Θ i → A i → ℝ) : Prop :=
  p ∈ lotteries (∀ j, Θ j) ∧ IsBehavProfile β ∧
    ∀ i θi (c : A i), behavAnalogyInterim u p cls β i θi c ≤
      ∑ c', β i θi c' * behavAnalogyInterim u p cls β i θi c'

/-- The behavioral analogy-based interim payoff is the interim payoff of the
class-averaged game. -/
theorem behavAnalogyInterim_eq {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ) (p : (∀ j, Θ j) → ℝ) (β : ∀ i, Θ i → A i → ℝ)
    (i : I) (θi : Θ i) (c : A i) :
    behavAnalogyInterim u p cls β i θi c = behavInterim (classPayoff u p cls) p β i θi c := by
  set P := actProb (devTo β i c)
  set G : (∀ j, Θ j) → (∀ j, Θ j) → ℝ := fun θ' θ => ∑ a, P θ' a * u i a θ
  simp only [behavAnalogyInterim, behavInterim, classPayoff]
  have lhs : ∀ θ, (if θ i = θi then p θ * ∑ θ', (if cls i θ' = cls i θ then
      p θ' / classProb p cls i θ else 0) * ∑ a, P θ' a * u i a θ else 0) =
      ∑ θ', (if θ i = θi ∧ cls i θ' = cls i θ then p θ * p θ' / classProb p cls i θ *
        G θ' θ else 0) := fun θ => by
    split_ifs with h
    · rw [mul_sum]
      refine sum_congr rfl fun θ' _ => ?_
      by_cases hc : cls i θ' = cls i θ
      · simp only [hc, ite_true, and_self, h, G]; ring
      · simp [hc]
    · simp [h]
  have rhs : ∀ θ', (if θ' i = θi then p θ' * ∑ a, P θ' a * ((∑ θ, if cls i θ = cls i θ' then
      p θ * u i a θ else 0) / classProb p cls i θ') else 0) =
      ∑ θ, (if θ i = θi ∧ cls i θ' = cls i θ then p θ * p θ' / classProb p cls i θ *
        G θ' θ else 0) := fun θ' => by
    split_ifs with h
    · have e : ∑ a, P θ' a * ((∑ θ, if cls i θ = cls i θ' then p θ * u i a θ else 0) /
          classProb p cls i θ') = (∑ θ, if cls i θ = cls i θ' then p θ * G θ' θ else 0) /
          classProb p cls i θ' := by
        simp only [G, mul_div_assoc', mul_sum, ← sum_div]
        rw [sum_comm]
        refine congrArg (· / _) (sum_congr rfl fun θ _ => ?_)
        split_ifs
        · exact sum_congr rfl fun a _ => by ring
        · simp
      rw [e, sum_div, mul_sum]
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

/-- **Jehiel–Koessler (behavioral strategies).** -/
theorem isBehavABEE_iff {cls : ∀ i, (∀ j, Θ j) → C i} (hcls : IsAnalogyPartition cls)
    {u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ} {p : (∀ j, Θ j) → ℝ} {β : ∀ i, Θ i → A i → ℝ} :
    IsBehavABEE u p cls β ↔ IsBehavBNE (classPayoff u p cls) p β := by
  simp only [IsBehavABEE, IsBehavBNE, behavAnalogyInterim_eq hcls]

/-- **Existence of ABEE in behavioral strategies.** -/
theorem exists_isBehavABEE [∀ i, Nonempty (A i)] {cls : ∀ i, (∀ j, Θ j) → C i}
    (hcls : IsAnalogyPartition cls) (u : I → (∀ j, A j) → (∀ j, Θ j) → ℝ)
    {p : (∀ j, Θ j) → ℝ} (hp : p ∈ lotteries (∀ j, Θ j)) :
    ∃ β : ∀ i, Θ i → A i → ℝ, IsBehavABEE u p cls β := by
  obtain ⟨β, hβ⟩ := exists_isBehavBNE (classPayoff u p cls) hp
  exact ⟨β, (isBehavABEE_iff hcls).2 hβ⟩

end ABEE

end Cursed

end Econ
