/-
# Mechanisms, implementation and the revelation principle

MWG §23.B–23.D (Defs. 23.B.1–23.B.5, 23.D.1; Props. 23.C.1, 23.D.1). Each agent `i` has a
private type `θᵢ ∈ Θ i` and utility `u i x θᵢ` over outcomes `x ∈ X`. A **social choice
function** `f : (∀ i, Θ i) → X` picks an outcome for each type profile. A **mechanism**
gives each agent a message space `M i` and an outcome rule `g : (∀ i, M i) → X`.

* `IsDominantEq u g s`: the strategies `sᵢ : Θ i → M i` form a dominant-strategy
  equilibrium: whatever the others send, `sᵢ θᵢ` is optimal for type `θᵢ`.
* `IsDSIC u f`: `f` is **truthfully implementable in dominant strategies** (strategy-proof):
  reporting the true type is optimal whatever the others report.
* `IsBIC u p f`: `f` is **Bayesian incentive compatible** for the prior `p`: truth-telling is
  optimal at the interim stage when the others report truthfully.

Main results:
* `revelation_dominant` (MWG Prop. 23.C.1): if a mechanism has a dominant-strategy equilibrium
  `s`, the social choice function `g ∘ s` it implements is strategy-proof.
* `revelation_bayesian` (MWG Prop. 23.D.1): if `s` is a Bayesian Nash equilibrium of the
  mechanism, `g ∘ s` is Bayesian incentive compatible. This reuses the interim
  characterization of BNE in `Games/Bayesian.lean`.
-/
module

public import EconLean.Games.Bayesian

@[expose] public section

namespace Econ

open Function

variable {I : Type*} [DecidableEq I] {Θ : I → Type*} {X : Type*} {M : I → Type*}

/-- `s` is a **dominant-strategy equilibrium** of the mechanism `g` (MWG Def. 23.B.5). -/
def IsDominantEq (u : ∀ i, X → Θ i → ℝ) (g : (∀ i, M i) → X) (s : ∀ i, Θ i → M i) : Prop :=
  ∀ i (θi : Θ i) (m : ∀ j, M j) (mi : M i),
    u i (g (update m i mi)) θi ≤ u i (g (update m i (s i θi))) θi

/-- `f` is **strategy-proof** (truthfully implementable in dominant strategies, MWG Def.
23.B.6): reporting the true type is optimal for every report of the others. -/
def IsDSIC (u : ∀ i, X → Θ i → ℝ) (f : (∀ i, Θ i) → X) : Prop :=
  ∀ i (θ : ∀ j, Θ j) (θi' : Θ i), u i (f (update θ i θi')) (θ i) ≤ u i (f θ) (θ i)

theorem play_update' (s : ∀ i, Θ i → M i) (θ : ∀ j, Θ j) (i : I) (θi' : Θ i) :
    (fun j => s j (update θ i θi' j)) = update (fun j => s j (θ j)) i (s i θi') := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [update_of_ne hj]

/-- **Revelation principle, dominant strategies** (MWG Prop. 23.C.1). -/
theorem revelation_dominant {u : ∀ i, X → Θ i → ℝ} {g : (∀ i, M i) → X} {s : ∀ i, Θ i → M i}
    (h : IsDominantEq u g s) : IsDSIC u fun θ => g fun j => s j (θ j) := by
  intro i θ θi'
  have := h i (θ i) (fun j => s j (θ j)) (s i θi')
  simp only [play_update' s θ i θi']
  have e : update (fun j => s j (θ j)) i (s i (θ i)) = fun j => s j (θ j) := by
    simp
  rwa [e] at this

variable [Fintype I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]

/-- `f` is **Bayesian incentive compatible** for the prior `p` (MWG Def. 23.D.1, written with
prior-weighted interim payoffs, so types of probability zero are unconstrained). -/
def IsBIC (u : ∀ i, X → Θ i → ℝ) (p : (∀ j, Θ j) → ℝ) (f : (∀ i, Θ i) → X) : Prop :=
  ∀ i (θi θi' : Θ i),
    (∑ θ, if θ i = θi then p θ * u i (f (update θ i θi')) θi else 0) ≤
      ∑ θ, if θ i = θi then p θ * u i (f θ) θi else 0

/-- The Bayesian game induced by a mechanism: actions are messages, and `i`'s payoff from
the message profile `m` at types `θ` is `u i (g m) (θ i)`. -/
def mechGame (u : ∀ i, X → Θ i → ℝ) (g : (∀ i, M i) → X) : I → (∀ j, M j) → (∀ j, Θ j) → ℝ :=
  fun i m θ => u i (g m) (θ i)

/-- **Revelation principle, Bayesian** (MWG Prop. 23.D.1): the outcome of a Bayesian Nash
equilibrium of any mechanism is a Bayesian incentive compatible social choice function. -/
theorem revelation_bayesian {u : ∀ i, X → Θ i → ℝ} {g : (∀ i, M i) → X}
    {p : (∀ j, Θ j) → ℝ} {s : ∀ i, Θ i → M i} (h : IsBNE (mechGame u g) p s) :
    IsBIC u p fun θ => g fun j => s j (θ j) := by
  intro i θi θi'
  have hint := (isBNE_iff_interim h.1).1 h i θi (s i θi')
  simp only [interim, mechGame] at hint
  -- Sending `sᵢ θᵢ'` is the same as reporting `θᵢ'` in the direct mechanism.
  have e1 : ∀ θ : ∀ j, Θ j, θ i = θi →
      update (fun j => s j (θ j)) i (s i θi') = fun j => s j (update θ i θi' j) := by
    intro θ _; rw [play_update']
  have e2 : ∀ θ : ∀ j, Θ j, θ i = θi →
      update (fun j => s j (θ j)) i (s i θi) = fun j => s j (θ j) := by
    intro θ hθ; rw [← hθ]; simp
  calc (∑ θ, if θ i = θi then p θ * u i (g fun j => s j (update θ i θi' j)) θi else 0)
      = ∑ θ, if θ i = θi then p θ * u i (g (update (fun j => s j (θ j)) i (s i θi'))) (θ i)
          else 0 :=
        Finset.sum_congr rfl fun θ _ => by
          split_ifs with hθ
          · rw [e1 θ hθ, hθ]
          · rfl
    _ ≤ ∑ θ, if θ i = θi then p θ * u i (g (update (fun j => s j (θ j)) i (s i θi))) (θ i)
          else 0 := hint
    _ = _ := Finset.sum_congr rfl fun θ _ => by
          split_ifs with hθ
          · rw [e2 θ hθ, hθ]
          · rfl

end Econ
