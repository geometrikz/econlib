/-
# Bayes correlated equilibrium (Bergemann–Morris 2016)

Bergemann and Morris (2016), "Bayes correlated equilibrium and the comparison of information
structures in games", Theorem 1. A finite **basic game** has states `θ ∈ Θ` with prior `ψ`,
players `i ∈ I` with actions `A i` and payoffs `u i θ a`. An **information structure** gives
each player a signal `tᵢ ∈ T i`, drawn jointly as `π θ t`.

A **Bayes correlated equilibrium** (BCE) is a joint law `ν θ t a` of states, signals and
action profiles whose marginal on `(θ, t)` is `ψ θ π θ t` and which is **obedient**: a player
told her signal `tᵢ` and recommended `aᵢ` cannot gain by playing `aᵢ'` instead (`IsBCE`).

An **expansion** of `(T, π)` adds further signals `rᵢ ∈ R i`, drawn as `π' θ t r` with
`∑_r π' θ t r = π θ t`. A pure strategy `βᵢ(tᵢ, rᵢ)` profile is a **Bayes Nash equilibrium**
of the expanded game if no player gains by changing her action after any pair of signals
(`IsExpansionBNE`); its outcome law is `bneOutcome`.

* `bneOutcome_isBCE`: the outcome of any Bayes Nash equilibrium of any expansion is a BCE.
* `isBCE_bneOutcome` and `isBCE_iff`: conversely every BCE arises this way, from the
  expansion in which each player's extra signal is her recommended action and she obeys it.

So the BCE set is exactly the set of outcomes that some additional information can induce in
equilibrium: Aumann's correlated equilibrium is the case without payoff uncertainty.
Equilibria of expansions are in pure strategies here; mixed strategies add no outcomes since
randomization can be moved into the extra signals, but that reduction is not formalized.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

open Finset Function

universe uA

variable {Θ I : Type*} [Fintype Θ] [Fintype I] [DecidableEq I]
  {A : I → Type uA} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

/-- **Bayes correlated equilibrium** of the basic game `(ψ, u)` with information structure
`π` (Bergemann–Morris 2016, Def. 1). -/
def IsBCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (u : I → Θ → (∀ i, A i) → ℝ)
    (ν : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) : Prop :=
  (∀ θ t a, 0 ≤ ν θ t a) ∧ (∀ θ t, ∑ a, ν θ t a = ψ θ * π θ t) ∧
    ∀ i (tᵢ : T i) (aᵢ aᵢ' : A i),
      ∑ θ, ∑ t ∈ univ.filter (fun t : ∀ j, T j => t i = tᵢ),
        ∑ a ∈ univ.filter (fun a : ∀ j, A j => a i = aᵢ),
          ν θ t a * (u i θ (update a i aᵢ') - u i θ a) ≤ 0

section Expansion

variable {R : I → Type*} [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]

/-- `π'` is an **expansion** of `π`: a joint law of the original and extra signals whose
marginal on the original signals is `π`. -/
def IsExpansion (π : Θ → (∀ i, T i) → ℝ) (π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ) : Prop :=
  (∀ θ t r, 0 ≤ π' θ t r) ∧ ∀ θ t, ∑ r, π' θ t r = π θ t

/-- The action profile played under the pure strategies `β` at signals `(t, r)`. -/
def playAt (β : ∀ i, T i → R i → A i) (t : ∀ i, T i) (r : ∀ i, R i) : ∀ i, A i :=
  fun j => β j (t j) (r j)

/-- `β` is a **Bayes Nash equilibrium** of the expanded game: after every pair of signals
`(tᵢ, rᵢ)` no player gains by switching her action. -/
def IsExpansionBNE (ψ : Θ → ℝ) (u : I → Θ → (∀ i, A i) → ℝ)
    (π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ) (β : ∀ i, T i → R i → A i) : Prop :=
  ∀ i (tᵢ : T i) (rᵢ : R i) (aᵢ' : A i),
    ∑ θ, ∑ t ∈ univ.filter (fun t : ∀ j, T j => t i = tᵢ),
      ∑ r ∈ univ.filter (fun r : ∀ j, R j => r i = rᵢ),
        ψ θ * π' θ t r * (u i θ (update (playAt β t r) i aᵢ') - u i θ (playAt β t r)) ≤ 0

/-- The joint law of states, original signals and actions induced by `β`. -/
def bneOutcome (ψ : Θ → ℝ) (π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ)
    (β : ∀ i, T i → R i → A i) (θ : Θ) (t : ∀ i, T i) (a : ∀ i, A i) : ℝ :=
  ∑ r ∈ univ.filter (fun r => playAt β t r = a), ψ θ * π' θ t r

omit [Fintype Θ] [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)] [∀ i, DecidableEq (R i)] in
/-- Regrouping the obedience sum by the extra signals. -/
lemma sum_bneOutcome_mul (ψ : Θ → ℝ) (π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ)
    (β : ∀ i, T i → R i → A i) (θ : Θ) (t : ∀ i, T i) (i : I) (aᵢ : A i)
    (Δ : (∀ j, A j) → ℝ) :
    ∑ a ∈ univ.filter (fun a : ∀ j, A j => a i = aᵢ), bneOutcome ψ π' β θ t a * Δ a =
      ∑ r ∈ univ.filter (fun r : ∀ j, R j => β i (t i) (r i) = aᵢ),
        ψ θ * π' θ t r * Δ (playAt β t r) := by
  rw [← sum_fiberwise (s := univ.filter fun r : ∀ j, R j => β i (t i) (r i) = aᵢ)
    (g := playAt β t), sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : a i = aᵢ
  · simp only [ha, ↓reduceIte]
    rw [bneOutcome, sum_mul]
    have e : ((univ.filter fun r : ∀ j, R j => β i (t i) (r i) = aᵢ).filter
        fun r => playAt β t r = a) = univ.filter fun r => playAt β t r = a := by
      ext r
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro hr
      rw [← ha, ← hr]
      rfl
    rw [e]
    exact sum_congr rfl fun r hr => by rw [(mem_filter.1 hr).2]
  · simp only [ha, ↓reduceIte]
    symm
    refine sum_eq_zero fun r hr => ?_
    simp only [mem_filter, mem_univ, true_and] at hr
    exact absurd (by rw [← hr.2, ← hr.1]; rfl) ha

/-- **BNE outcomes of expansions are BCE** (Bergemann–Morris 2016, Thm. 1, "if"). -/
theorem bneOutcome_isBCE {ψ : Θ → ℝ} (hψ : ∀ θ, 0 ≤ ψ θ) {π : Θ → (∀ i, T i) → ℝ}
    {π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ} (hexp : IsExpansion π π')
    {u : I → Θ → (∀ i, A i) → ℝ} {β : ∀ i, T i → R i → A i} (hβ : IsExpansionBNE ψ u π' β) :
    IsBCE ψ π u (bneOutcome ψ π' β) := by
  refine ⟨fun θ t a => sum_nonneg fun r _ => mul_nonneg (hψ θ) (hexp.1 θ t r),
    fun θ t => ?_, fun i tᵢ aᵢ aᵢ' => ?_⟩
  · simp only [bneOutcome]
    rw [sum_fiberwise (s := univ) (g := playAt β t), ← mul_sum, hexp.2]
  · set G : Θ → (∀ j, T j) → (∀ j, R j) → ℝ := fun θ t r =>
      ψ θ * π' θ t r * (u i θ (update (playAt β t r) i aᵢ') - u i θ (playAt β t r))
    -- Regroup by the extra signal `rᵢ`.
    have step : ∀ θ, ∀ t ∈ univ.filter (fun t : ∀ j, T j => t i = tᵢ),
        ∑ a ∈ univ.filter (fun a : ∀ j, A j => a i = aᵢ),
          bneOutcome ψ π' β θ t a * (u i θ (update a i aᵢ') - u i θ a) =
        ∑ rᵢ ∈ univ.filter (fun rᵢ => β i tᵢ rᵢ = aᵢ),
          ∑ r ∈ univ.filter (fun r : ∀ j, R j => r i = rᵢ), G θ t r := by
      intro θ t ht
      have hti : t i = tᵢ := (mem_filter.1 ht).2
      rw [sum_bneOutcome_mul ψ π' β θ t i aᵢ (fun a => u i θ (update a i aᵢ') - u i θ a)]
      rw [← sum_fiberwise_of_maps_to (g := fun r : ∀ j, R j => r i)
        (t := univ.filter fun rᵢ => β i tᵢ rᵢ = aᵢ) (fun r hr => by
          simp only [mem_filter, mem_univ, true_and] at hr ⊢
          rwa [← hti])]
      refine sum_congr rfl fun rᵢ hrᵢ => ?_
      have e : ((univ.filter fun r : ∀ j, R j => β i (t i) (r i) = aᵢ).filter
          fun r => r i = rᵢ) = univ.filter fun r : ∀ j, R j => r i = rᵢ := by
        ext r
        simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        intro hr
        rw [hr, hti]
        exact (mem_filter.1 hrᵢ).2
      rw [e]
    rw [sum_congr rfl fun θ _ => sum_congr rfl (step θ)]
    -- Swap the order of summation and apply the BNE inequality for each `rᵢ`.
    rw [sum_congr rfl fun θ _ => sum_comm, sum_comm]
    exact sum_nonpos fun rᵢ _ => hβ i tᵢ rᵢ aᵢ'

end Expansion

/-- The expansion used for the converse: the extra signal is the recommended action, drawn
from `ν θ t · / ψ θ`; at states of prior probability zero it is a fixed profile `a₀`. -/
noncomputable def obedientExpansion [∀ i, Nonempty (A i)] (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ν : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (θ : Θ) (t : ∀ i, T i) (a : ∀ i, A i) : ℝ :=
  if ψ θ = 0 then (if a = fun i => Classical.arbitrary (A i) then π θ t else 0)
  else ν θ t a / ψ θ

/-- **Every BCE is a BNE outcome of an expansion** (Bergemann–Morris 2016, Thm. 1, "only
if"): give each player her recommended action as an extra signal and let her obey. -/
theorem isBCE_bneOutcome [∀ i, Nonempty (A i)] {ψ : Θ → ℝ} (hψ : ∀ θ, 0 ≤ ψ θ)
    {π : Θ → (∀ i, T i) → ℝ} (hπ : ∀ θ t, 0 ≤ π θ t)
    {u : I → Θ → (∀ i, A i) → ℝ} {ν : Θ → (∀ i, T i) → (∀ i, A i) → ℝ}
    (hν : IsBCE ψ π u ν) :
    IsExpansion (R := A) π (obedientExpansion ψ π ν) ∧
      IsExpansionBNE (R := A) ψ u (obedientExpansion ψ π ν) (fun _ _ a => a) ∧
      bneOutcome (R := A) ψ (obedientExpansion ψ π ν) (fun _ _ a => a) = ν := by
  have hplay : ∀ (t : ∀ i, T i) (r : ∀ i, A i), playAt (R := A) (fun _ _ a => a) t r = r :=
    fun _ _ => rfl
  -- At a null state the BCE puts no mass.
  have hzero : ∀ θ, ψ θ = 0 → ∀ t a, ν θ t a = 0 := fun θ h0 t a => by
    have hs := hν.2.1 θ t
    rw [h0, zero_mul] at hs
    exact (sum_eq_zero_iff_of_nonneg fun a _ => hν.1 θ t a).1 hs a (mem_univ _)
  have hcancel : ∀ θ t a, ψ θ * obedientExpansion ψ π ν θ t a = ν θ t a := fun θ t a => by
    unfold obedientExpansion
    by_cases h0 : ψ θ = 0
    · rw [h0, zero_mul, hzero θ h0 t a]
    · simp only [h0, ↓reduceIte]
      exact mul_div_cancel₀ _ h0
  refine ⟨⟨fun θ t a => ?_, fun θ t => ?_⟩, fun i tᵢ rᵢ aᵢ' => ?_, ?_⟩
  · unfold obedientExpansion
    split_ifs
    · exact hπ θ t
    · exact le_rfl
    · exact div_nonneg (hν.1 θ t a) (hψ θ)
  · unfold obedientExpansion
    by_cases h0 : ψ θ = 0
    · simp only [h0, ↓reduceIte, sum_ite_eq', mem_univ]
    · simp only [h0, ↓reduceIte]
      rw [← sum_div, hν.2.1, mul_div_cancel_left₀ _ h0]
  · simp only [hplay, hcancel]
    exact hν.2.2 i tᵢ rᵢ aᵢ'
  · funext θ t a
    simp only [bneOutcome, hplay, hcancel, filter_eq', mem_univ, ↓reduceIte, sum_singleton]

/-- **Bergemann–Morris characterization**: `ν` is a BCE iff it is the outcome of a
pure-strategy Bayes Nash equilibrium of some expansion of the information structure (extra
signals in the same universe as actions). Mixed-strategy equilibria of expansions give no
further outcomes, since randomization can be put into the extra signals; that reduction is
not formalized here. -/
theorem isBCE_iff [∀ i, Nonempty (A i)] {ψ : Θ → ℝ} (hψ : ∀ θ, 0 ≤ ψ θ)
    {π : Θ → (∀ i, T i) → ℝ} (hπ : ∀ θ t, 0 ≤ π θ t)
    {u : I → Θ → (∀ i, A i) → ℝ} (ν : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) :
    IsBCE ψ π u ν ↔ ∃ (R : I → Type uA) (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i))
      (π' : Θ → (∀ i, T i) → (∀ i, R i) → ℝ) (β : ∀ i, T i → R i → A i),
      IsExpansion π π' ∧ IsExpansionBNE ψ u π' β ∧ bneOutcome ψ π' β = ν := by
  constructor
  · intro h
    exact ⟨A, inferInstance, inferInstance, _, _, isBCE_bneOutcome hψ hπ h⟩
  · rintro ⟨R, _, _, π', β, hexp, hβ, rfl⟩
    exact bneOutcome_isBCE hψ hexp hβ

end Econ
