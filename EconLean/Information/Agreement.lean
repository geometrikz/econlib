/-
# Agreeing to disagree (Aumann 1976)

A finite state space `Ω` carries a common prior `μ` with full support. Agent `k` learns the
cell of her information partition, encoded by a labelling `c k : Ω → L` (states with the same
label are indistinguishable to her). Her posterior of an event `E` at `ω` is
`μ(E ∩ P_k(ω)) / μ(P_k(ω))`.

An event is **common knowledge** at `ω₀` if it contains a set `C ∋ ω₀` that is
**self-evident** for every agent, i.e. a union of cells of each partition (equivalently, the
event contains the cell of `ω₀` in the meet of the partitions; Aumann 1976; Osborne–Rubinstein
1994, Prop. 74.2 and Def. 73.2).

* `aumann_agreement`: if it is common knowledge at `ω₀` that agent `1`'s posterior of `E` is
  `a` and agent `2`'s is `b`, then `a = b`.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Econ

open Finset

variable {Ω L : Type*} [Fintype Ω] [DecidableEq L]

/-- The cell of `ω` in the partition given by the labelling `c`. -/
def infoCell (c : Ω → L) (ω : Ω) : Finset Ω := univ.filter fun ω' => c ω' = c ω

/-- Probability of a finite event under the weights `μ`. -/
def probOf (μ : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ ω ∈ A, μ ω

/-- The posterior probability of `E` at `ω` for the agent with partition `c`. -/
noncomputable def posterior [DecidableEq Ω] (μ : Ω → ℝ) (c : Ω → L) (E : Finset Ω) (ω : Ω) :
    ℝ :=
  probOf μ (E ∩ infoCell c ω) / probOf μ (infoCell c ω)

/-- `C` is **self-evident** for the partition `c`: it is a union of cells. -/
def IsSelfEvident (c : Ω → L) (C : Finset Ω) : Prop :=
  ∀ ω ∈ C, ∀ ω', c ω' = c ω → ω' ∈ C

/-- On a self-evident set where the posterior is constant `a`, the probability of `E ∩ C` is
`a μ(C)`: sum the defining equation of the posterior over the cells making up `C`. -/
lemma probOf_inter_of_selfEvident [DecidableEq Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 < μ ω) {c : Ω → L}
    {E C : Finset Ω} (hC : IsSelfEvident c C) {a : ℝ}
    (ha : ∀ ω ∈ C, posterior μ c E ω = a) : probOf μ (E ∩ C) = a * probOf μ C := by
  -- Each cell inside `C`.
  have hcell : ∀ ω ∈ C, C.filter (fun ω' => c ω' = c ω) = infoCell c ω := fun ω hω => by
    ext ω'
    simp only [mem_filter, infoCell, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hC ω hω ω' h, h⟩⟩
  have hpos : ∀ ω, 0 < probOf μ (infoCell c ω) := fun ω =>
    sum_pos (fun ω' _ => hμ ω') ⟨ω, by simp [infoCell]⟩
  -- Fibre both sums over the labels of the cells in `C`.
  have key : ∀ g : Ω → ℝ, ∑ ω ∈ C, g ω =
      ∑ l ∈ C.image c, ∑ ω ∈ C.filter (fun ω' => c ω' = l), g ω := fun g =>
    (sum_fiberwise_of_maps_to (fun ω hω => mem_image_of_mem c hω) g).symm
  have hE : probOf μ (E ∩ C) = ∑ ω ∈ C, if ω ∈ E then μ ω else 0 := by
    rw [probOf, ← sum_filter]
    congr 1
    ext ω; simp [and_comm]
  rw [hE, probOf, key, key, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  obtain ⟨ω, hω, rfl⟩ := mem_image.1 hl
  rw [hcell ω hω]
  have h := ha ω hω
  rw [posterior, div_eq_iff (hpos ω).ne'] at h
  simp only [probOf] at h
  rw [← h, ← sum_filter]
  congr 1
  ext ω'; simp [infoCell, and_comm]

/-- **Aumann's agreement theorem** (1976). Under a common prior with full support, if at
`ω₀` it is common knowledge that agent `1`'s posterior of `E` is `a` and agent `2`'s is `b`,
then `a = b`. -/
theorem aumann_agreement [DecidableEq Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 < μ ω) {c₁ c₂ : Ω → L}
    {E : Finset Ω} {a b : ℝ} {ω₀ : Ω} {C : Finset Ω} (hω₀ : ω₀ ∈ C)
    (hC₁ : IsSelfEvident c₁ C) (hC₂ : IsSelfEvident c₂ C)
    (ha : ∀ ω ∈ C, posterior μ c₁ E ω = a) (hb : ∀ ω ∈ C, posterior μ c₂ E ω = b) :
    a = b := by
  have h₁ := probOf_inter_of_selfEvident hμ hC₁ ha
  have h₂ := probOf_inter_of_selfEvident hμ hC₂ hb
  have hpos : 0 < probOf μ C := sum_pos (fun ω _ => hμ ω) ⟨ω₀, hω₀⟩
  exact mul_right_cancel₀ hpos.ne' (h₁.symm.trans h₂)

/-- Witness that the theorem has content: with *different* (non-common-knowledge)
information, posteriors can differ. Two equally likely states; agent `1` learns the state,
agent `2` learns nothing; at state `0` the posteriors of `{0}` are `1` and `1/2`. The only set
self-evident for agent `2` is the whole space, on which agent `1`'s posterior is not
constant. -/
example : posterior (fun _ : Fin 2 => (1 : ℝ)) (fun ω => ω) {0} 0 = 1 ∧
    posterior (fun _ : Fin 2 => (1 : ℝ)) (fun _ => (0 : Fin 1)) {0} 0 = 1 / 2 := by
  constructor
  · simp [posterior, probOf, infoCell, filter_eq']
  · simp [posterior, probOf, infoCell]

end Econ
