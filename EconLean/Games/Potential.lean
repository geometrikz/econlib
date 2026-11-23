/-
# Potential games (Monderer–Shapley 1996; Rosenthal 1973)

A strategic-form game `u` has an **exact potential** `Φ` if every unilateral deviation changes
the deviator's payoff by exactly the change in `Φ`, and an **ordinal potential** if it changes
in the same direction (Monderer and Shapley 1996, §2).

Main results:
* `isNash_of_isMaxOn_potential`: a maximizer of an ordinal potential is a pure Nash
  equilibrium.
* `exists_isNash_of_potential`: every finite game with an ordinal potential has a pure Nash
  equilibrium.
* `not_infinite_improvementPath`: the **finite improvement property**: in a finite game with
  an ordinal potential every sequence of strict unilateral improvements is finite.
* `congestion_isExactPotential` (Rosenthal 1973): a congestion game, where each player picks a
  set of resources and pays on each the cost `c r k` at its load `k`, has the exact potential
  `∑_r ∑_{k ≤ n_r} c r k` (`rosenthal`); hence congestion games have pure equilibria.
-/
module

public import EconLean.Games.Strategic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

open Function Finset

variable {I : Type*} [DecidableEq I] {S : I → Type*}

/-- `Φ` is an **exact potential** for `u` (Monderer–Shapley 1996). -/
def IsExactPotential (u : I → (∀ j, S j) → ℝ) (Φ : (∀ j, S j) → ℝ) : Prop :=
  ∀ i (s : ∀ j, S j) (t : S i), u i (update s i t) - u i s = Φ (update s i t) - Φ s

/-- `Φ` is an **ordinal potential** for `u`: a unilateral deviation raises the deviator's
payoff exactly when it raises `Φ`. -/
def IsOrdinalPotential (u : I → (∀ j, S j) → ℝ) (Φ : (∀ j, S j) → ℝ) : Prop :=
  ∀ i (s : ∀ j, S j) (t : S i), u i s < u i (update s i t) ↔ Φ s < Φ (update s i t)

theorem IsExactPotential.isOrdinalPotential {u : I → (∀ j, S j) → ℝ} {Φ : (∀ j, S j) → ℝ}
    (h : IsExactPotential u Φ) : IsOrdinalPotential u Φ := fun i s t => by
  have := h i s t
  constructor <;> intro h' <;> linarith

/-- A maximizer of an ordinal potential is a pure Nash equilibrium. -/
theorem isNash_of_isMaxOn_potential {u : I → (∀ j, S j) → ℝ} {Φ : (∀ j, S j) → ℝ}
    (hΦ : IsOrdinalPotential u Φ) {s : ∀ j, S j} (hs : ∀ s', Φ s' ≤ Φ s) : IsNash u s :=
  fun i t => not_lt.1 fun h => not_lt.2 (hs _) ((hΦ i s t).1 h)

/-- **Existence of pure equilibria in finite potential games.** -/
theorem exists_isNash_of_potential [Fintype I] [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {u : I → (∀ j, S j) → ℝ} {Φ : (∀ j, S j) → ℝ} (hΦ : IsOrdinalPotential u Φ) :
    ∃ s, IsNash u s := by
  obtain ⟨s, -, hs⟩ := exists_max_image (univ : Finset (∀ j, S j)) Φ univ_nonempty
  exact ⟨s, isNash_of_isMaxOn_potential hΦ fun s' => hs s' (mem_univ _)⟩

/-- An **improvement path**: each step is a strict unilateral improvement by some player. -/
def IsImprovementPath (u : I → (∀ j, S j) → ℝ) (f : ℕ → ∀ j, S j) : Prop :=
  ∀ n, ∃ i, ∃ t : S i, f (n + 1) = update (f n) i t ∧ u i (f n) < u i (f (n + 1))

/-- **Finite improvement property** (Monderer–Shapley 1996, Lemma 2.3): a finite game with an
ordinal potential has no infinite improvement path. -/
theorem not_infinite_improvementPath [Fintype I] [∀ i, Fintype (S i)]
    {u : I → (∀ j, S j) → ℝ} {Φ : (∀ j, S j) → ℝ} (hΦ : IsOrdinalPotential u Φ)
    (f : ℕ → ∀ j, S j) : ¬ IsImprovementPath u f := by
  intro hf
  have hmono : StrictMono (Φ ∘ f) := strictMono_nat_of_lt_succ fun n => by
    obtain ⟨i, t, he, hlt⟩ := hf n
    rw [he] at hlt
    simp only [Function.comp_apply, he]
    exact (hΦ i (f n) t).1 hlt
  exact not_injective_infinite_finite (f) (hmono.injective.of_comp)

/-! ### Congestion games -/

section Congestion

variable {R : Type*} [Fintype R] [DecidableEq R] [Fintype I]

/-- The load on resource `r` when the players choose the resource sets `s`. -/
def load (s : I → Finset R) (r : R) : ℕ := (univ.filter fun i => r ∈ s i).card

/-- Payoff in a **congestion game**: minus the sum over the chosen resources of the cost
`c r k` at the resource's load `k`. -/
def congestionPayoff (c : R → ℕ → ℝ) (i : I) (s : I → Finset R) : ℝ :=
  -∑ r ∈ s i, c r (load s r)

/-- **Rosenthal's potential** `−∑_r ∑_{k=1}^{n_r} c r k`. -/
def rosenthal (c : R → ℕ → ℝ) (s : I → Finset R) : ℝ :=
  -∑ r, ∑ k ∈ range (load s r), c r (k + 1)

omit [Fintype R] in
lemma load_update_of_mem_of_mem {s : I → Finset R} {i : I} {T : Finset R} {r : R}
    (h₁ : r ∈ s i) (h₂ : r ∈ T) : load (update s i T) r = load s r := by
  unfold load
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp [h₁, h₂]
  · simp [update_of_ne hj]

omit [Fintype R] in
lemma load_update_of_not_mem_of_not_mem {s : I → Finset R} {i : I} {T : Finset R} {r : R}
    (h₁ : r ∉ s i) (h₂ : r ∉ T) : load (update s i T) r = load s r := by
  unfold load
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp [h₁, h₂]
  · simp [update_of_ne hj]

omit [Fintype R] in
/-- Joining a resource raises its load by one. -/
lemma load_update_of_not_mem_of_mem {s : I → Finset R} {i : I} {T : Finset R} {r : R}
    (h₁ : r ∉ s i) (h₂ : r ∈ T) : load (update s i T) r = load s r + 1 := by
  unfold load
  have : (univ.filter fun j => r ∈ update s i T j) =
      insert i (univ.filter fun j => r ∈ s j) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [h₂]
    · simp [hj]
  rw [this, card_insert_of_notMem (by simp [h₁])]

omit [Fintype R] in
/-- Leaving a resource lowers its load by one. -/
lemma load_update_of_mem_of_not_mem {s : I → Finset R} {i : I} {T : Finset R} {r : R}
    (h₁ : r ∈ s i) (h₂ : r ∉ T) : load (update s i T) r + 1 = load s r := by
  have := load_update_of_not_mem_of_mem (s := update s i T) (i := i) (T := s i) (r := r)
    (by simp [h₂]) h₁
  rw [update_idem, update_eq_self] at this
  exact this.symm

/-- **Rosenthal's theorem** (1973): congestion games are exact potential games. -/
theorem congestion_isExactPotential (c : R → ℕ → ℝ) :
    IsExactPotential (S := fun _ : I => Finset R) (congestionPayoff c) (rosenthal c) := by
  intro i s T
  set s' := update s i T
  -- Both sides are sums over resources of a per-resource change.
  have hu : congestionPayoff c i s' - congestionPayoff c i s =
      ∑ r, ((if r ∈ s i then c r (load s r) else 0) -
        (if r ∈ T then c r (load s' r) else 0)) := by
    simp only [congestionPayoff, s', update_self, sum_sub_distrib, ← sum_filter]
    simp only [filter_mem_eq_inter, univ_inter]
    ring
  have hΦ : rosenthal c s' - rosenthal c s =
      ∑ r, (∑ k ∈ range (load s r), c r (k + 1) - ∑ k ∈ range (load s' r), c r (k + 1)) := by
    simp only [rosenthal, sum_sub_distrib]
    ring
  rw [hu, hΦ]
  refine sum_congr rfl fun r _ => ?_
  by_cases h₁ : r ∈ s i <;> by_cases h₂ : r ∈ T <;> simp only [h₁, h₂, ↓reduceIte]
  · rw [load_update_of_mem_of_mem h₁ h₂]; ring
  · rw [← load_update_of_mem_of_not_mem h₁ h₂, sum_range_succ]; ring
  · rw [load_update_of_not_mem_of_mem h₁ h₂, sum_range_succ]; ring
  · rw [load_update_of_not_mem_of_not_mem h₁ h₂]; ring

/-- **Congestion games have pure Nash equilibria** (Rosenthal 1973), when every player has a
nonempty finite set of feasible resource sets. -/
theorem congestion_exists_isNash (c : R → ℕ → ℝ) (A : I → Finset (Finset R))
    (hA : ∀ i, (A i).Nonempty) :
    ∃ s : ∀ i, A i, ∀ i (t : A i),
      congestionPayoff c i (update (fun j => (s j : Finset R)) i t) ≤
        congestionPayoff c i (fun j => (s j : Finset R)) := by
  have : ∀ i, Nonempty (A i) := fun i => (hA i).to_subtype
  have hpot := (congestion_isExactPotential (I := I) c).isOrdinalPotential
  -- Restrict the potential to feasible profiles.
  set v : I → (∀ j, A j) → ℝ := fun i s => congestionPayoff c i (fun j => (s j : Finset R))
  have hv : IsOrdinalPotential v (fun s => rosenthal c fun j => (s j : Finset R)) := by
    intro i s t
    have e : (fun j => ((update s i t j : A j) : Finset R)) =
        update (fun j => (s j : Finset R)) i (t : Finset R) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [update_of_ne hj]
    simp only [v, e]
    exact hpot i _ _
  obtain ⟨s, hs⟩ := exists_isNash_of_potential hv
  refine ⟨s, fun i t => ?_⟩
  have := hs i t
  have e : (fun j => ((update s i t j : A j) : Finset R)) =
      update (fun j => (s j : Finset R)) i (t : Finset R) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  simpa only [v, e] using this

end Congestion

/-- Witness: in a pure coordination game (both players get `1` if they match and `0`
otherwise) the common payoff is an exact potential. -/
example : IsExactPotential (S := fun _ : Bool => Bool)
    (fun _ s => if s true = s false then (1 : ℝ) else 0)
    (fun s => if s true = s false then (1 : ℝ) else 0) := by
  intro i s t
  rfl

end Econ
