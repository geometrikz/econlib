/-
# Ambiguity aversion: the Ellsberg paradox and maxmin expected utility

References.
* D. Ellsberg (1961), "Risk, Ambiguity, and the Savage Axioms", *QJE* 75(4):
  the three-color urn.
* I. Gilboa and D. Schmeidler (1989), "Maxmin Expected Utility with
  Non-Unique Prior", *J. Math. Econ.* 18(2).

**The setting.** Finitely many states `s : S`. An *act* is described by the
utility it yields in each state, `f : S → ℝ` (Anscombe–Aumann acts after
applying the vN–M utility). A maxmin agent has a nonempty finite set `C` of
priors and evaluates

    V(f) = min_{π ∈ C} Σ_s π(s) f(s).

(Using a finite set of priors loses nothing for evaluating acts: the minimum
of a linear function over a compact convex set is attained at an extreme
point, and the examples need only finitely many.)

**Results.**
* `ellsberg_not_seu`: the modal Ellsberg choices (bet on red over black, and
  on "black or yellow" over "red or yellow") cannot be explained by *any*
  single prior with expected utility, indeed by any additive weights at all;
* `ellsberg_meu`: maxmin EU with the priors `(1/3, b, 2/3 − b)`, `b ∈ {0, 2/3}`
  rationalizes both choices;
* `meu_le_eu`: the maxmin value is below the expected utility under every
  prior in `C`;
* `meu_mix_ge` (**uncertainty aversion**, GS axiom): mixing acts never lowers
  the value below the mixture of the values (`V` is concave);
* `meu_mix_const` (**certainty independence**, GS axiom): mixing with a
  constant act shifts the value linearly;
* `meu_mono` (monotonicity).

The *sufficiency* half of the Gilboa–Schmeidler representation theorem
(axioms ⟹ maxmin form, via a separating-hyperplane argument) is not
formalized here.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Econ

namespace Ambiguity

open Finset

variable {S : Type*} [Fintype S]

/-- Expected utility of act `f` under prior `π`. -/
def eu (π f : S → ℝ) : ℝ := ∑ s, π s * f s

/-- Maxmin expected utility over a nonempty finite set of priors. -/
noncomputable def meu (C : Finset (S → ℝ)) (hC : C.Nonempty) (f : S → ℝ) : ℝ :=
  C.inf' hC fun π => eu π f

theorem meu_le_eu (C : Finset (S → ℝ)) (hC : C.Nonempty) (f : S → ℝ) {π : S → ℝ} (hπ : π ∈ C) :
    meu C hC f ≤ eu π f :=
  Finset.inf'_le _ hπ

/-- The maxmin value is attained by some prior in `C`. -/
theorem exists_eq_meu (C : Finset (S → ℝ)) (hC : C.Nonempty) (f : S → ℝ) :
    ∃ π ∈ C, eu π f = meu C hC f := by
  obtain ⟨π, hπ, h⟩ := Finset.exists_mem_eq_inf' hC (fun π => eu π f)
  exact ⟨π, hπ, h.symm⟩

/-- Monotonicity: a statewise better act is weakly preferred (priors are
nonnegative). -/
theorem meu_mono (C : Finset (S → ℝ)) (hC : C.Nonempty) (hnn : ∀ π ∈ C, ∀ s, 0 ≤ π s)
    {f g : S → ℝ} (h : ∀ s, f s ≤ g s) : meu C hC f ≤ meu C hC g := by
  apply Finset.le_inf'
  intro π hπ
  refine (meu_le_eu C hC f hπ).trans ?_
  exact sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hnn π hπ s)

/-- **Uncertainty aversion** (Gilboa–Schmeidler's axiom): for `α ∈ [0,1]`,
`V(α f + (1−α) g) ≥ α V(f) + (1−α) V(g)`. -/
theorem meu_mix_ge (C : Finset (S → ℝ)) (hC : C.Nonempty) (f g : S → ℝ) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    α * meu C hC f + (1 - α) * meu C hC g ≤ meu C hC (fun s => α * f s + (1 - α) * g s) := by
  apply Finset.le_inf'
  intro π hπ
  have e : eu π (fun s => α * f s + (1 - α) * g s) = α * eu π f + (1 - α) * eu π g := by
    simp only [eu, mul_add, sum_add_distrib, mul_sum]
    congr 1 <;> exact sum_congr rfl fun s _ => by ring
  rw [e]
  have := meu_le_eu C hC f hπ
  have := meu_le_eu C hC g hπ
  nlinarith

/-- **Certainty independence** (Gilboa–Schmeidler's axiom): mixing with a
constant act `c` (utility `c` in every state) is linear, when every prior
sums to one. -/
theorem meu_mix_const (C : Finset (S → ℝ)) (hC : C.Nonempty) (hsum : ∀ π ∈ C, ∑ s, π s = 1)
    (f : S → ℝ) (α c : ℝ) (h0 : 0 ≤ α) :
    meu C hC (fun s => α * f s + (1 - α) * c) = α * meu C hC f + (1 - α) * c := by
  have e : ∀ π ∈ C, eu π (fun s => α * f s + (1 - α) * c) = α * eu π f + (1 - α) * c := by
    intro π hπ
    simp only [eu, mul_add, sum_add_distrib, mul_sum]
    rw [← sum_mul, hsum π hπ, one_mul]
    congr 1
    exact sum_congr rfl fun s _ => by ring
  apply le_antisymm
  · obtain ⟨π, hπ, hmin⟩ := exists_eq_meu C hC f
    calc meu C hC (fun s => α * f s + (1 - α) * c)
        ≤ eu π (fun s => α * f s + (1 - α) * c) := meu_le_eu C hC _ hπ
      _ = α * meu C hC f + (1 - α) * c := by rw [e π hπ, hmin]
  · apply Finset.le_inf'
    intro π hπ
    rw [e π hπ]
    have := meu_le_eu C hC f hπ
    nlinarith

/-! ### The Ellsberg three-color urn

30 red balls and 60 balls that are black or yellow in unknown proportion.
States `0 = red`, `1 = black`, `2 = yellow`. Bets pay utility `1` if they win
and `0` otherwise. -/

/-- Bet on red. -/
def betR : Fin 3 → ℝ := ![1, 0, 0]
/-- Bet on black. -/
def betB : Fin 3 → ℝ := ![0, 1, 0]
/-- Bet on red or yellow. -/
def betRY : Fin 3 → ℝ := ![1, 0, 1]
/-- Bet on black or yellow. -/
def betBY : Fin 3 → ℝ := ![0, 1, 1]

/-- **The Ellsberg paradox.** No assignment of weights `π` to the three colors
(probabilities or not) makes expected utility rank `betR` strictly above
`betB` *and* `betBY` strictly above `betRY`: the first says `π red > π black`,
the second `π black > π red`. So the modal choices violate subjective
expected utility (Savage's sure-thing principle). -/
theorem ellsberg_not_seu : ¬ ∃ π : Fin 3 → ℝ,
    eu π betB < eu π betR ∧ eu π betRY < eu π betBY := by
  rintro ⟨π, h1, h2⟩
  simp [eu, Fin.sum_univ_three, betR, betB, betRY, betBY] at h1 h2
  linarith

/-- The two extreme priors consistent with the urn: red has probability
`1/3`, black between `0` and `2/3`. -/
noncomputable def ellsbergPriors : Finset (Fin 3 → ℝ) := {![1/3, 0, 2/3], ![1/3, 2/3, 0]}

theorem ellsbergPriors_nonempty : ellsbergPriors.Nonempty := by
  simp [ellsbergPriors]

/-- **Maxmin EU rationalizes Ellsberg.** With these priors,
`V(betR) = 1/3 > 0 = V(betB)` and `V(betBY) = 2/3 > 1/3 = V(betRY)`. -/
theorem ellsberg_meu :
    meu ellsbergPriors ellsbergPriors_nonempty betB <
      meu ellsbergPriors ellsbergPriors_nonempty betR ∧
    meu ellsbergPriors ellsbergPriors_nonempty betRY <
      meu ellsbergPriors ellsbergPriors_nonempty betBY := by
  simp [meu, ellsbergPriors, eu, Fin.sum_univ_three, betR, betB, betRY, betBY]
  norm_num

end Ambiguity

end Econ
