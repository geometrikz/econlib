/-
# Level-k thinking and cognitive hierarchy

References.
* R. Nagel (1995), "Unraveling in Guessing Games: An Experimental Study",
  *AER* 85(5): the p-beauty contest and level-k reasoning.
* D. Stahl and P. Wilson (1995), *GEB* 10; M. Costa-Gomes, V. Crawford and
  B. Broseta (2001), *Econometrica* 69: level-k types.
* C. Camerer, T.-H. Ho and J.-K. Chong (2004), "A Cognitive Hierarchy Model
  of Games", *QJE* 119(3).

**Level-k in a finite game.** Players `i : I` have finite action sets `A i`
and payoffs `u i`. Level-0 plays an exogenous *pure* profile (an anchor; the
literature usually takes level-0 to randomize uniformly, which in the
beauty contest below is summarized by its mean `50`); ties among best
responses are broken arbitrarily; a
level-`(k+1)` player best-responds to the belief that everyone else is
level-`k`. We record a whole hierarchy as a path `L : ℕ → profiles` with
`L (k+1) i` a best response of `i` to `L k`.
* `exists_levelKPath`: from any level-0 profile a hierarchy exists;
* `isPureNash_of_levelK_fixed`: if the hierarchy stops moving, it has
  reached a pure Nash equilibrium;
* `levelK_eq_of_strictNash`: if level-0 is a strict Nash equilibrium, every
  level plays it.

**The p-beauty contest (Nagel 1995).** Everyone guesses in `[0, 100]`; the
guess closest to `p` times the average wins (`0 < p < 1`). With many players
(one's own guess has negligible effect on the average), the best response to
a belief that others guess `x` is `p x`. **This large-population
approximation is a modelling step, not a theorem here**: the finite-player
beauty contest game itself (and the uniqueness of its all-zero equilibrium) is
not formalized. Level-0 guesses uniformly, mean
`50`, so level-`k` guesses `50 pᵏ` (`levelK_guess`), which falls to the
unique equilibrium guess `0` as `k → ∞` (`levelK_guess_tendsto`).

**Cognitive hierarchy (CHC 2004).** Level-`k` best-responds to a mixture of
*all* lower levels with weights proportional to a positive frequency `f j`
(Poisson in CHC, any positive weights here). In the beauty contest its guess
is `p` times the `f`-weighted mean of lower-level guesses. CH guesses are
positive and strictly decreasing in the level (`chGuess_strictAnti`).
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

namespace BoundedRationality

open Finset Filter Topology

/-- A finite normal-form game: players `I`, action sets `A i`, payoffs `u i`
on pure profiles. -/
structure FiniteGame (I : Type*) where
  /-- actions of player `i` -/
  A : I → Type
  /-- finitely many actions -/
  fintype : ∀ i, Fintype (A i)
  /-- actions can be compared -/
  decEq : ∀ i, DecidableEq (A i)
  /-- payoff of player `i` at a pure profile -/
  u : I → (∀ i, A i) → ℝ

attribute [instance] FiniteGame.fintype FiniteGame.decEq

variable {I : Type*} [DecidableEq I] (G : FiniteGame I)

/-- `b` is a best response of player `i` when the others play as in `a`. -/
def BestResponse (i : I) (a : ∀ i, G.A i) (b : G.A i) : Prop :=
  ∀ b', G.u i (Function.update a i b') ≤ G.u i (Function.update a i b)

/-- A pure-strategy Nash equilibrium. -/
def IsPureNash (a : ∀ i, G.A i) : Prop := ∀ i, BestResponse G i a (a i)

/-- A strict pure Nash equilibrium: every unilateral deviation strictly
loses. -/
def IsStrictNash (a : ∀ i, G.A i) : Prop :=
  ∀ i b, b ≠ a i → G.u i (Function.update a i b) < G.u i a

/-- A level-k hierarchy: level `k+1` best-responds to level `k`. -/
def IsLevelKPath (L : ℕ → ∀ i, G.A i) : Prop := ∀ k i, BestResponse G i (L k) (L (k + 1) i)

/-- Best responses exist when action sets are finite and nonempty. -/
theorem exists_bestResponse [∀ i, Nonempty (G.A i)] (i : I) (a : ∀ i, G.A i) :
    ∃ b, BestResponse G i a b := by
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image (univ : Finset (G.A i))
    (fun b => G.u i (Function.update a i b)) univ_nonempty
  exact ⟨b, fun b' => hb b' (mem_univ _)⟩

/-- **Existence of the hierarchy** from any level-0 profile. -/
theorem exists_levelKPath [∀ i, Nonempty (G.A i)] (a₀ : ∀ i, G.A i) :
    ∃ L, L 0 = a₀ ∧ IsLevelKPath G L := by
  classical
  choose br hbr using fun (a : ∀ i, G.A i) (i : I) => exists_bestResponse G i a
  let L : ℕ → ∀ i, G.A i := fun k => Nat.rec a₀ (fun _ a i => br a i) k
  exact ⟨L, rfl, fun k i => hbr (L k) i⟩

/-- **A level-k hierarchy that stops moving is at a pure Nash equilibrium.** -/
theorem isPureNash_of_levelK_fixed {L : ℕ → ∀ i, G.A i} (hL : IsLevelKPath G L) {k : ℕ}
    (hfix : L (k + 1) = L k) : IsPureNash G (L k) := by
  intro i b'
  have := hL k i b'
  rw [hfix, Function.update_eq_self] at this
  rwa [Function.update_eq_self]

/-- **If level-0 plays a strict Nash equilibrium, so does every level.** -/
theorem levelK_eq_of_strictNash {L : ℕ → ∀ i, G.A i} (hL : IsLevelKPath G L)
    (hstrict : IsStrictNash G (L 0)) (k : ℕ) : L k = L 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    by_contra hne
    have hbr := hL k i (L 0 i)
    rw [ih, Function.update_eq_self] at hbr
    have := hstrict i (L (k + 1) i) hne
    linarith

/-! ### The p-beauty contest -/

/-- Level-k guess in the p-beauty contest: level-0 averages `50`, each level
best-responds with `p` times the guess it expects. -/
noncomputable def levelKGuess (p : ℝ) : ℕ → ℝ
  | 0 => 50
  | k + 1 => p * levelKGuess p k

theorem levelK_guess (p : ℝ) (k : ℕ) : levelKGuess p k = 50 * p ^ k := by
  induction k with
  | zero => simp [levelKGuess]
  | succ k ih => rw [levelKGuess, ih, pow_succ]; ring

/-- Algebraic lemma: `0` is the only fixed point of the large-population best
response map `x ↦ p x` (`p ≠ 1`). This is *not* a proof that all-zero is the
unique Nash equilibrium of the finite beauty-contest game. -/
theorem beauty_fixed_iff {p : ℝ} (hp : p ≠ 1) (x : ℝ) : p * x = x ↔ x = 0 := by
  constructor
  · intro h
    have : (p - 1) * x = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (by linarith : p = 1) hp
    · exact h1
  · rintro rfl; simp

/-- **Level-k guesses unravel to the equilibrium**: `50 pᵏ → 0`. -/
theorem levelK_guess_tendsto {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) :
    Tendsto (levelKGuess p) atTop (𝓝 0) := by
  simp_rw [funext (levelK_guess p)]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul 50

/-- Cognitive-hierarchy guesses: level `0` guesses `50`; level `k+1` guesses
`p` times the `f`-weighted average of levels `0..k`. -/
noncomputable def chGuess (p : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 50
  | k + 1 => p * (∑ j : Fin (k + 1), f j * chGuess p f j) / ∑ j ∈ range (k + 1), f j

/-- The `f`-weighted average of the guesses of levels `0..k`. -/
noncomputable def chAvg (p : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ j ∈ range (k + 1), f j * chGuess p f j) / ∑ j ∈ range (k + 1), f j

theorem chGuess_succ (p : ℝ) (f : ℕ → ℝ) (k : ℕ) : chGuess p f (k + 1) = p * chAvg p f k := by
  rw [chGuess, chAvg, Fin.sum_univ_eq_sum_range (fun j => f j * chGuess p f j)]
  ring

theorem chGuess_pos {p : ℝ} (hp : 0 < p) {f : ℕ → ℝ} (hf : ∀ j, 0 < f j) (k : ℕ) :
    0 < chGuess p f k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp [chGuess]
    | succ k =>
      rw [chGuess_succ, chAvg]
      apply mul_pos hp
      apply div_pos
      · exact sum_pos (fun j hj => mul_pos (hf j) (ih j (by simpa [Nat.lt_succ_iff] using hj)))
          ⟨0, by simp⟩
      · exact sum_pos (fun j _ => hf j) ⟨0, by simp⟩

/-- The weighted average of guesses falls strictly as a level is added. -/
theorem chAvg_succ_lt {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {f : ℕ → ℝ} (hf : ∀ j, 0 < f j)
    (k : ℕ) : chAvg p f (k + 1) < chAvg p f k := by
  set N := ∑ j ∈ range (k + 1), f j * chGuess p f j with hN
  set S := ∑ j ∈ range (k + 1), f j with hS
  have hSpos : 0 < S := sum_pos (fun j _ => hf j) ⟨0, by simp⟩
  have hNpos : 0 < N := sum_pos (fun j _ => mul_pos (hf j) (chGuess_pos hp0 hf j))
    ⟨0, by simp⟩
  have hnext : chGuess p f (k + 1) = p * (N / S) := by rw [chGuess_succ, chAvg]
  unfold chAvg
  rw [sum_range_succ (fun j => f j * chGuess p f j) (k + 1), sum_range_succ f (k + 1), ← hN, ← hS,
    hnext]
  have hfk := hf (k + 1)
  rw [div_lt_div_iff₀ (by linarith) hSpos]
  -- `(N + f·p·N/S)·S < N·(S + f)` ⟺ `p < 1`
  have e : (N + f (k + 1) * (p * (N / S))) * S = N * S + f (k + 1) * p * N := by
    field_simp
  rw [e]
  nlinarith [mul_pos hfk hNpos]

/-- **CH guesses fall strictly with the level** (for `0 < p < 1` and any
positive level frequencies, e.g. Poisson). -/
theorem chGuess_strictAnti {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {f : ℕ → ℝ}
    (hf : ∀ j, 0 < f j) : StrictAnti (chGuess p f) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  cases k with
  | zero =>
    rw [chGuess_succ, chAvg]
    simp [chGuess]
    have := hf 0
    field_simp
    nlinarith
  | succ k =>
    rw [chGuess_succ, chGuess_succ]
    exact mul_lt_mul_of_pos_left (chAvg_succ_lt hp0 hp1 hf k) hp0

end BoundedRationality

end Econ
