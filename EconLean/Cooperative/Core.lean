/-
# The core of a TU game and the Bondareva–Shapley theorem

Bondareva (1963), Shapley (1967); MWG §18.AA; Osborne–Rubinstein, *A Course in Game
Theory*, §13.1; Peleg–Sudhölter, Ch. 3.

The **core** of a TU game `v` is the set of payoff vectors `x` that distribute exactly
`v N` and give every coalition at least its worth: `∑ᵢ xᵢ = v N` and `∑_{i ∈ S} xᵢ ≥ v S`
for every `S`.

A family of weights `λ_S ≥ 0` on coalitions is **balanced** if every player's coalitions
carry total weight one: `∑_{S ∋ i} λ_S = 1` for each `i`. The game is **balanced** if
`∑_S λ_S v S ≤ v N` for every balanced family: no "part-time" allocation of the players'
time among coalitions produces more than the grand coalition.

* `isBalanced_of_mem_core`: a game with a nonempty core is balanced (one line of algebra).
* `bondareva_shapley`: the core is nonempty **iff** the game is balanced.

The converse direction is usually proved by linear-programming duality. Here it follows
from von Neumann's minimax theorem (`exists_saddle`): after adding a large additive game
(which shifts the core and preserves balancedness) all singletons have positive worth;
then in the zero-sum game where one player picks a coalition `S`, the other a player `i`,
with payoff `v S / v N − [i ∈ S]`, the minimizer's optimal mixed strategy, scaled by
`v N`, is a core allocation, and a positive value would yield a balanced family violating
balancedness.

The empty coalition is allowed in both definitions. For games with `v ∅ = 0` this changes
nothing; in general both sides of the theorem require `v ∅ ≤ 0`.
-/
module

public import EconLean.Cooperative.Shapley
public import EconLean.Games.ZeroSum

@[expose] public section

namespace Econ

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `x` is in the **core** of `v`. -/
def IsInCore (v : TUGame N) (x : N → ℝ) : Prop :=
  ∑ i, x i = v univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i

/-- `w` is a **balanced family** of coalition weights. -/
def IsBalancedFamily (w : Finset N → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧ ∀ i, ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), w S = 1

/-- `v` is **balanced**. -/
def IsBalanced (v : TUGame N) : Prop :=
  ∀ w, IsBalancedFamily w → ∑ S, w S * v S ≤ v univ

/-- Exchanging the order of summation over coalitions and their members. -/
lemma sum_weight_mul_sum (w : Finset N → ℝ) (x : N → ℝ) :
    ∑ S, w S * ∑ i ∈ S, x i = ∑ i, x i * ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), w S := by
  calc ∑ S, w S * ∑ i ∈ S, x i = ∑ S, ∑ i, if i ∈ S then w S * x i else 0 := by
        refine sum_congr rfl fun S _ => ?_
        rw [sum_ite_mem, univ_inter, mul_sum]
    _ = ∑ i, ∑ S, if i ∈ S then w S * x i else 0 := sum_comm
    _ = _ := by
        refine sum_congr rfl fun i _ => ?_
        rw [sum_filter, mul_sum]
        refine sum_congr rfl fun S _ => ?_
        split_ifs <;> ring

/-- **A game with a nonempty core is balanced.** -/
theorem isBalanced_of_mem_core {v : TUGame N} {x : N → ℝ} (hx : IsInCore v x) :
    IsBalanced v := fun w hw =>
  calc ∑ S, w S * v S ≤ ∑ S, w S * ∑ i ∈ S, x i :=
        sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hx.2 S) (hw.1 S)
    _ = ∑ i, x i * ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), w S := sum_weight_mul_sum w x
    _ = v univ := by simp only [hw.2, mul_one]; exact hx.1

/-! ### Singleton weights -/

/-- Weight `a j` on each singleton `{j}`, zero elsewhere. -/
def singletonWeights (a : N → ℝ) (S : Finset N) : ℝ := ∑ j, if S = {j} then a j else 0

lemma sum_singletonWeights_mem (a : N → ℝ) (i : N) :
    ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), singletonWeights a S = a i := by
  simp only [singletonWeights]
  rw [sum_comm]
  simp

lemma sum_singletonWeights_mul (a : N → ℝ) (u : TUGame N) :
    ∑ S, singletonWeights a S * u S = ∑ j, a j * u {j} := by
  simp only [singletonWeights, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp

lemma singletonWeights_nonneg {a : N → ℝ} (ha : ∀ j, 0 ≤ a j) (S : Finset N) :
    0 ≤ singletonWeights a S :=
  sum_nonneg fun j _ => by split_ifs; exacts [ha j, le_rfl]

/-! ### The hard direction for games with positive singletons -/

lemma matrixPayoff_degenerate_left {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : m → n → ℝ) (S : m) (y : n → ℝ) :
    matrixPayoff A (degenerate S) y = ∑ j, A S j * y j := by
  simp [matrixPayoff, degenerate]

lemma matrixPayoff_degenerate_right {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : m → n → ℝ) (x : m → ℝ) (i : n) :
    matrixPayoff A x (degenerate i) = ∑ S, x S * A S i := by
  simp [matrixPayoff, degenerate]

/-- A balanced game in which every singleton has positive worth has a nonempty core. -/
lemma exists_mem_core_of_pos [Nonempty N] {u : TUGame N} (hu : IsBalanced u)
    (hpos : ∀ i, 0 < u {i}) : ∃ x, IsInCore u x := by
  -- `u N > 0`, from the balanced family of singletons.
  have hU : 0 < u univ := by
    have := hu (singletonWeights fun _ => 1)
      ⟨singletonWeights_nonneg fun _ => zero_le_one, sum_singletonWeights_mem _⟩
    rw [sum_singletonWeights_mul] at this
    have : 0 < ∑ j : N, (1 : ℝ) * u {j} :=
      sum_pos (fun j _ => by rw [one_mul]; exact hpos j) univ_nonempty
    linarith
  -- The zero-sum game: rows are coalitions, columns are players.
  set A : Finset N → N → ℝ := fun S i => u S / u univ - if i ∈ S then 1 else 0 with hA
  obtain ⟨μ, y, hμ, hy, hsad⟩ := exists_saddle A
  set val := matrixPayoff A μ y
  have hrow : ∀ i, matrixPayoff A μ (degenerate i) =
      (∑ S, μ S * u S) / u univ - ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), μ S := by
    intro i
    rw [matrixPayoff_degenerate_right, sum_div, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun S _ => ?_
    simp only [hA]
    split_ifs <;> ring
  -- The value is at most zero.
  have hval : val ≤ 0 := by
    by_contra hv
    push Not at hv
    set c := (∑ S, μ S * u S) / u univ
    set ci := fun i => ∑ S ∈ univ.filter (fun S : Finset N => i ∈ S), μ S
    have hci : ∀ i, ci i < c := fun i => by
      have := (hsad μ hμ (degenerate i) (degenerate_mem i)).2
      rw [hrow i] at this
      simp only [ci]; linarith
    have hci0 : ∀ i, 0 ≤ ci i := fun i => sum_nonneg fun S _ => hμ.1 S
    have hc : 0 < c := lt_of_le_of_lt (hci0 (Classical.arbitrary N)) (hci _)
    set a := fun j => 1 - ci j / c
    have ha : ∀ j, 0 < a j := fun j => by
      simp only [a]; rw [sub_pos, div_lt_one hc]; exact hci j
    set w := fun S => μ S / c + singletonWeights a S
    have hw : IsBalancedFamily w := by
      refine ⟨fun S => add_nonneg (div_nonneg (hμ.1 S) hc.le)
        (singletonWeights_nonneg (fun j => (ha j).le) S), fun i => ?_⟩
      simp only [w, sum_add_distrib, sum_singletonWeights_mem, a, ← sum_div]
      change ci i / c + (1 - ci i / c) = 1
      ring
    have hbal := hu w hw
    simp only [w, add_mul, sum_add_distrib, sum_singletonWeights_mul] at hbal
    have h1 : ∑ S, μ S / c * u S = u univ := by
      simp only [div_mul_eq_mul_div, ← sum_div]
      simp only [c]
      exact div_div_cancel₀ (ne_of_gt ((div_pos_iff_of_pos_right hU).1 hc))
    have h2 : 0 < ∑ j, a j * u {j} :=
      sum_pos (fun j _ => mul_pos (ha j) (hpos j)) univ_nonempty
    linarith
  -- So `u N • y` is in the core.
  refine ⟨fun i => u univ * y i, ?_, fun S => ?_⟩
  · rw [← mul_sum, hy.2, mul_one]
  · have := (hsad (degenerate S) (degenerate_mem S) y hy).1
    rw [matrixPayoff_degenerate_left] at this
    have e : ∑ j, A S j * y j = u S / u univ - ∑ j ∈ S, y j := by
      simp only [hA, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul]
      rw [sum_ite_mem, univ_inter, ← mul_sum, hy.2, mul_one]
    rw [e] at this
    rw [← mul_sum]
    have : u S / u univ ≤ ∑ j ∈ S, y j := by linarith
    rwa [div_le_iff₀ hU, mul_comm] at this

/-! ### The theorem -/

/-- **Bondareva–Shapley theorem.** A TU game has a nonempty core if and only if it is
balanced. -/
theorem bondareva_shapley [Nonempty N] (v : TUGame N) :
    (∃ x, IsInCore v x) ↔ IsBalanced v := by
  refine ⟨fun ⟨x, hx⟩ => isBalanced_of_mem_core hx, fun hv => ?_⟩
  -- Add the additive game `K |S|` so that singletons have positive worth.
  set K : ℝ := ∑ i, |v {i}| + 1
  set u : TUGame N := fun S => v S + K * S.card with hu
  have hpos : ∀ i, 0 < u {i} := fun i => by
    simp only [hu, card_singleton, Nat.cast_one, mul_one, K]
    have := single_le_sum (f := fun j => |v {j}|) (fun j _ => abs_nonneg _) (mem_univ i)
    linarith [neg_abs_le (v {i})]
  have hcard : ∀ w : Finset N → ℝ, IsBalancedFamily w →
      ∑ S, w S * (S.card : ℝ) = Fintype.card N := fun w hw => by
    have := sum_weight_mul_sum w (fun _ => (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one, hw.2] at this
    exact this
  have hub : IsBalanced u := fun w hw => by
    simp only [hu, mul_add, sum_add_distrib]
    have e : ∑ S, w S * (K * (S.card : ℝ)) = K * Fintype.card N := by
      rw [← hcard w hw, mul_sum]; exact sum_congr rfl fun S _ => by ring
    rw [e, card_univ]
    linarith [hv w hw]
  obtain ⟨y, hy1, hy2⟩ := exists_mem_core_of_pos hub hpos
  refine ⟨fun i => y i - K, ?_, fun S => ?_⟩
  · rw [sum_sub_distrib, hy1]; simp [hu, card_univ]; ring
  · have := hy2 S
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    simp only [hu] at this
    linarith

/-- Witness: the three-player majority game (a coalition is worth `1` iff it has at least
two members) is not balanced (weights `1/2` on each pair), so its core is empty; adding
`v N = 3/2` instead of `1` makes the equal split `1/2` a core allocation. -/
example : ¬ ∃ x, IsInCore (fun S : Finset (Fin 3) => if 2 ≤ S.card then (1 : ℝ) else 0) x := by
  rintro ⟨x, hsum, hS⟩
  have h01 := hS {0, 1}
  have h02 := hS {0, 2}
  have h12 := hS {1, 2}
  simp [Fin.sum_univ_three] at hsum h01 h02 h12
  linarith

example : IsInCore (fun S : Finset (Fin 3) =>
    if S = univ then (3 / 2 : ℝ) else if 2 ≤ S.card then 1 else 0) (fun _ => 1 / 2) := by
  refine ⟨by simp; norm_num, fun S => ?_⟩
  simp only [sum_const, nsmul_eq_mul]
  split_ifs with h1 h2
  · subst h1; simp; norm_num
  · have : (2 : ℝ) ≤ S.card := by exact_mod_cast h2
    linarith
  · positivity

end Econ
