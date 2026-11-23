/-
# Zero-sum games: von Neumann's minimax theorem

MWG §8.D (Exercise 8.D.7 and the discussion of strictly competitive games); von Neumann
(1928). A two-player zero-sum game is a payoff matrix `A`: the row player picks `i`, the
column player picks `j`, the row player receives `A i j` and the column player pays it.
With mixed strategies `x` (rows) and `y` (columns) the row player's expected payoff is
`xᵀ A y`.

Main results:
* `exists_saddle` (minimax theorem): there are mixed strategies `x*`, `y*` that are best
  responses to each other: `xᵀ A y* ≤ x*ᵀ A y* ≤ x*ᵀ A y` for all mixed `x`, `y`.
* `exists_unique_value`: the game has a unique **value** `v`: the row player can guarantee
  at least `v` and the column player can hold the row player to at most `v`. Equivalently
  `max_x min_y = min_y max_x`.
* `IsSaddle.interchange`: equilibrium strategies are interchangeable.

The proof applies Mathlib's Sion minimax theorem (`Sion.exists_isSaddlePointOn`): the payoff
is bilinear (so continuous, convex and concave in each argument) and the sets of mixed
strategies are nonempty, convex and compact (`isCompact_lotteries`).
-/
module

public import EconLean.Games.Mixed
public import Mathlib.Topology.Sion

@[expose] public section

namespace Econ

open Finset

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Row player's expected payoff `xᵀ A y` in the matrix game `A`. -/
def matrixPayoff (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * y j

/-- `(x, y)` is a **saddle point** (an equilibrium in mixed strategies) of the matrix game. -/
def IsSaddle (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) : Prop :=
  x ∈ lotteries m ∧ y ∈ lotteries n ∧
    ∀ x' ∈ lotteries m, ∀ y' ∈ lotteries n,
      matrixPayoff A x' y ≤ matrixPayoff A x y ∧ matrixPayoff A x y ≤ matrixPayoff A x y'

/-- `v` is the **value** of the game: the row player has a mixed strategy guaranteeing at
least `v`, and the column player one guaranteeing that the row player gets at most `v`. -/
def IsValue (A : m → n → ℝ) (v : ℝ) : Prop :=
  (∃ x ∈ lotteries m, ∀ y ∈ lotteries n, v ≤ matrixPayoff A x y) ∧
    ∃ y ∈ lotteries n, ∀ x ∈ lotteries m, matrixPayoff A x y ≤ v

theorem matrixPayoff_mix_left (A : m → n → ℝ) (x x' : m → ℝ) (y : n → ℝ) (a b : ℝ) :
    matrixPayoff A (a • x + b • x') y = a * matrixPayoff A x y + b * matrixPayoff A x' y := by
  simp only [matrixPayoff, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem matrixPayoff_mix_right (A : m → n → ℝ) (x : m → ℝ) (y y' : n → ℝ) (a b : ℝ) :
    matrixPayoff A x (a • y + b • y') = a * matrixPayoff A x y + b * matrixPayoff A x y' := by
  simp only [matrixPayoff, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_matrixPayoff_left (A : m → n → ℝ) (y : n → ℝ) :
    Continuous fun x : m → ℝ => matrixPayoff A x y := by
  unfold matrixPayoff; fun_prop

theorem continuous_matrixPayoff_right (A : m → n → ℝ) (x : m → ℝ) :
    Continuous fun y : n → ℝ => matrixPayoff A x y := by
  unfold matrixPayoff; fun_prop

/-- **Minimax theorem** (von Neumann 1928): every finite two-player zero-sum game has a
saddle point in mixed strategies. -/
theorem exists_saddle [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ x y, IsSaddle A x y := by
  classical
  -- Sion with the column player's strategy as the minimizing variable.
  have hX : (lotteries n).Nonempty := ⟨_, degenerate_mem (Classical.arbitrary n)⟩
  have hY : (lotteries m).Nonempty := ⟨_, degenerate_mem (Classical.arbitrary m)⟩
  obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn (f := fun y x => matrixPayoff A x y)
    hX convex_lotteries (isCompact_lotteries n)
    (fun x _ => (continuous_matrixPayoff_right A x).continuousOn.lowerSemicontinuousOn)
    (fun x _ => ConvexOn.quasiconvexOn ⟨convex_lotteries, fun y _ y' _ p q _ _ _ => le_of_eq
      (matrixPayoff_mix_right A x y y' p q)⟩)
    convex_lotteries hY (isCompact_lotteries m)
    (fun y _ => (continuous_matrixPayoff_left A y).continuousOn.upperSemicontinuousOn)
    (fun y _ => ConcaveOn.quasiconcaveOn ⟨convex_lotteries, fun x _ x' _ p q _ _ _ => ge_of_eq
      (matrixPayoff_mix_left A x x' y p q)⟩)
  exact ⟨b, a, hb, ha, fun x' hx' y' hy' => ⟨hsad a ha x' hx', hsad y' hy' b hb⟩⟩

/-- At a saddle point the payoff is the value of the game. -/
theorem IsSaddle.isValue {A : m → n → ℝ} {x : m → ℝ} {y : n → ℝ} (h : IsSaddle A x y) :
    IsValue A (matrixPayoff A x y) :=
  ⟨⟨x, h.1, fun y' hy' => (h.2.2 x h.1 y' hy').2⟩,
    ⟨y, h.2.1, fun x' hx' => (h.2.2 x' hx' y h.2.1).1⟩⟩

/-- The value is unique: whatever the row player can guarantee is at most what the column
player can hold it to. -/
theorem IsValue.unique {A : m → n → ℝ} {v w : ℝ} (hv : IsValue A v) (hw : IsValue A w) :
    v = w := by
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := hv
  obtain ⟨⟨x', hx', hxw⟩, ⟨y', hy', hyw⟩⟩ := hw
  exact le_antisymm ((hxv y' hy').trans (hyw x hx)) ((hxw y hy).trans (hyv x' hx'))

/-- **Every finite zero-sum game has a unique value** (`max min = min max`). -/
theorem exists_unique_value [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃! v, IsValue A v := by
  obtain ⟨x, y, h⟩ := exists_saddle A
  exact ⟨_, h.isValue, fun w hw => hw.unique h.isValue⟩

/-- **Interchangeability**: if `(x, y)` and `(x', y')` are saddle points, so is `(x, y')`. -/
theorem IsSaddle.interchange {A : m → n → ℝ} {x x' : m → ℝ} {y y' : n → ℝ}
    (h : IsSaddle A x y) (h' : IsSaddle A x' y') : IsSaddle A x y' := by
  have hv := h.isValue.unique h'.isValue
  refine ⟨h.1, h'.2.1, fun x'' hx'' y'' hy'' => ⟨?_, ?_⟩⟩
  · -- `x''ᵀAy' ≤ v' = v ≤ xᵀAy'`.
    have h1 := (h'.2.2 x'' hx'' y' h'.2.1).1
    have h2 := (h.2.2 x h.1 y' h'.2.1).2
    linarith
  · have h1 := (h.2.2 x h.1 y'' hy'').2
    have h2 := (h'.2.2 x h.1 y' h'.2.1).1
    have h3 := (h.2.2 x h.1 y' h'.2.1).2
    have h4 := (h'.2.2 x' h'.1 y'' hy'').2
    linarith

/-- **Witness: matching pennies has value `0`**, with both players mixing `1/2`–`1/2`. -/
example : IsValue (fun i j : Bool => if i = j then (1 : ℝ) else -1) 0 := by
  have hu : (fun _ : Bool => (1 / 2 : ℝ)) ∈ lotteries Bool := ⟨fun _ => by norm_num, by simp⟩
  refine ⟨⟨_, hu, fun y hy => ?_⟩, ⟨_, hu, fun x hx => ?_⟩⟩
  · simp [matrixPayoff]; linarith
  · simp [matrixPayoff]

end Econ
