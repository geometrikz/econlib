/-
# Cheap talk: partition equilibria in the uniform-quadratic model (Crawford–Sobel 1982)

Crawford and Sobel (1982), §4 example; Gibbons (1992), §4.3.A. The sender's type `θ` is
uniform on `[0, 1]`. After a costless message the receiver takes an action `y`; the receiver's
payoff is `−(y − θ)²` and the sender's is `−(y − θ − b)²`, with bias `b > 0`.

In a **partition equilibrium** with `N` steps `0 = a₀ < a₁ < ⋯ < a_N = 1`, types in
`[aᵢ, aᵢ₊₁]` send the same message and the receiver, whose posterior is uniform on that
interval, takes the conditional mean `yᵢ = (aᵢ + aᵢ₊₁)/2` (`midpoint_minimizes`: the midpoint
minimizes the expected quadratic loss). The sender's incentive constraint asks every type to
weakly prefer the action of her own interval to every other equilibrium action
(`IsPartitionEq`). Scope: the receiver's midpoint rule and the interval structure are part
of the definition; Crawford and Sobel's theorem that every equilibrium is of this partition
form, and the general (non-uniform, non-quadratic) model, are not formalized.

Main results:
* `partitionEq_arbitrage`: the **arbitrage condition** `aᵢ₊₂ − aᵢ₊₁ = aᵢ₊₁ − aᵢ + 4b`: each
  boundary type is indifferent between the two neighbouring actions, so the steps grow by
  `4b`.
* `partitionEq_closed_form`: `aᵢ = i a₁ + 2 i (i − 1) b`.
* `partitionEq_exists_iff`: an `N`-step equilibrium exists iff `2 N (N − 1) b < 1`. In
  particular the number of steps is bounded, and more bias means coarser communication; the
  one-step (babbling) equilibrium always exists.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

/-- The receiver's expected loss from action `y` on the interval `[a, c]` (times `c − a`):
`∫ₐᶜ (y − θ)² dθ = (c − a)(y − (a + c)/2)² + (c − a)³/12`. -/
lemma integral_sq_loss (a c y : ℝ) :
    ∫ θ in a..c, (y - θ) ^ 2 = (c - a) * (y - (a + c) / 2) ^ 2 + (c - a) ^ 3 / 12 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) y, integral_pow]
  ring

/-- **The receiver's best response** to a uniform posterior on `[a, c]` is the midpoint. -/
theorem midpoint_minimizes {a c : ℝ} (hac : a ≤ c) (y : ℝ) :
    ∫ θ in a..c, ((a + c) / 2 - θ) ^ 2 ≤ ∫ θ in a..c, (y - θ) ^ 2 := by
  rw [integral_sq_loss, integral_sq_loss]
  have : 0 ≤ (c - a) * (y - (a + c) / 2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add]
  linarith

/-- The receiver's action on the `i`-th interval: its midpoint. -/
noncomputable def ctAction (a : ℕ → ℝ) (i : ℕ) : ℝ := (a i + a (i + 1)) / 2

/-- An `N`-step **partition equilibrium** with bias `b`: boundaries `0 = a₀ < ⋯ < a_N = 1`,
the receiver plays the midpoint of each interval, and every sender type weakly prefers the
action of her interval to every other equilibrium action. -/
def IsPartitionEq (b : ℝ) (N : ℕ) (a : ℕ → ℝ) : Prop :=
  0 < N ∧ a 0 = 0 ∧ a N = 1 ∧ (∀ i < N, a i < a (i + 1)) ∧
    ∀ i < N, ∀ θ, a i ≤ θ → θ ≤ a (i + 1) → ∀ j < N,
      (ctAction a i - θ - b) ^ 2 ≤ (ctAction a j - θ - b) ^ 2

/-- **Arbitrage condition** (Crawford–Sobel 1982, eq. (A) in the uniform-quadratic case). -/
theorem partitionEq_arbitrage {b : ℝ} {N : ℕ} {a : ℕ → ℝ} (h : IsPartitionEq b N a) {i : ℕ}
    (hi : i + 1 < N) : a (i + 2) - a (i + 1) = a (i + 1) - a i + 4 * b := by
  obtain ⟨-, -, -, hmono, hic⟩ := h
  -- The boundary type `a (i+1)` belongs to intervals `i` and `i + 1`.
  have h1 := hic i (by omega) (a (i + 1)) (hmono i (by omega)).le le_rfl (i + 1) hi
  have h2 := hic (i + 1) hi (a (i + 1)) le_rfl (hmono (i + 1) hi).le i (by omega)
  have heq : (ctAction a i - a (i + 1) - b) ^ 2 = (ctAction a (i + 1) - a (i + 1) - b) ^ 2 :=
    le_antisymm h1 h2
  have hlt : ctAction a i < ctAction a (i + 1) := by
    simp only [ctAction]
    have := hmono i (by omega)
    have := hmono (i + 1) hi
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 heq with h | h
  · linarith
  · simp only [ctAction] at h
    linarith

/-- **Closed form of the boundaries**: `aᵢ = i a₁ + 2 i (i − 1) b` for `i ≤ N`. -/
theorem partitionEq_closed_form {b : ℝ} {N : ℕ} {a : ℕ → ℝ} (h : IsPartitionEq b N a) :
    ∀ i ≤ N, a i = i * a 1 + 2 * i * (i - 1) * b := by
  have h0 := h.2.1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  match i, ih with
  | 0, _ => simp [h0]
  | 1, _ => simp
  | k + 2, ih =>
    have e := partitionEq_arbitrage h (i := k) (by omega)
    rw [ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)] at e
    push_cast at e ⊢
    linarith

/-- The incentive constraint holds as soon as the actions are increasing and each boundary
type is exactly between the two neighbouring actions. -/
lemma partitionEq_ic_of_boundary {b : ℝ} {a : ℕ → ℝ} (hmono : StrictMono a)
    (hbd : ∀ i, (ctAction a i + ctAction a (i + 1)) / 2 = a (i + 1) + b) {i : ℕ} {θ : ℝ}
    (h₁ : a i ≤ θ) (h₂ : θ ≤ a (i + 1)) (j : ℕ) :
    (ctAction a i - θ - b) ^ 2 ≤ (ctAction a j - θ - b) ^ 2 := by
  have hy : StrictMono (ctAction a) := strictMono_nat_of_lt_succ fun k => by
    simp only [ctAction]
    have := hmono (Nat.lt_succ_self k)
    have := hmono (Nat.lt_succ_self (k + 1))
    linarith
  -- `(y_j − x)² − (y_i − x)² = (y_j − y_i)(y_j + y_i − 2x)`.
  have key : (ctAction a j - θ - b) ^ 2 - (ctAction a i - θ - b) ^ 2 =
      (ctAction a j - ctAction a i) * (ctAction a j + ctAction a i - 2 * (θ + b)) := by ring
  rcases lt_trichotomy j i with hji | rfl | hij
  · -- Lower actions: the sender's ideal point is above `a i + b`.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hji
    have hb := hbd (j + k)
    have hle : ctAction a j ≤ ctAction a (j + k) := hy.monotone (by omega)
    have hlt : ctAction a j < ctAction a (j + k + 1) := hy (by omega)
    have : ctAction a j + ctAction a (j + k + 1) ≤ 2 * (θ + b) := by linarith
    nlinarith
  · simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have hb := hbd i
    have : ctAction a (i + 1) ≤ ctAction a (i + k + 1) := hy.monotone (by omega)
    have hlt : ctAction a i < ctAction a (i + k + 1) := hy (by omega)
    have : 2 * (θ + b) ≤ ctAction a (i + k + 1) + ctAction a i := by linarith
    nlinarith

/-- **Existence of `N`-step equilibria** (Crawford–Sobel 1982, uniform-quadratic case): with
bias `b > 0`, an `N`-step partition equilibrium exists iff `2 N (N − 1) b < 1`. -/
theorem partitionEq_exists_iff {b : ℝ} (hb : 0 < b) {N : ℕ} (hN : 0 < N) :
    (∃ a, IsPartitionEq b N a) ↔ 2 * N * (N - 1) * b < 1 := by
  constructor
  · rintro ⟨a, h⟩
    have hN' := partitionEq_closed_form h N le_rfl
    rw [h.2.2.1] at hN'
    have h1 : 0 < a 1 := by
      have := h.2.2.2.1 0 hN
      rw [h.2.1] at this
      simpa using this
    have : (0 : ℝ) < N * a 1 := mul_pos (by exact_mod_cast hN) h1
    linarith
  · intro hlt
    set a1 : ℝ := (1 - 2 * N * (N - 1) * b) / N
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have ha1 : 0 < a1 := div_pos (by linarith) hN'
    set a : ℕ → ℝ := fun i => i * a1 + 2 * i * (i - 1) * b
    have hstep : ∀ i : ℕ, a (i + 1) - a i = a1 + 4 * i * b := fun i => by
      simp only [a]; push_cast; ring
    have hmono : StrictMono a := strictMono_nat_of_lt_succ fun i => by
      have := hstep i
      have : (0 : ℝ) ≤ 4 * i * b := by positivity
      linarith
    have hbd : ∀ i, (ctAction a i + ctAction a (i + 1)) / 2 = a (i + 1) + b := fun i => by
      simp only [ctAction, a]; push_cast; ring
    refine ⟨a, hN, by simp [a], ?_, fun i _ => hmono (Nat.lt_succ_self i),
      fun i _ θ h₁ h₂ j _ => partitionEq_ic_of_boundary hmono hbd h₁ h₂ j⟩
    simp only [a, a1]
    field_simp
    ring

/-- **Babbling** (the one-step equilibrium) exists for every bias. -/
theorem babbling_isPartitionEq {b : ℝ} (hb : 0 < b) : ∃ a, IsPartitionEq b 1 a :=
  (partitionEq_exists_iff hb one_pos).2 (by norm_num)

/-- Witness: with `b = 1/20`, a two-step equilibrium exists (`2·2·1·b = 1/5 < 1`) but a
four-step one does not (`2·4·3·b = 6/5 ≥ 1`). -/
example : (∃ a, IsPartitionEq (1 / 20) 2 a) ∧ ¬ ∃ a, IsPartitionEq (1 / 20) 4 a := by
  refine ⟨(partitionEq_exists_iff (by norm_num) (by norm_num)).2 (by norm_num), fun h => ?_⟩
  have := (partitionEq_exists_iff (b := 1 / 20) (by norm_num) (N := 4) (by norm_num)).1 h
  norm_num at this

end Econ
