/-
# Evolutionarily stable strategies

References. J. Maynard Smith and G. Price (1973), "The Logic of Animal
Conflict", *Nature* 246; J. Weibull (1995), *Evolutionary Game Theory*,
§2.1 (Definition 2.1, Propositions 2.1–2.2) and Example 2.3 (Hawk–Dove).

A symmetric two-player game with payoff matrix `A` (row strategy against
column strategy); mixed strategies are probability vectors `x` and
`E(x, y) = xᵀ A y`. A strategy `x` is an **ESS** if for every mutant `y ≠ x`,
either `E(y, x) < E(x, x)`, or `E(y, x) = E(x, x)` and `E(y, y) < E(x, y)`.

**Results.**
* `isNash_of_isESS` (Weibull Prop. 2.1): an ESS is a symmetric Nash
  equilibrium, `E(y, x) ≤ E(x, x)` for all `y`.
* `isESS_of_strict` : a strict symmetric Nash equilibrium is an ESS.
* `isESS_iff_invasion` (Weibull Prop. 2.2): `x` is an ESS iff it resists every
  small invasion: for each `y ≠ x` there is a barrier `ε̄ > 0` (depending on
  `y`; the uniform-barrier version is not stated) such that `x`
  does strictly better than `y` against the post-entry population
  `(1 − ε) x + ε y` for all `ε ∈ (0, ε̄)`.
* `hawkDove_isESS`: in Hawk–Dove with prize `V` and fight cost `C > V > 0`,
  playing Hawk with probability `V/C` is an ESS (and pure Hawk is not a Nash
  equilibrium, `hawk_not_nash`).
-/
module

public import EconLean.Uncertainty.VNM
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section

namespace Econ

namespace ESS

open Finset

variable {n : ℕ}

/-- Expected payoff of `x` against `y`. -/
def E (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * y j

/-- Evolutionary stability. -/
def IsESS (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ lotteries (Fin n) ∧ ∀ y ∈ lotteries (Fin n), y ≠ x →
    E A y x < E A x x ∨ (E A y x = E A x x ∧ E A y y < E A x y)

/-- Symmetric Nash equilibrium. -/
def IsNash (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ lotteries (Fin n) ∧ ∀ y ∈ lotteries (Fin n), E A y x ≤ E A x x

theorem isNash_of_isESS {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (h : IsESS A x) :
    IsNash A x := by
  refine ⟨h.1, fun y hy => ?_⟩
  by_cases hyx : y = x
  · rw [hyx]
  · rcases h.2 y hy hyx with h1 | ⟨h1, -⟩
    · exact h1.le
    · exact h1.le

theorem isESS_of_strict {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (hx : x ∈ lotteries (Fin n))
    (h : ∀ y ∈ lotteries (Fin n), y ≠ x → E A y x < E A x x) : IsESS A x :=
  ⟨hx, fun y hy hyx => Or.inl (h y hy hyx)⟩

/-- `E` is linear in the first argument. -/
theorem E_mix_left (A : Fin n → Fin n → ℝ) (x y z : Fin n → ℝ) (a b : ℝ) :
    E A (fun i => a * x i + b * y i) z = a * E A x z + b * E A y z := by
  simp only [E, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- `E` is linear in the second argument. -/
theorem E_mix_right (A : Fin n → Fin n → ℝ) (x y z : Fin n → ℝ) (a b : ℝ) :
    E A x (fun j => a * y j + b * z j) = a * E A x y + b * E A x z := by
  simp only [E, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- Payoff advantage of `x` over `y` against the post-entry population
`(1 − ε) x + ε y`: `(1 − ε)(E(x,x) − E(y,x)) + ε(E(x,y) − E(y,y))`. -/
theorem advantage_eq (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (ε : ℝ) :
    E A x (fun j => (1 - ε) * x j + ε * y j) - E A y (fun j => (1 - ε) * x j + ε * y j) =
      (1 - ε) * (E A x x - E A y x) + ε * (E A x y - E A y y) := by
  rw [E_mix_right, E_mix_right]; ring

/-- **Weibull Proposition 2.2.** `x` is an ESS iff every mutant `y ≠ x` has a
positive invasion barrier. -/
theorem isESS_iff_invasion (A : Fin n → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : x ∈ lotteries (Fin n)) :
    IsESS A x ↔ ∀ y ∈ lotteries (Fin n), y ≠ x → ∃ εbar > 0, ∀ ε, 0 < ε → ε < εbar →
      E A y (fun j => (1 - ε) * x j + ε * y j) < E A x (fun j => (1 - ε) * x j + ε * y j) := by
  constructor
  · rintro ⟨-, h⟩ y hy hyx
    rcases h y hy hyx with h1 | ⟨h1, h2⟩
    · -- choose `ε̄` so that the first-order term dominates
      set a := E A x x - E A y x
      set b := E A x y - E A y y
      have ha : 0 < a := by simp only [a]; linarith
      refine ⟨a / (a + |b| + 1), by positivity, fun ε hε hεb => ?_⟩
      have key := advantage_eq A x y ε
      have hε1 : ε < 1 := by
        have : a / (a + |b| + 1) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [abs_nonneg b]
        linarith
      have hb : -|b| ≤ b := neg_abs_le b
      have : ε * (a + |b| + 1) < a := by
        rwa [lt_div_iff₀ (by positivity)] at hεb
      have : 0 < (1 - ε) * a + ε * b := by nlinarith [abs_nonneg b]
      linarith
    · refine ⟨1, one_pos, fun ε hε _ => ?_⟩
      have key := advantage_eq A x y ε
      have : 0 < (1 - ε) * (E A x x - E A y x) + ε * (E A x y - E A y y) := by
        rw [h1, sub_self, mul_zero, zero_add]; exact mul_pos hε (by linarith)
      linarith
  · intro h
    refine ⟨hx, fun y hy hyx => ?_⟩
    obtain ⟨εbar, hεbar, hinv⟩ := h y hy hyx
    -- the advantage is affine in `ε` and positive on `(0, ε̄)`
    set a := E A x x - E A y x
    set b := E A x y - E A y y
    have hpos : ∀ ε, 0 < ε → ε < εbar → 0 < (1 - ε) * a + ε * b := fun ε h1 h2 => by
      have := hinv ε h1 h2; have key := advantage_eq A x y ε; linarith
    have ha : 0 ≤ a := by
      by_contra hneg
      rw [not_le] at hneg
      -- for small `ε` the term `(1 − ε) a` dominates
      set δ := min (εbar / 2) ((-a) / (2 * (|b| + -a)))
      have hδ : 0 < δ := lt_min (by positivity) (div_pos (by linarith)
        (by have := abs_nonneg b; linarith))
      have hδ1 : δ < εbar := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hδ2 : δ ≤ (-a) / (2 * (|b| + -a)) := min_le_right _ _
      have := hpos δ hδ hδ1
      have hden : 0 < 2 * (|b| + -a) := by have := abs_nonneg b; linarith
      have hδ3 : δ * (2 * (|b| + -a)) ≤ -a := by rwa [le_div_iff₀ hden] at hδ2
      have hb : b ≤ |b| := le_abs_self b
      nlinarith [abs_nonneg b]
    rcases ha.lt_or_eq with ha | ha
    · left; simp only [a] at ha; linarith
    · right
      refine ⟨by simp only [a] at ha; linarith, ?_⟩
      have := hpos (εbar / 2) (by positivity) (by linarith)
      rw [← ha, mul_zero, zero_add] at this
      have : 0 < b := pos_of_mul_pos_right this (by positivity)
      simp only [b] at this; linarith

/-! ### Hawk–Dove -/

/-- Hawk–Dove payoffs (strategy `0` = Hawk, `1` = Dove), prize `V`, cost `C`. -/
def hawkDove (V C : ℝ) : Fin 2 → Fin 2 → ℝ := ![![(V - C) / 2, V], ![0, V / 2]]

/-- The mixed strategy playing Hawk with probability `p`. -/
def hdMix (p : ℝ) : Fin 2 → ℝ := ![p, 1 - p]

theorem E_hawkDove (V C p q : ℝ) :
    E (hawkDove V C) (hdMix p) (hdMix q) =
      p * q * ((V - C) / 2) + p * (1 - q) * V + (1 - p) * (1 - q) * (V / 2) := by
  simp [E, hawkDove, hdMix, Fin.sum_univ_two]; ring

theorem hdMix_surj {y : Fin 2 → ℝ} (hy : y ∈ lotteries (Fin 2)) : y = hdMix (y 0) := by
  funext j; fin_cases j
  · rfl
  · have := hy.2; simp [Fin.sum_univ_two] at this; simp [hdMix]; linarith

/-- **Hawk–Dove.** With `0 < V < C`, playing Hawk with probability `V/C` is an
ESS. -/
theorem hawkDove_isESS {V C : ℝ} (hV : 0 < V) (hVC : V < C) :
    IsESS (hawkDove V C) (hdMix (V / C)) := by
  have hC : 0 < C := by linarith
  have hp1 : V / C ≤ 1 := (div_le_one hC).2 hVC.le
  refine ⟨⟨fun j => by fin_cases j <;> simp [hdMix] <;> [positivity; linarith], by
    simp [hdMix, Fin.sum_univ_two]⟩, fun y hy hyx => Or.inr ?_⟩
  rw [hdMix_surj hy] at hyx ⊢
  set q := y 0
  have hq : q ≠ V / C := fun h => hyx (by rw [h])
  rw [E_hawkDove, E_hawkDove, E_hawkDove, E_hawkDove]
  constructor
  · field_simp; ring
  · have : 0 < (q - V / C) ^ 2 := by
      have : q - V / C ≠ 0 := sub_ne_zero.2 hq; positivity
    have e : (V / C) * q * ((V - C) / 2) + V / C * (1 - q) * V + (1 - V / C) * (1 - q) * (V / 2) -
        (q * q * ((V - C) / 2) + q * (1 - q) * V + (1 - q) * (1 - q) * (V / 2)) =
        C / 2 * (q - V / C) ^ 2 := by field_simp; ring
    nlinarith

/-- Pure Hawk is not a Nash equilibrium when `V < C`: Dove does better
against Hawk. -/
theorem hawk_not_nash {V C : ℝ} (hVC : V < C) : ¬ IsNash (hawkDove V C) (hdMix 1) := by
  rintro ⟨-, h⟩
  have := h (hdMix 0) ⟨fun j => by fin_cases j <;> simp [hdMix], by simp [hdMix, Fin.sum_univ_two]⟩
  rw [E_hawkDove, E_hawkDove] at this
  linarith

end ESS

end Econ
