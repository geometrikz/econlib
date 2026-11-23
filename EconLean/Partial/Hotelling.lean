/-
# The linear city with quadratic transport costs (d'Aspremont–Gabszewicz–Thisse 1979)

Hotelling (1929); d'Aspremont, Gabszewicz and Thisse (1979); Tirole, *The Theory of Industrial
Organization*, §7.1.1. Consumers are uniform on `[0, 1]`. Firm 1 is at `a` and firm 2 at
`1 − b`, with `a, b ≥ 0` and `a + b < 1`; both have marginal cost `c`. A consumer at `x`
buying from a firm at `z` pays its price plus `t (x − z)²`.

With prices `p₁, p₂` the indifferent consumer is
`x̂ = a + (1 − a − b)/2 + (p₂ − p₁) / (2 t (1 − a − b))`, and firm 1 sells to the consumers
to its left (`hotellingShare`; firm 1's demand is `x̂` truncated to `[0, 1]`).

Main results:
* `hotelling_equilibrium`: given firm 2's price `p₂*`, firm 1's profit is maximized at
  `p₁* = c + t(1 − a − b)(1 + (a − b)/3)`, against any demand that is the indifferent
  consumer's location where that lies in `[0, 1]` (and no more than its positive part
  elsewhere). Its equilibrium profit is `t(1 − a − b)(3 + a − b)²/18`. (A generalization of
  `hotelling_bestResponse` to abstract demands.)
* `hotelling_nash`: with the actual demands (firm 1 sells to the consumers left of the
  indifferent one, truncated to `[0, 1]`, firm 2 to the rest), the price pair
  `(p₁*, p₂*)` is a Nash equilibrium of the price game.
* `hotelling_symmetric`: at the ends of the city (`a = b = 0`) prices are `c + t` and profits
  `t/2`.
* `hotelling_max_differentiation`: firm 1's equilibrium profit strictly falls as it moves
  toward the centre (for locations with `a + b < 1`), the force behind maximal
  differentiation, which overturns Hotelling's principle of minimum differentiation. The
  location game itself, including leapfrogging the rival, is not formalized here.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Econ

/-- The location of the consumer indifferent between firm 1 (at `a`, price `p₁`) and firm 2
(at `1 − b`, price `p₂`). -/
noncomputable def hotellingShare (a b t p₁ p₂ : ℝ) : ℝ :=
  a + (1 - a - b) / 2 + (p₂ - p₁) / (2 * t * (1 - a - b))

/-- Equilibrium price of firm 1 (firm 2's is the same with `a` and `b` swapped). -/
noncomputable def hotellingPrice (a b t c : ℝ) : ℝ := c + t * (1 - a - b) * (1 + (a - b) / 3)

/-- Equilibrium profit of firm 1. -/
noncomputable def hotellingProfit (a b t : ℝ) : ℝ := t * (1 - a - b) * (3 + a - b) ^ 2 / 18

/-- **Equilibrium of the price game** (d'Aspremont–Gabszewicz–Thisse 1979). If firm 2 charges
its equilibrium price, firm 1's profit `(p − c) D(p)` is maximal at `hotellingPrice a b t c`,
where it equals `hotellingProfit a b t`; here `D` is any nonnegative demand that equals the
indifferent consumer's location at the equilibrium price and never exceeds its positive part
at prices `p ≥ c` (as the true demand, truncated to `[0, 1]`, does). -/
theorem hotelling_equilibrium {a b t c : ℝ} (hab : a + b < 1)
    (ht : 0 < t) (D : ℝ → ℝ) (hD0 : ∀ p, 0 ≤ D p)
    (hDle : ∀ p, c ≤ p → D p ≤ max 0 (hotellingShare a b t p (hotellingPrice b a t c)))
    (hDeq : D (hotellingPrice a b t c) =
      hotellingShare a b t (hotellingPrice a b t c) (hotellingPrice b a t c)) :
    D (hotellingPrice a b t c) = (3 + a - b) / 6 ∧
      (hotellingPrice a b t c - c) * D (hotellingPrice a b t c) = hotellingProfit a b t ∧
      ∀ p, (p - c) * D p ≤ hotellingProfit a b t := by
  have hL : 0 < 1 - a - b := by linarith
  have hshare : hotellingShare a b t (hotellingPrice a b t c) (hotellingPrice b a t c) =
      (3 + a - b) / 6 := by
    simp only [hotellingShare, hotellingPrice]
    field_simp
    ring
  have hπ0 : 0 ≤ hotellingProfit a b t := by
    unfold hotellingProfit; positivity
  refine ⟨hDeq.trans hshare, ?_, fun p => ?_⟩
  · rw [hDeq, hshare]
    simp only [hotellingPrice, hotellingProfit]
    ring
  rcases lt_or_ge p c with hp | hp
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hD0 p)).trans hπ0
  have hle : (p - c) * D p ≤ (p - c) * max 0 (hotellingShare a b t p (hotellingPrice b a t c)) :=
    mul_le_mul_of_nonneg_left (hDle p hp) (by linarith)
  refine hle.trans ?_
  rcases le_total (hotellingShare a b t p (hotellingPrice b a t c)) 0 with h | h
  · rw [max_eq_left h, mul_zero]; exact hπ0
  · rw [max_eq_right h]
    -- The profit is a concave quadratic in `p` with peak at the equilibrium price.
    have e : (p - c) * hotellingShare a b t p (hotellingPrice b a t c) =
        hotellingProfit a b t - (p - hotellingPrice a b t c) ^ 2 / (2 * t * (1 - a - b)) := by
      simp only [hotellingShare, hotellingPrice, hotellingProfit]
      field_simp
      ring
    rw [e]
    have : 0 ≤ (p - hotellingPrice a b t c) ^ 2 / (2 * t * (1 - a - b)) := by positivity
    linarith

/-- Firm 1's demand: the indifferent consumer's location, truncated to `[0, 1]`. Firm 2 sells
to the remaining `1 − hotellingDemand`. -/
noncomputable def hotellingDemand (a b t p₁ p₂ : ℝ) : ℝ := min 1 (max 0 (hotellingShare a b t p₁ p₂))

lemma one_sub_hotellingShare {a b t : ℝ} (ht : t ≠ 0) (hab : a + b ≠ 1) (p₁ p₂ : ℝ) :
    1 - hotellingShare a b t p₁ p₂ = hotellingShare b a t p₂ p₁ := by
  have : 1 - a - b ≠ 0 := fun h => hab (by linarith)
  have : 1 - b - a ≠ 0 := fun h => hab (by linarith)
  simp only [hotellingShare]
  field_simp
  ring

lemma one_sub_hotellingDemand {a b t : ℝ} (ht : t ≠ 0) (hab : a + b ≠ 1) (p₁ p₂ : ℝ) :
    1 - hotellingDemand a b t p₁ p₂ = hotellingDemand b a t p₂ p₁ := by
  simp only [hotellingDemand, ← one_sub_hotellingShare ht hab p₁ p₂]
  set x := hotellingShare a b t p₁ p₂
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, min_eq_right zero_le_one, max_eq_right (by linarith),
      min_eq_left (by linarith)]
    ring
  · rcases le_total x 1 with h' | h'
    · rw [max_eq_right h, min_eq_right h', max_eq_right (by linarith),
        min_eq_right (by linarith)]
    · rw [max_eq_right h, min_eq_left h', max_eq_left (by linarith),
        min_eq_right zero_le_one]
      ring

/-- Firm 1's best response with the actual truncated demand. -/
lemma hotelling_bestResponse {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (ht : 0 < t) (p : ℝ) :
    (p - c) * hotellingDemand a b t p (hotellingPrice b a t c) ≤ hotellingProfit a b t := by
  have hshare : hotellingShare a b t (hotellingPrice a b t c) (hotellingPrice b a t c) =
      (3 + a - b) / 6 := by
    have hL : 0 < 1 - a - b := by linarith
    simp only [hotellingShare, hotellingPrice]
    field_simp
    ring
  refine (hotelling_equilibrium hab ht (fun p => hotellingDemand a b t p (hotellingPrice b a t c))
    (fun p => le_min zero_le_one (le_max_left _ _)) (fun p _ => min_le_right _ _) ?_).2.2 p
  simp only [hotellingDemand, hshare]
  rw [max_eq_right (by linarith), min_eq_right (by linarith)]

/-- **The price equilibrium** (d'Aspremont–Gabszewicz–Thisse 1979): with the actual demands,
neither firm can gain by deviating from `(p₁*, p₂*)`, and each earns its formula profit. -/
theorem hotelling_nash {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1) (ht : 0 < t) :
    (hotellingPrice a b t c - c) *
        hotellingDemand a b t (hotellingPrice a b t c) (hotellingPrice b a t c) =
      hotellingProfit a b t ∧
    (hotellingPrice b a t c - c) *
        (1 - hotellingDemand a b t (hotellingPrice a b t c) (hotellingPrice b a t c)) =
      hotellingProfit b a t ∧
    (∀ p, (p - c) * hotellingDemand a b t p (hotellingPrice b a t c) ≤ hotellingProfit a b t) ∧
    ∀ p, (p - c) * (1 - hotellingDemand a b t (hotellingPrice a b t c) p) ≤
      hotellingProfit b a t := by
  have hab' : a + b ≠ 1 := ne_of_lt hab
  have hba : b + a < 1 := by linarith
  have h1 : ∀ x y, 0 ≤ x → 0 ≤ y → x + y < 1 →
      hotellingDemand x y t (hotellingPrice x y t c) (hotellingPrice y x t c) = (3 + x - y) / 6 :=
    fun x y hx hy hxy => by
      have hL : 0 < 1 - x - y := by linarith
      have : hotellingShare x y t (hotellingPrice x y t c) (hotellingPrice y x t c) =
          (3 + x - y) / 6 := by
        simp only [hotellingShare, hotellingPrice]
        field_simp
        ring
      simp only [hotellingDemand, this]
      rw [max_eq_right (by linarith), min_eq_right (by linarith)]
  refine ⟨?_, ?_, hotelling_bestResponse ha hb hab ht, fun p => ?_⟩
  · rw [h1 a b ha hb hab]
    simp only [hotellingPrice, hotellingProfit]; ring
  · rw [one_sub_hotellingDemand ht.ne' hab', h1 b a hb ha hba]
    simp only [hotellingPrice, hotellingProfit]; ring
  · rw [one_sub_hotellingDemand ht.ne' hab']
    exact hotelling_bestResponse hb ha hba ht p

/-- **Firms at the ends of the city**: prices `c + t`, profits `t/2`. -/
theorem hotelling_symmetric (t c : ℝ) :
    hotellingPrice 0 0 t c = c + t ∧ hotellingProfit 0 0 t = t / 2 := by
  constructor
  · simp [hotellingPrice]
  · simp only [hotellingProfit]; ring

/-- **The force behind maximal differentiation** (d'Aspremont–Gabszewicz–Thisse 1979): taking
the price equilibrium as given, moving inward (raising `a`) strictly lowers firm 1's
equilibrium profit, whatever firm 2's location. -/
theorem hotelling_max_differentiation {a a' b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haa' : a < a')
    (hab : a' + b < 1) (ht : 0 < t) : hotellingProfit a' b t < hotellingProfit a b t := by
  unfold hotellingProfit
  -- With `s = 3 + a − b`, the profit is `t (4 − 2b − s) s² / 18`.
  set s := 3 + a - b
  set s' := 3 + a' - b
  have hs : 2 < s := by simp only [s]; linarith
  have hss : s < s' := by simp only [s, s']; linarith
  have e : (1 - a - b) * s ^ 2 - (1 - a' - b) * s' ^ 2 =
      (s' - s) * (s ^ 2 + s * s' + s' ^ 2 - (4 - 2 * b) * (s + s')) := by
    simp only [s, s']; ring
  have hpos : 0 < s ^ 2 + s * s' + s' ^ 2 - (4 - 2 * b) * (s + s') := by
    have h1 : 3 - b ≤ s := by simp only [s]; linarith
    have h2 : 3 - b ≤ s' := by linarith
    nlinarith [mul_le_mul h1 h2 (by linarith) (by linarith)]
  have : 0 < (1 - a - b) * s ^ 2 - (1 - a' - b) * s' ^ 2 := by
    rw [e]; exact mul_pos (by linarith) hpos
  have h18 : t * (1 - a' - b) * s' ^ 2 < t * (1 - a - b) * s ^ 2 := by nlinarith
  linarith

end Econ
