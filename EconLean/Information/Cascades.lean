/-
# Informational cascades (Bikhchandani–Hirshleifer–Welch 1992; Banerjee 1992)

The binary model of BHW (1992, §II). A state `V ∈ {0, 1}` has prior `1/2`. Agents move in
sequence; agent `n` gets a private signal `sₙ ∈ {H, L}` (`true`/`false`) that matches the
state with probability `p ∈ (1/2, 1)`, observes all earlier actions, and adopts (`true`) or
rejects (`false`); adopting pays off when `V = 1`. An indifferent agent follows her own
signal (a common textbook convention; BHW let her randomize, which changes when a cascade
starts but not the absorption argument).

Scope: the public state is modelled directly as the net count of revealed signals. That
earlier actions reveal exactly these signals is what `cascadeAction_injective_of_abs_le_one`
and `cascadeAction_const_of_two_le_abs` show, but the step "the Bayes action given the history
of actions equals `cascadePlay`" is not derived from a probability model of histories.

* `bayesPost_gt_half_iff`, `bayesPost_eq_half_iff`: after `h` high and `l` low signals, the
  posterior of `V = 1` exceeds `1/2` iff `h > l`, and equals `1/2` iff `h = l`. So an agent's
  decision depends only on the net count `d` of high signals that earlier actions revealed
  plus her own: `cascadeAction` is the Bayesian decision (`cascadeAction_eq_bayes`).
* `cascadeAction_injective_of_abs_le_one`, `cascadeAction_const_of_two_le_abs`: an action
  reveals the signal exactly while `|d| ≤ 1`; once `|d| ≥ 2` the action ignores the signal.
* `cascade_absorbing`: once `|d| ≥ 2` (an **informational cascade**), no further signal is
  revealed, the public state is frozen, and every later agent takes the same action whatever
  her signal. `cascade_of_first_two`: if the first two signals agree, everybody from the
  third agent on copies them, even if the cascade is wrong.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Econ

/-- Posterior probability of `V = 1` after `h` high and `l` low signals of precision `p`,
from the prior `1/2`. -/
noncomputable def bayesPost (p : ℝ) (h l : ℕ) : ℝ :=
  p ^ h * (1 - p) ^ l / (p ^ h * (1 - p) ^ l + (1 - p) ^ h * p ^ l)

/-- The likelihood comparison behind the posterior: `pʰ qˡ` vs `qʰ pˡ`. -/
lemma likelihood_lt_iff {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {h l : ℕ} :
    (1 - p) ^ h * p ^ l < p ^ h * (1 - p) ^ l ↔ l < h := by
  have hq : 0 < 1 - p := by linarith
  have hqp : 1 - p < p := by linarith
  have hp0 : 0 < p := by linarith
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have : p ^ h * (1 - p) ^ (h + k) ≤ (1 - p) ^ h * p ^ (h + k) := by
      rw [pow_add, pow_add]
      have := pow_le_pow_left₀ hq.le hqp.le k
      have h0 : 0 ≤ p ^ h * (1 - p) ^ h := by positivity
      nlinarith
    linarith
  · intro hlt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hk := pow_lt_pow_left₀ hqp hq.le (show k + 1 ≠ 0 by omega)
    have h0 : 0 < p ^ l * (1 - p) ^ l := by positivity
    have e1 : (1 - p) ^ (l + k + 1) * p ^ l = (p ^ l * (1 - p) ^ l) * (1 - p) ^ (k + 1) := by
      ring
    have e2 : p ^ (l + k + 1) * (1 - p) ^ l = (p ^ l * (1 - p) ^ l) * p ^ (k + 1) := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hk h0

lemma bayesPost_gt_half_iff {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {h l : ℕ} :
    1 / 2 < bayesPost p h l ↔ l < h := by
  have hq : 0 < 1 - p := by linarith
  have hp0 : 0 < p := by linarith
  have hden : 0 < p ^ h * (1 - p) ^ l + (1 - p) ^ h * p ^ l := by positivity
  rw [bayesPost, lt_div_iff₀ hden, ← likelihood_lt_iff hp hp1]
  constructor <;> intro h' <;> linarith

lemma bayesPost_eq_half_iff {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {h l : ℕ} :
    bayesPost p h l = 1 / 2 ↔ h = l := by
  have hq : 0 < 1 - p := by linarith
  have hp0 : 0 < p := by linarith
  have hden : 0 < p ^ h * (1 - p) ^ l + (1 - p) ^ h * p ^ l := by positivity
  rw [bayesPost, div_eq_iff hden.ne']
  constructor
  · intro he
    rcases lt_trichotomy l h with hlh | rfl | hlh
    · have := (likelihood_lt_iff hp hp1).2 hlh; linarith
    · rfl
    · have := (likelihood_lt_iff (h := l) (l := h) hp hp1).2 hlh; linarith
  · rintro rfl; ring

/-- `+1` for a high signal, `−1` for a low one. -/
def signalSign (b : Bool) : ℤ := if b then 1 else -1

/-- The decision of an agent whose public state (net revealed high signals) is `d` and whose
signal is `b`: adopt if the net count including her own signal is positive, reject if
negative, follow her own signal if zero. -/
def cascadeAction (d : ℤ) (b : Bool) : Bool :=
  if 0 < d + signalSign b then true else if d + signalSign b < 0 then false else b

/-- **The decision rule is Bayesian**: with `h` high and `l` low signals in total (revealed plus
own), `h − l = d + sign(b)`, the agent adopts iff her posterior exceeds `1/2`, or equals `1/2`
and her own signal is high. -/
theorem cascadeAction_eq_bayes {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {h l : ℕ} {d : ℤ}
    {b : Bool} (hd : (h : ℤ) - l = d + signalSign b) :
    cascadeAction d b = true ↔
      (1 / 2 < bayesPost p h l ∨ (bayesPost p h l = 1 / 2 ∧ b = true)) := by
  rw [bayesPost_gt_half_iff hp hp1, bayesPost_eq_half_iff hp hp1, cascadeAction]
  by_cases h1 : 0 < d + signalSign b
  · simp only [h1, ↓reduceIte, true_iff]; left; omega
  · by_cases h2 : d + signalSign b < 0
    · simp only [h1, h2, ↓reduceIte]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro (h | ⟨h, -⟩) <;> omega
    · simp only [h1, h2, ↓reduceIte]
      constructor
      · intro hb; right; exact ⟨by omega, hb⟩
      · rintro (h | ⟨-, hb⟩)
        · omega
        · exact hb

/-- While `|d| ≤ 1` the action reveals the signal. -/
theorem cascadeAction_injective_of_abs_le_one {d : ℤ} (hd : |d| ≤ 1) :
    Function.Injective (cascadeAction d) := by
  have : d = -1 ∨ d = 0 ∨ d = 1 := by rw [abs_le] at hd; omega
  intro b b' h
  rcases this with rfl | rfl | rfl <;> cases b <;> cases b' <;>
    simp_all [cascadeAction, signalSign]

/-- Once `|d| ≥ 2` the action is the same whatever the signal. -/
theorem cascadeAction_const_of_two_le_abs {d : ℤ} (hd : 2 ≤ |d|) (b : Bool) :
    cascadeAction d b = decide (0 < d) := by
  rcases le_abs'.1 hd with h | h <;> cases b <;> simp only [cascadeAction, signalSign] <;>
    split_ifs <;> simp <;> omega

/-- The public state after `n` agents: the net number of high signals revealed by their
actions. A signal is revealed iff `|d| ≤ 1` when its holder moves. -/
def cascadeState (s : ℕ → Bool) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
    if |cascadeState s n| ≤ 1 then cascadeState s n + signalSign (s n) else cascadeState s n

/-- The action of agent `n`. -/
def cascadePlay (s : ℕ → Bool) (n : ℕ) : Bool := cascadeAction (cascadeState s n) (s n)

/-- **Cascades are absorbing** (BHW 1992, §II): once `|d| ≥ 2`, the public state never
changes again and every later agent takes the same action, whatever her signal. -/
theorem cascade_absorbing (s : ℕ → Bool) {n : ℕ} (hn : 2 ≤ |cascadeState s n|) :
    ∀ m, n ≤ m → cascadeState s m = cascadeState s n ∧
      cascadePlay s m = decide (0 < cascadeState s n) := by
  have hstate : ∀ m, n ≤ m → cascadeState s m = cascadeState s n := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m _ ih =>
      rw [cascadeState, ih]
      have : ¬ |cascadeState s n| ≤ 1 := by omega
      simp [this]
  intro m hm
  refine ⟨hstate m hm, ?_⟩
  rw [cascadePlay, hstate m hm]
  exact cascadeAction_const_of_two_le_abs hn _

/-- **A cascade after two agreeing signals**: if the first two signals agree, every agent
from the third on takes the action they indicate, whatever her own signal (even when the
state is the opposite: a wrong cascade). -/
theorem cascade_of_first_two (s : ℕ → Bool) (h : s 0 = s 1) :
    ∀ m, 2 ≤ m → cascadePlay s m = s 0 := by
  have h2 : cascadeState s 2 = 2 * signalSign (s 0) := by
    simp only [cascadeState, h]
    cases s 1 <;> simp [signalSign]
  have habs : 2 ≤ |cascadeState s 2| := by
    rw [h2]; cases s 0 <;> simp [signalSign]
  intro m hm
  rw [(cascade_absorbing s habs m hm).2, h2]
  cases s 0 <;> simp [signalSign]

/-- Witness: after signals `H, H, L, L, …` everybody adopts, although a majority of signals
from the third on are low. -/
example : cascadePlay (fun n => decide (n < 2)) 5 = true :=
  cascade_of_first_two _ rfl 5 (by norm_num)

end Econ
