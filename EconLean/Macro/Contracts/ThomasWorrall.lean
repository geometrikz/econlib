/-
# Self-enforcing wage contracts (Thomas–Worrall)

Thomas and Worrall (1988), "Self-Enforcing Wage Contracts", REStud;
Kocherlakota (1996), REStud; Ljungqvist–Sargent, *Recursive Macroeconomic
Theory*, ch. 20 ("Insurance versus incentives": limited commitment).

**Setting.** A risk-neutral firm insures a risk-averse worker, but neither
party can commit: in each state `s` of the spot market, the wage must lie in
an interval `[a_s, b_s]` — below `a_s` the worker would quit to the spot
market, above `b_s` the firm would renege. (The model is stated in wages; in
the recursive formulation the same algebra governs the worker's relative
Pareto weight.) With multipliers `μ, ν ≥ 0` on the worker's and the firm's
participation constraints, the first-order conditions of the planner's
Lagrangian give the updating rule `x' = x + μ − ν` with complementary
slackness (`μ > 0` only if the worker's constraint binds, `x' = a_s`;
`ν > 0` only if the firm's binds, `x' = b_s`).

**Results.**
* `kkt_clamp`: these conditions determine the new wage uniquely:
  `x' = clamp(x; a_s, b_s) = max a_s (min x b_s)`. The wage **does not move**
  unless a participation constraint binds, and then moves only to the
  nearest boundary (`clamp_eq_self`, `clamp_nearest`).
* `clamp_mono`: the rule is monotone in the inherited wage.
* `path_mem`, `path_ge_of_hit`, `path_le_of_hit`, `path_const`: along any
  sequence of states, the wage lies in the current interval; once the state
  whose lower bound `A = max_s a_s` is the highest has occurred the wage
  stays at least `A`, and symmetrically for `B = min_s b_s`.
* `eventually_constant`: if `A ≤ B` (a wage acceptable in every state
  exists), the wage becomes **constant** once both extreme states have
  occurred: full insurance in the long run.
* `not_eventually_constant`, `eventually_mem_Icc_B_A`: if `A > B`, and both
  extreme states recur infinitely often, the wage **never settles down**,
  but once both have occurred it stays in `[B, A]` for ever.

**Deviations.** The intervals `[a_s, b_s]` (the sets of wages compatible
with both participation constraints) are taken as primitives rather than
computed from the value functions; the Lagrangian first-order conditions are
assumed in the additive KKT form above (in Marcet–Marimon form the update is
multiplicative, which becomes additive after a monotone transformation), and
`path` is defined by the clamp rule that `kkt_clamp` justifies. The state
sequence is deterministic with explicit recurrence hypotheses (TW's
almost-sure statements follow for i.i.d. states, which recur a.s.). The
initial wage `x₀` is not clamped, so the results start at `t ≥ 1`.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace Econ
namespace ThomasWorrall

/-- The clamp of `x` into `[a, b]`. -/
def clamp (a b x : ℝ) : ℝ := max a (min x b)

/-- **KKT conditions give the clamp rule.** -/
theorem kkt_clamp {a b x x' μ ν : ℝ} (hab : a ≤ b) (hx' : x' = x + μ - ν) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (ha : a ≤ x') (hb : x' ≤ b) (hμc : 0 < μ → x' = a) (hνc : 0 < ν → x' = b) :
    x' = clamp a b x := by
  unfold clamp
  rcases hμ.eq_or_lt with h1 | h1 <;> rcases hν.eq_or_lt with h2 | h2
  · subst h1 h2
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]; linarith
  · have := hνc h2; subst h1
    rw [min_eq_right (by linarith), max_eq_right hab]; exact this
  · have := hμc h1; subst h2
    rw [max_eq_left (by simp only [min_le_iff]; left; linarith)]; exact this
  · have e1 := hμc h1; have e2 := hνc h2
    have hab' : a = b := by linarith
    rw [max_eq_left (min_le_right _ _ |>.trans hab'.ge)]; exact e1

theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : a ≤ clamp a b x ∧ clamp a b x ≤ b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

/-- **Wage rigidity**: inside the interval nothing changes. -/
theorem clamp_eq_self {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) : clamp a b x = x := by
  simp [clamp, min_eq_left hb, max_eq_right ha]

theorem clamp_mono (a b : ℝ) {x y : ℝ} (h : x ≤ y) : clamp a b x ≤ clamp a b y :=
  max_le_max le_rfl (min_le_min h le_rfl)

/-- The clamp is the point of `[a, b]` nearest to `x`. -/
theorem clamp_nearest {a b x y : ℝ} (hab : a ≤ b) (hy : a ≤ y ∧ y ≤ b) :
    |clamp a b x - x| ≤ |y - x| := by
  unfold clamp
  rcases le_total x a with h | h
  · rw [min_eq_left (h.trans hab), max_eq_left h, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]; linarith
  · rcases le_total x b with h' | h'
    · rw [min_eq_left h', max_eq_right h, sub_self, abs_zero]; exact abs_nonneg _
    · rw [min_eq_right h', max_eq_right hab, abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]; linarith

/-! ### Dynamics -/

variable {S : Type*} (a b : S → ℝ) (s : ℕ → S) (x₀ : ℝ)

/-- The wage path: `x₀` given, `x_{t+1} = clamp(x_t; a_{s_{t+1}}, b_{s_{t+1}})`. -/
def path : ℕ → ℝ
  | 0 => x₀
  | t + 1 => clamp (a (s (t + 1))) (b (s (t + 1))) (path t)

theorem path_succ (t : ℕ) :
    path a b s x₀ (t + 1) = clamp (a (s (t + 1))) (b (s (t + 1))) (path a b s x₀ t) := rfl

/-- The wage is always in the current state's interval. -/
theorem path_mem (hab : ∀ σ, a σ ≤ b σ) {t : ℕ} (ht : 1 ≤ t) :
    a (s t) ≤ path a b s x₀ t ∧ path a b s x₀ t ≤ b (s t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' ht
  exact clamp_mem (hab _) _

/-- Once the wage is at least `A` it stays so, if every interval reaches
above `A`. -/
theorem path_ge_of_hit {A : ℝ} (hA : ∀ σ, A ≤ b σ) {t₁ : ℕ} (h₁ : A ≤ path a b s x₀ t₁) :
    ∀ k, A ≤ path a b s x₀ (t₁ + k) := by
  intro k
  induction k with
  | zero => simpa using h₁
  | succ k ih =>
    rw [← add_assoc, path_succ]
    exact le_max_of_le_right (le_min ih (hA _))

theorem path_le_of_hit {B : ℝ} (hB : ∀ σ, a σ ≤ B) {t₁ : ℕ} (h₁ : path a b s x₀ t₁ ≤ B) :
    ∀ k, path a b s x₀ (t₁ + k) ≤ B := by
  intro k
  induction k with
  | zero => simpa using h₁
  | succ k ih =>
    rw [← add_assoc, path_succ]
    exact max_le (hB _) ((min_le_left _ _).trans ih)

/-- Inside `[A, B] ⊆ [a_s, b_s]` for all `s`, the wage is constant. -/
theorem path_const {A B : ℝ} (ha : ∀ σ, a σ ≤ A) (hb : ∀ σ, B ≤ b σ) {t : ℕ}
    (h1 : A ≤ path a b s x₀ t) (h2 : path a b s x₀ t ≤ B) :
    ∀ k, path a b s x₀ (t + k) = path a b s x₀ t := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, path_succ, ih]
    exact clamp_eq_self ((ha _).trans h1) (h2.trans (hb _))

/-- **Long-run full insurance.** If `A = max a_s ≤ B = min b_s`, and the
states attaining `A` and `B` have both occurred by date `T`, the wage is
constant from `T` on. -/
theorem eventually_constant {A B : ℝ} (hAB : A ≤ B) (ha : ∀ σ, a σ ≤ A) (hb : ∀ σ, B ≤ b σ)
    {sA sB : S} (hsA : a sA = A) (hsB : b sB = B) {tA tB : ℕ} (htA : 1 ≤ tA) (htB : 1 ≤ tB)
    (hA : s tA = sA) (hB : s tB = sB) :
    ∀ t, max tA tB ≤ t → path a b s x₀ t = path a b s x₀ (max tA tB) := by
  have hab : ∀ σ, a σ ≤ b σ := fun σ => (ha σ).trans (hAB.trans (hb σ))
  have hA' : A ≤ path a b s x₀ tA := by rw [← hsA, ← hA]; exact (path_mem a b s x₀ hab htA).1
  have hB' : path a b s x₀ tB ≤ B := by rw [← hsB, ← hB]; exact (path_mem a b s x₀ hab htB).2
  have hgeA := path_ge_of_hit a b s x₀ (fun σ => hAB.trans (hb σ)) hA'
  have hleB := path_le_of_hit a b s x₀ (fun σ => (ha σ).trans hAB) hB'
  have h1 : A ≤ path a b s x₀ (max tA tB) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left tA tB); rw [hk]; exact hgeA k
  have h2 : path a b s x₀ (max tA tB) ≤ B := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_right tA tB); rw [hk]; exact hleB k
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact path_const a b s x₀ ha hb h1 h2 k

/-- **Perpetual fluctuations.** If `B < A` (no wage is acceptable in every
state) and the extreme states recur infinitely often, the wage is never
eventually constant. -/
theorem not_eventually_constant {A B : ℝ} (hBA : B < A) (hab : ∀ σ, a σ ≤ b σ)
    {sA sB : S} (hsA : a sA = A) (hsB : b sB = B)
    (hA : ∀ T, ∃ t, T ≤ t ∧ 1 ≤ t ∧ s t = sA) (hB : ∀ T, ∃ t, T ≤ t ∧ 1 ≤ t ∧ s t = sB) :
    ¬ ∃ T c, ∀ t, T ≤ t → path a b s x₀ t = c := by
  rintro ⟨T, c, hc⟩
  obtain ⟨t₁, hT₁, h1, hs₁⟩ := hA T
  obtain ⟨t₂, hT₂, h2, hs₂⟩ := hB T
  have e1 := (path_mem a b s x₀ hab h1).1
  have e2 := (path_mem a b s x₀ hab h2).2
  rw [hs₁, hsA, hc t₁ hT₁] at e1
  rw [hs₂, hsB, hc t₂ hT₂] at e2
  linarith

/-- **Long-run confinement without overlap.** If `B < A`, once both extreme
states have occurred the wage stays in `[B, A]` forever, moving between the
two bounds as the extreme states recur. -/
theorem eventually_mem_Icc_B_A {A B : ℝ} (hBA : B < A) (ha : ∀ σ, a σ ≤ A) (hb : ∀ σ, B ≤ b σ)
    (hab : ∀ σ, a σ ≤ b σ) {sA sB : S} (hsA : a sA = A) (hsB : b sB = B) {tA tB : ℕ}
    (htA : 1 ≤ tA) (htB : 1 ≤ tB) (hA : s tA = sA) (hB : s tB = sB) :
    ∀ t, max tA tB ≤ t → B ≤ path a b s x₀ t ∧ path a b s x₀ t ≤ A := by
  have hA' : B ≤ path a b s x₀ tA := by
    have := (path_mem a b s x₀ hab htA).1; rw [hA, hsA] at this; linarith
  have hB' : path a b s x₀ tB ≤ A := by
    have := (path_mem a b s x₀ hab htB).2; rw [hB, hsB] at this; linarith
  intro t ht
  obtain ⟨k₁, hk₁⟩ := Nat.exists_eq_add_of_le ((le_max_left tA tB).trans ht)
  obtain ⟨k₂, hk₂⟩ := Nat.exists_eq_add_of_le ((le_max_right tA tB).trans ht)
  exact ⟨hk₁ ▸ path_ge_of_hit a b s x₀ hb hA' k₁, hk₂ ▸ path_le_of_hit a b s x₀ ha hB' k₂⟩

end ThomasWorrall
end Econ

end
