/-
# Validity of the first-order approach (Rogerson 1985)

Rogerson (1985), "The first-order approach to principal–agent problems", Econometrica;
Mirrlees (1975/1999); Holmström (1979); Bolton–Dewatripont §4.4; MWG §14.B. The agent chooses
effort `a` in an interval `I`; output takes one of the values `0, 1, …, m` (ordered from worst to
best), with probability `p a j` (only `Σ_j p a j = 1` is used, not `p ≥ 0`). The agent's payoff from wages `w j` is
`U a = Σ_j p a j · u (w j) − ψ a`, with `ψ` a convex cost.

The **first-order approach** replaces the agent's incentive constraint by the first-order
condition `U' a* = 0`. It is valid when that condition implies that `a*` is a global optimum.

* `expect_abel`: summation by parts,
  `Σ_{j ≤ m} p j v j = v m · F m − Σ_{k < m} F k (v (k+1) − v k)`, with `F k = Σ_{j ≤ k} p j`.
* `expected_concave`: under the **convexity of the distribution function condition** (CDFC:
  each `F k` is convex in `a`), expected utility from a nondecreasing utility schedule is
  concave in effort.
* `foa_valid`: hence, with a convex cost, the first-order condition implies that `a*`
  maximizes the agent's payoff on `I`.
* `mirrlees_monotone`: a wage schedule of the Mirrlees–Holmström form `g (w j) = λ + μ · L j`,
  with `g` strictly increasing, `μ ≥ 0` and `L` nondecreasing, is nondecreasing. In the
  principal–agent problem `g = 1/u'` and `L j = p_a(a*, j)/p(a*, j)` is the likelihood ratio,
  nondecreasing under **MLRP**; these links are not encoded: `g` and `L` are abstract, so the
  hypotheses are a sufficient condition standing in for "concave `u` and MLRP".
* `rogerson`: combining these, under CDFC and a nondecreasing `L` (standing in for MLRP), with
  `μ ≥ 0`, a wage schedule satisfying the Mirrlees–Holmström condition satisfies the agent's
  global incentive constraint at any effort satisfying the first-order condition.
* Witnesses: two outcomes with success probability `a` on `[0, 1]` and cost `a²/2` (a linear,
  hence weakly convex, distribution function; probabilities lie in `[0, 1]` on `I`); a monotone Mirrlees–Holmström schedule.

Not formalized: the derivation of the Mirrlees–Holmström condition from the principal's
relaxed program, and the proof that `μ ≥ 0` (Rogerson's Lemma; taken here as a hypothesis);
Jewitt's (1988) alternative conditions; continuous output.
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

namespace Econ

open Finset Set

/-- The distribution function: the probability of an output at most `k`. -/
def outputCDF (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), p j

/-- **Summation by parts**. -/
theorem expect_abel (p v : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range (m + 1), p j * v j =
      v m * outputCDF p m - ∑ k ∈ range m, outputCDF p k * (v (k + 1) - v k) := by
  induction m with
  | zero => simp [outputCDF, mul_comm]
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun k => outputCDF p k * _)]
    have : outputCDF p (m + 1) = outputCDF p m + p (m + 1) := by
      unfold outputCDF; rw [sum_range_succ]
    rw [this]
    ring

/-- **CDFC implies concave expected utility**: if each distribution function `F k` is convex
in effort on `I`, the probabilities sum to `1` on `I`, and `v` is nondecreasing, then
`a ↦ Σ_{j ≤ m} p a j · v j` is concave on `I`. -/
theorem expected_concave {I : Set ℝ} (hI : Convex ℝ I) {p : ℝ → ℕ → ℝ} {m : ℕ}
    (hsum : ∀ a ∈ I, outputCDF (p a) m = 1)
    (hcdfc : ∀ k < m, ConvexOn ℝ I (fun a => outputCDF (p a) k)) {v : ℕ → ℝ}
    (hv : ∀ k, v k ≤ v (k + 1)) :
    ConcaveOn ℝ I (fun a => ∑ j ∈ range (m + 1), p a j * v j) := by
  -- on `I` the function is `v m − Σ_k F k · Δ k`, a constant minus nonnegative multiples of
  -- convex functions
  have heq : EqOn (fun a => v m - ∑ k ∈ range m, outputCDF (p a) k * (v (k + 1) - v k))
      (fun a => ∑ j ∈ range (m + 1), p a j * v j) I := by
    intro a ha
    simp only
    rw [expect_abel, hsum a ha, mul_one]
  refine ConcaveOn.congr ?_ heq
  refine ⟨hI, fun x hx y hy α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  have key : ∀ k ∈ range m, outputCDF (p (α * x + β * y)) k * (v (k + 1) - v k) ≤
      α * (outputCDF (p x) k * (v (k + 1) - v k)) +
        β * (outputCDF (p y) k * (v (k + 1) - v k)) := by
    intro k hk
    have hc := (hcdfc k (mem_range.1 hk)).2 hx hy hα hβ hαβ
    simp only [smul_eq_mul] at hc
    have hd : 0 ≤ v (k + 1) - v k := sub_nonneg.2 (hv k)
    nlinarith
  have hs := sum_le_sum key
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  have : α * v m + β * v m = v m := by rw [← add_mul, hαβ, one_mul]
  nlinarith

/-- **Validity of the first-order approach** (Rogerson 1985): under CDFC, with a
nondecreasing utility schedule `v j = u (w j)` and a convex cost `ψ`, an effort `a*` in `I`
satisfying the first-order condition maximizes the agent's payoff over `I`. -/
theorem foa_valid {I : Set ℝ} (hI : Convex ℝ I) {p : ℝ → ℕ → ℝ} {m : ℕ}
    (hsum : ∀ a ∈ I, outputCDF (p a) m = 1)
    (hcdfc : ∀ k < m, ConvexOn ℝ I (fun a => outputCDF (p a) k)) {v : ℕ → ℝ}
    (hv : ∀ k, v k ≤ v (k + 1)) {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ I ψ) {a : ℝ} (ha : a ∈ I)
    (hfoc : HasDerivAt (fun b => ∑ j ∈ range (m + 1), p b j * v j - ψ b) 0 a) :
    ∀ b ∈ I, ∑ j ∈ range (m + 1), p b j * v j - ψ b ≤ ∑ j ∈ range (m + 1), p a j * v j - ψ a := by
  have hconc : ConcaveOn ℝ I (fun b => ∑ j ∈ range (m + 1), p b j * v j - ψ b) :=
    (expected_concave hI hsum hcdfc hv).sub hψ
  intro b hb
  rcases lt_trichotomy b a with hlt | heq | hgt
  · have := hconc.le_slope_of_hasDerivAt hb ha hlt hfoc
    rw [slope_def_field] at this
    have hpos : 0 < a - b := sub_pos.2 hlt
    have := (le_div_iff₀ hpos).1 this
    linarith
  · rw [heq]
  · have := hconc.slope_le_of_hasDerivAt ha hb hgt hfoc
    rw [slope_def_field] at this
    have hpos : 0 < b - a := sub_pos.2 hgt
    have := (div_le_iff₀ hpos).1 this
    linarith

/-- **Monotone wages under MLRP** (Mirrlees–Holmström): if `g = 1/u'` is strictly increasing
and `g (w j) = λ + μ · L j` with `μ ≥ 0` and `L` nondecreasing, wages are nondecreasing. -/
theorem mirrlees_monotone {g : ℝ → ℝ} (hg : StrictMono g) {w L : ℕ → ℝ} {lam μ : ℝ}
    (hμ : 0 ≤ μ) (hL : ∀ k, L k ≤ L (k + 1)) (hw : ∀ j, g (w j) = lam + μ * L j) (k : ℕ) :
    w k ≤ w (k + 1) := by
  rw [← hg.le_iff_le, hw, hw]
  nlinarith [hL k]

/-- **Rogerson (1985)**: under CDFC, a wage schedule satisfying the Mirrlees–Holmström
condition with `μ ≥ 0` and a nondecreasing `L` (standing in for MLRP) satisfies the agent's
global incentive constraint at any effort satisfying the first-order condition. -/
theorem rogerson {I : Set ℝ} (hI : Convex ℝ I) {p : ℝ → ℕ → ℝ} {m : ℕ}
    (hsum : ∀ a ∈ I, outputCDF (p a) m = 1)
    (hcdfc : ∀ k < m, ConvexOn ℝ I (fun a => outputCDF (p a) k)) {u : ℝ → ℝ} (hu : Monotone u)
    {g : ℝ → ℝ} (hg : StrictMono g) {w L : ℕ → ℝ} {lam μ : ℝ} (hμ : 0 ≤ μ)
    (hL : ∀ k, L k ≤ L (k + 1)) (hw : ∀ j, g (w j) = lam + μ * L j) {ψ : ℝ → ℝ}
    (hψ : ConvexOn ℝ I ψ) {a : ℝ} (ha : a ∈ I)
    (hfoc : HasDerivAt (fun b => ∑ j ∈ range (m + 1), p b j * u (w j) - ψ b) 0 a) :
    ∀ b ∈ I, ∑ j ∈ range (m + 1), p b j * u (w j) - ψ b ≤
      ∑ j ∈ range (m + 1), p a j * u (w j) - ψ a :=
  foa_valid hI hsum hcdfc (fun k => hu (mirrlees_monotone hg hμ hL hw k)) hψ ha hfoc

/-! ### Witness: two outcomes, success probability `a` -/

/-- Failure (`0`) with probability `1 − a`, success (`1`) with probability `a`. -/
noncomputable def coinP (a : ℝ) (j : ℕ) : ℝ := if j = 0 then 1 - a else if j = 1 then a else 0

/-- With utilities `0` after failure and `1/2` after success and cost `a²/2`, the first-order
condition at `a = 1/2` identifies the agent's optimum on `[0, 1]`. -/
example : ∀ b ∈ Icc (0 : ℝ) 1,
    ∑ j ∈ range 2, coinP b j * (if j = 0 then 0 else 1 / 2) - b ^ 2 / 2 ≤
      ∑ j ∈ range 2, coinP (1 / 2) j * (if j = 0 then 0 else 1 / 2) - (1 / 2) ^ 2 / 2 := by
  have hU : (fun b : ℝ => ∑ j ∈ range 2, coinP b j * (if j = 0 then 0 else 1 / 2) - b ^ 2 / 2) =
      fun b => b / 2 - b ^ 2 / 2 := by
    funext b; simp [sum_range_succ, coinP]; ring
  refine foa_valid (m := 1) (convex_Icc 0 1) (fun a _ => by simp [outputCDF, sum_range_succ, coinP])
    (fun k hk => ?_) (fun k => ?_) (by
      have h2 := ((convexOn_pow (𝕜 := ℝ) 2).subset Icc_subset_Ici_self (convex_Icc 0 1)).smul
        (c := (1 / 2 : ℝ)) (by norm_num)
      exact h2.congr fun x _ => by simp only [smul_eq_mul]; ring) (by norm_num) ?_
  · have hk0 : k = 0 := by omega
    subst hk0
    have : (fun a => outputCDF (coinP a) 0) = fun a => 1 - a := by
      funext a; simp [outputCDF, coinP]
    rw [this]
    exact (convexOn_const 1 (convex_Icc 0 1)).sub (concaveOn_id (convex_Icc 0 1))
  · rcases k with _ | k
    · norm_num
    · norm_num
  · rw [hU]
    have := ((hasDerivAt_id (1 / 2 : ℝ)).div_const 2).sub ((hasDerivAt_pow 2 (1 / 2 : ℝ)).div_const 2)
    convert this using 1
    · funext x; simp
    · norm_num

/-- Witness for `mirrlees_monotone`: `g = id`, `λ = 0`, `μ = 1/2`, `L = 1[j ≥ 1]` give the
wage schedule `0, 1/2, 1/2, …`. -/
example : ∀ k, (fun j : ℕ => if j = 0 then (0 : ℝ) else 1 / 2) k ≤
    (fun j : ℕ => if j = 0 then (0 : ℝ) else 1 / 2) (k + 1) :=
  mirrlees_monotone (g := id) strictMono_id (lam := 0) (μ := 1 / 2) (by norm_num)
    (L := fun j => if j = 0 then 0 else 1) (fun k => by split_ifs <;> simp_all)
    (fun j => by simp only [id]; split_ifs <;> norm_num)

end Econ
