/-
# Strong risk aversion under general rank-dependent utility

References. S. Chew, E. Karni and Z. Safra (1987), "Risk Aversion in the
Theory of Expected Utility with Rank Dependent Probabilities", *JET* 42(2);
J. Quiggin (1993), *Generalized Expected Utility Theory*, ch. 6; M. Rothschild
and J. Stiglitz (1970), "Increasing Risk I"; M. Tomić (1949) and H. Weyl (1949)
on weak majorization.

Builds on `RDUStrongRiskAversion.lean`, which treats linear utility of money
(Yaari). Here utility of money `U : ℝ → ℝ` is general and the RDU value of a
lottery `p` on the outcome grid `x` is `rdu w (fun k => U (x k)) p`.

**Results.**
* `fuchs_mono` (**Tomić–Weyl, weighted**): for `f` convex *and increasing* on
  `I`, Fuchs' inequality holds without the condition that the total weighted sum
  vanish: nonnegative partial sums of `c (x − y)` alone give
  `Σ c (f x − f y) ≥ 0` (weights `c` of any sign; `x`, `y` decreasing in `I`).
* `SSD x q p`: on the grid `x`, every partial integral of the decumulative
  distribution of `q` is at most that of `p`,
  `Σ_{k<m} G q (k+1) Δx_k ≤ Σ_{k<m} G p (k+1) Δx_k`. On a weakly increasing grid
  this is second-order stochastic dominance of `p` over `q` (the increasing
  concave order). `IsMPS` unfolds to equal means ∧ `SSD`; `isMPS_ssd`
  extracts the `SSD` part. Grids here may be weakly increasing (repeated grid
  points contribute zero `Δx` terms).
* `ssd_weighted`: with `w` convex and increasing on `[0, 1]`, `SSD` survives
  the probability distortion: the partial sums of `w (G q (k+1)) Δx_k` are at
  most those of `w (G p (k+1)) Δx_k`.
* `cks_ssd` and `cks_mps` (**Chew–Karni–Safra 1987, sufficiency**): if `U` is
  concave and increasing on a set containing a weakly increasing grid and `w` is
  convex and increasing on `[0, 1]` with `w 0 = 0`, `w 1 = 1`, then RDU never
  increases when `p` is replaced by a lottery it dominates in `SSD`, in
  particular by any mean-preserving spread of `p`: the agent is strongly risk
  averse. Monotonicity of `w` is a standing assumption of Chew–Karni–Safra; it
  cannot be dropped once `U` is nonlinear (unlike `yaari_mps`, linear `U`).
* Non-vacuity: `sqrt_sq_mps` (`U = √`, `w t = t²`) and `sqrt_sq_tri`, a
  concrete spread on the grid `(0, 1/2, 1)`; `sq_tri_strict`, where expected
  value is unchanged by that spread but the distortion `w t = t²` alone makes
  the agent strictly prefer the sure outcome (value `1/4 < 1/2`).

**Scope.** Only the sufficiency half of Chew–Karni–Safra is formalized. Its
necessity half (strong risk aversion forces `U` concave and `w` convex, which
in the original uses differentiability) is not; for linear `U` the converse is
`yaari_strongRiskAverse_iff`.
-/
module

public import EconLean.Behavioral.RDUStrongRiskAversion
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

namespace Econ

namespace RankDependent

open Finset

/-- Chord slopes of a function increasing on `I` are nonnegative. -/
theorem slope_nonneg_of_monotoneOn {f : ℝ → ℝ} {I : Set ℝ} (hf : MonotoneOn f I) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) : 0 ≤ slope f a b := by
  rw [slope_def_field]
  rcases le_total a b with h | h
  · exact div_nonneg (sub_nonneg.2 (hf ha hb h)) (sub_nonneg.2 h)
  · exact div_nonneg_of_nonpos (sub_nonpos.2 (hf hb ha h)) (sub_nonpos.2 h)

/-- `slope f a b * (b - a) = f b - f a`, including the degenerate case `a = b`. -/
theorem slope_mul_sub (f : ℝ → ℝ) (a b : ℝ) : slope f a b * (b - a) = f b - f a := by
  rw [slope_def_field]
  by_cases h : b - a = 0
  · have : b = a := sub_eq_zero.1 h
    subst this; simp
  · field_simp

/-- **Weighted Tomić–Weyl inequality**: Fuchs' inequality for an increasing
convex function needs only nonnegative partial sums, not a zero total. -/
theorem fuchs_mono {f : ℝ → ℝ} {I : Set ℝ} (hf : ConvexOn ℝ I f) (hfm : MonotoneOn f I)
    (n : ℕ) {c x y : ℕ → ℝ}
    (hxI : ∀ k < n, x k ∈ I) (hyI : ∀ k < n, y k ∈ I)
    (hx : ∀ j k, j < k → k < n → x k ≤ x j) (hy : ∀ j k, j < k → k < n → y k ≤ y j)
    (hP : ∀ m ≤ n, 0 ≤ ∑ k ∈ range m, c k * (x k - y k)) :
    0 ≤ ∑ k ∈ range n, c k * (f (x k) - f (y k)) := by
  set a : ℕ → ℝ := fun k => c k * (x k - y k)
  set s : ℕ → ℝ := fun k => slope f (y k) (x k)
  have hsa : ∀ k, c k * (f (x k) - f (y k)) = s k * a k := fun k => by
    show c k * (f (x k) - f (y k)) = slope f (y k) (x k) * (c k * (x k - y k))
    rw [mul_left_comm, slope_mul_sub]
  have hne : ∀ k, a k ≠ 0 → x k ≠ y k := fun k hk e => hk (by simp [a, e])
  have hmono : ∀ j k, j < k → k < n → a j ≠ 0 → a k ≠ 0 → s k ≤ s j := by
    intro j k hjk hk hj hk'
    exact slope_le_slope hf (hxI j (by omega)) (hyI j (by omega)) (hxI k hk) (hyI k hk)
      (hx j k hjk hk) (hy j k hjk hk) (hne j hj) (hne k hk')
  have hσ : ∀ k < n, a k ≠ 0 → (0 : ℝ) ≤ s k := fun k hk _ =>
    slope_nonneg_of_monotoneOn hfm (hyI k hk) (hxI k hk)
  have := abel_support a s n 0 hP hmono hσ
  rw [zero_mul] at this
  rw [sum_congr rfl fun k _ => hsa k]
  exact this

variable {n : ℕ}

/-- `p` dominates `q` in the **increasing concave order** on the grid `x`
(second-order stochastic dominance, integral condition at the grid points). -/
def SSD (x : ℕ → ℝ) (q p : Lottery n) : Prop :=
  ∀ m ≤ n,
    ∑ k ∈ range m, G q (k + 1) * (x (k + 1) - x k) ≤ ∑ k ∈ range m, G p (k + 1) * (x (k + 1) - x k)

theorem isMPS_ssd {x : ℕ → ℝ} {p q : Lottery n} (h : IsMPS x q p) : SSD x q p := h.2

/-- A convex increasing distortion of the decumulative distribution preserves
second-order dominance. -/
theorem ssd_weighted {w : ℝ → ℝ} (hw : ConvexOn ℝ (Set.Icc 0 1) w)
    (hwm : MonotoneOn w (Set.Icc 0 1)) {x : ℕ → ℝ} {p q : Lottery n} (h : SSD x q p) :
    ∀ m ≤ n, ∑ k ∈ range m, w (G q (k + 1)) * (x (k + 1) - x k) ≤
      ∑ k ∈ range m, w (G p (k + 1)) * (x (k + 1) - x k) := by
  intro m hm
  have := fuchs_mono hw hwm m (c := fun k => x (k + 1) - x k) (x := fun k => G p (k + 1))
    (y := fun k => G q (k + 1))
    (fun k _ => ⟨G_nonneg _ _, G_le_one _ _⟩) (fun k _ => ⟨G_nonneg _ _, G_le_one _ _⟩)
    (fun j k hjk _ => G_antitone p (by omega)) (fun j k hjk _ => G_antitone q (by omega))
    (fun m' hm' => by
      have := h m' (by omega)
      rw [← sub_nonneg, ← sum_sub_distrib] at this
      exact this.trans_eq (sum_congr rfl fun k _ => by ring))
  rw [← sub_nonneg, ← sum_sub_distrib]
  exact this.trans_eq (sum_congr rfl fun k _ => by ring)

theorem monotoneOnGrid_le {x : ℕ → ℝ} (hx : MonotoneOnGrid n x) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) : x i ≤ x j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hx j (by omega))
    · rw [le_antisymm hij h]

/-- **Chew–Karni–Safra, sufficiency** (second-order dominance form): concave
increasing utility of money and convex increasing probability weighting make RDU
monotone in the increasing concave order. -/
theorem cks_ssd {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw : ConvexOn ℝ (Set.Icc 0 1) w) (hwm : MonotoneOn w (Set.Icc 0 1))
    {U : ℝ → ℝ} {I : Set ℝ} (hU : ConcaveOn ℝ I U) (hUm : MonotoneOn U I)
    {x : ℕ → ℝ} (hxI : ∀ k ≤ n, x k ∈ I) (hx : MonotoneOnGrid n x)
    {p q : Lottery n} (h : SSD x q p) :
    rdu w (fun k => U (x k)) q ≤ rdu w (fun k => U (x k)) p := by
  rw [rdu_eq_layer hw0 hw1, rdu_eq_layer hw0 hw1, add_le_add_iff_left]
  set a : ℕ → ℝ := fun k => (w (G p (k + 1)) - w (G q (k + 1))) * (x (k + 1) - x k)
  set s : ℕ → ℝ := fun k => slope U (x k) (x (k + 1))
  have hsa : ∀ k, (w (G p (k + 1)) - w (G q (k + 1))) * (U (x (k + 1)) - U (x k)) =
      s k * a k := fun k => by
    show _ = slope U (x k) (x (k + 1)) * ((w (G p (k + 1)) - w (G q (k + 1))) * (x (k + 1) - x k))
    rw [mul_left_comm, slope_mul_sub]
  have hP : ∀ m ≤ n, 0 ≤ ∑ k ∈ range m, a k := fun m hm => by
    have := ssd_weighted hw hwm h m hm
    rw [← sub_nonneg, ← sum_sub_distrib] at this
    exact this.trans_eq (sum_congr rfl fun k _ => by simp only [a]; ring)
  have hne : ∀ k, a k ≠ 0 → x k ≠ x (k + 1) := fun k hk e => hk (by simp [a, e])
  have hmono : ∀ j k, j < k → k < n → a j ≠ 0 → a k ≠ 0 → s k ≤ s j := by
    intro j k hjk hk hj hk'
    have h1 := slope_le_slope hU.neg (hxI (k + 1) (by omega)) (hxI k (by omega))
      (hxI (j + 1) (by omega)) (hxI j (by omega))
      (monotoneOnGrid_le hx (by omega) (by omega)) (monotoneOnGrid_le hx (by omega) (by omega))
      (Ne.symm (hne k hk')) (Ne.symm (hne j hj))
    have e : ∀ u v, slope (-U) u v = -slope U u v := fun u v => by
      rw [slope_def_field, slope_def_field]; simp only [Pi.neg_apply]; ring
    rw [e, e] at h1
    show slope U (x k) (x (k + 1)) ≤ slope U (x j) (x (j + 1))
    linarith
  have hσ : ∀ k < n, a k ≠ 0 → (0 : ℝ) ≤ s k := fun k hk _ =>
    slope_nonneg_of_monotoneOn hUm (hxI k (by omega)) (hxI (k + 1) (by omega))
  have := abel_support a s n 0 hP hmono hσ
  rw [zero_mul] at this
  rw [← sub_nonneg, ← sum_sub_distrib]
  exact this.trans_eq (sum_congr rfl fun k _ => by rw [← hsa]; ring)

/-- **Chew–Karni–Safra, sufficiency**: an RDU agent with concave increasing
utility and convex increasing weighting is averse to every mean-preserving
spread on a weakly increasing grid. -/
theorem cks_mps {w : ℝ → ℝ} (hw0 : w 0 = 0) (hw1 : w 1 = 1)
    (hw : ConvexOn ℝ (Set.Icc 0 1) w) (hwm : MonotoneOn w (Set.Icc 0 1))
    {U : ℝ → ℝ} {I : Set ℝ} (hU : ConcaveOn ℝ I U) (hUm : MonotoneOn U I)
    {x : ℕ → ℝ} (hxI : ∀ k ≤ n, x k ∈ I) (hx : MonotoneOnGrid n x)
    {p q : Lottery n} (h : IsMPS x q p) :
    rdu w (fun k => U (x k)) q ≤ rdu w (fun k => U (x k)) p :=
  cks_ssd hw0 hw1 hw hwm hU hUm hxI hx (isMPS_ssd h)

theorem sq_monotoneOn : MonotoneOn (fun t : ℝ => t ^ 2) (Set.Icc 0 1) :=
  fun _ ha _ _ hab => pow_le_pow_left₀ ha.1 hab 2

/-- Non-vacuity: square-root utility with `w t = t²` on any nonnegative weakly
increasing grid. -/
theorem sqrt_sq_mps {x : ℕ → ℝ} (hx0 : ∀ k ≤ n, 0 ≤ x k) (hx : MonotoneOnGrid n x)
    {p q : Lottery n} (h : IsMPS x q p) :
    rdu (fun t => t ^ 2) (fun k => Real.sqrt (x k)) q ≤
      rdu (fun t => t ^ 2) (fun k => Real.sqrt (x k)) p :=
  cks_mps (by norm_num) (by norm_num) sq_convex sq_monotoneOn
    Real.strictConcaveOn_sqrt.concaveOn (fun _ _ _ _ hab => Real.sqrt_le_sqrt hab)
    (I := Set.Ici 0) hx0 hx h

/-- A concrete instance: on the grid `(0, 1/2, 1)`, spreading the lottery with
`Prob(≥ 1/2) = 1`, `Prob(= 1) = 0` (sure `1/2`) to the even coin on `{0, 1}`
lowers the RDU value with `U = √`, `w t = t²`. -/
theorem sqrt_sq_tri :
    rdu (fun t => t ^ 2) (fun k => Real.sqrt ((fun k : ℕ => if k = 0 then 0 else if k = 1 then
        (1 / 2 : ℝ) else 1) k))
        (triLot (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)) ≤
      rdu (fun t => t ^ 2) (fun k => Real.sqrt ((fun k : ℕ => if k = 0 then 0 else if k = 1 then
        (1 / 2 : ℝ) else 1) k))
        (triLot 1 0 le_rfl (by norm_num) le_rfl) := by
  have h := isMPS_tri (t := 1) (s := 0) (l := 1 / 2) le_rfl (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have e : (1 / 2 : ℝ) * 1 + (1 - 1 / 2) * 0 = 1 / 2 := by norm_num
  simp only [e] at h
  refine sqrt_sq_mps (fun k _ => ?_) (fun k hk => ?_) h
  · split_ifs <;> norm_num
  · interval_cases k <;> norm_num

/-- The distortion matters: on the grid `(0, 1/2, 1)` with linear utility the
spread leaves the mean unchanged, but `w t = t²` values the even coin at `1/4`
and the sure `1/2` at `1/2`. -/
theorem sq_tri_strict :
    let x : ℕ → ℝ := fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else 1
    eu x (triLot (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)) =
        eu x (triLot 1 0 le_rfl (by norm_num) le_rfl) ∧
      rdu (fun t => t ^ 2) x (triLot (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)) = 1 / 4 ∧
      rdu (fun t => t ^ 2) x (triLot 1 0 le_rfl (by norm_num) le_rfl) = 1 / 2 := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · rw [eu_eq_layer, eu_eq_layer]
    simp [x, sum_range_succ, G_triLot_one, G_triLot_two]; norm_num
  · rw [rdu_eq_layer (by norm_num) (by norm_num)]
    simp [x, sum_range_succ, G_triLot_one, G_triLot_two]; norm_num
  · rw [rdu_eq_layer (by norm_num) (by norm_num)]
    simp [x, sum_range_succ, G_triLot_one, G_triLot_two]

end RankDependent

end Econ
