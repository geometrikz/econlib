/-
# Stable VARs: the MA(∞) (Wold) representation and impulse responses

Hamilton, *Time Series Analysis* (1994), §10.1; Lütkepohl, *New Introduction to
Multiple Time Series Analysis* (2005), §2.1.1–2.1.2; Kilian and Lütkepohl (2017),
§2.2.

**The economics.** A VAR(1) `y_t = c + A y_{t−1} + u_t` (any VAR(p) in
companion form) is *stable* when the powers of `A` die out; for a matrix this is
"all eigenvalues inside the unit circle", which is equivalent to
`∑_j ‖A^j‖ < ∞`. Then:

* the mean `μ = (I − A)⁻¹ c = ∑_j A^j c` is the unique fixed point
  `μ = c + A μ` (`mean_fixed`, `fixed_unique`);
* for any bounded shock path, `y_t = μ + ∑_{j ≥ 0} A^j u_{t−j}` solves the
  VAR (`ma_isPath`) and is its **only bounded solution** (`isPath_unique`):
  this is the VAR's MA(∞)/Wold representation (Lütkepohl Prop. 2.1);
* the impulse response of `y_{s+h}` to a shock `v` at date `s` is `A^h v`
  (`ma_impulse`), and impulse responses vanish as `h → ∞`
  (`tendsto_irf_zero`).

**Encoding and scope.** `y_t` lives in a real Banach space `E` (e.g.
`EuclideanSpace ℝ (Fin k)`), `A : E →L[ℝ] E`, and time is `ℤ`. The statements
are pathwise (for every realisation of a bounded shock sequence), so they hold
almost surely for a.s. bounded shocks. Stability is assumed as summability of
`‖A^j‖`; `summable_of_norm_lt_one` derives it from `‖A‖ < 1`. The general Wold
decomposition of an arbitrary covariance-stationary process is not formalised.
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

namespace Econ.TimeSeries.VAR

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `y` is a path of the VAR(1) `y_t = c + A y_{t−1} + u_t`. -/
def IsPath (c : E) (A : E →L[ℝ] E) (u : ℤ → E) (y : ℤ → E) : Prop :=
  ∀ t, y t = c + A (y (t - 1)) + u t

/-- Stability: `∑_j ‖A^j‖ < ∞`. -/
def Stable (A : E →L[ℝ] E) : Prop :=
  Summable fun j : ℕ => ‖A ^ j‖

omit [CompleteSpace E] in
/-- `‖A‖ < 1` implies stability. -/
theorem summable_of_norm_lt_one {A : E →L[ℝ] E} (hA : ‖A‖ < 1) : Stable A := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    (summable_geometric_of_lt_one (norm_nonneg _) hA)
  rcases j with _ | j
  · rw [pow_zero]; exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' A (Nat.succ_pos j)

/-- Summability of `j ↦ A^j x_j` for a bounded sequence. -/
lemma summable_pow_apply {A : E →L[ℝ] E} (hA : Stable A) {x : ℕ → E} {M : ℝ}
    (hx : ∀ j, ‖x j‖ ≤ M) : Summable fun j => (A ^ j) (x j) := by
  refine Summable.of_norm_bounded (hA.mul_right M) fun j => ?_
  calc ‖(A ^ j) (x j)‖ ≤ ‖A ^ j‖ * ‖x j‖ := (A ^ j).le_opNorm _
    _ ≤ ‖A ^ j‖ * M := by gcongr; exact hx j

/-- The stationary mean `μ = ∑_j A^j c`. -/
noncomputable def mean (c : E) (A : E →L[ℝ] E) : E :=
  ∑' j : ℕ, (A ^ j) c

/-- The MA(∞) solution `y_t = μ + ∑_{j≥0} A^j u_{t−j}`. -/
noncomputable def ma (c : E) (A : E →L[ℝ] E) (u : ℤ → E) (t : ℤ) : E :=
  mean c A + ∑' j : ℕ, (A ^ j) (u (t - j))

/-- Splitting off the `j = 0` term: `∑_j A^j x_j = x_0 + A (∑_j A^j x_{j+1})`. -/
lemma tsum_pow_apply_eq {A : E →L[ℝ] E} (hA : Stable A) {x : ℕ → E} {M : ℝ}
    (hx : ∀ j, ‖x j‖ ≤ M) :
    ∑' j : ℕ, (A ^ j) (x j) = x 0 + A (∑' j : ℕ, (A ^ j) (x (j + 1))) := by
  rw [(summable_pow_apply hA hx).tsum_eq_zero_add, A.map_tsum (summable_pow_apply hA
    fun j => hx (j + 1))]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ']; rfl

/-- **The mean is a fixed point**: `μ = c + A μ`. -/
theorem mean_fixed {A : E →L[ℝ] E} (hA : Stable A) (c : E) :
    mean c A = c + A (mean c A) :=
  tsum_pow_apply_eq hA (x := fun _ => c) (M := ‖c‖) fun _ => le_rfl

/-- **The MA(∞) process solves the VAR** for any bounded shock path. -/
theorem ma_isPath {A : E →L[ℝ] E} (hA : Stable A) (c : E) {u : ℤ → E} {M : ℝ}
    (hu : ∀ t, ‖u t‖ ≤ M) : IsPath c A u (ma c A u) := by
  intro t
  have h := tsum_pow_apply_eq hA (x := fun j : ℕ => u (t - j)) (fun j => hu _)
  simp only [Nat.cast_zero, sub_zero, Nat.cast_succ] at h
  have : ∀ j : ℕ, t - (j + 1 : ℤ) = t - 1 - j := fun j => by ring
  simp only [this] at h
  rw [ma, ma, h, A.map_add]
  nth_rewrite 1 [mean_fixed hA c]
  abel

omit [CompleteSpace E] in
/-- The MA(∞) process is bounded. -/
theorem ma_bounded {A : E →L[ℝ] E} (hA : Stable A) (c : E) {u : ℤ → E} {M : ℝ}
    (hu : ∀ t, ‖u t‖ ≤ M) : ∃ K, ∀ t, ‖ma c A u t‖ ≤ K := by
  refine ⟨(∑' j, ‖A ^ j‖) * ‖c‖ + (∑' j, ‖A ^ j‖) * M, fun t => ?_⟩
  have hb : ∀ {x : ℕ → E} {N : ℝ}, (∀ j, ‖x j‖ ≤ N) →
      ‖∑' j, (A ^ j) (x j)‖ ≤ (∑' j, ‖A ^ j‖) * N := by
    intro x N hx
    have hle : ∀ j, ‖(A ^ j) (x j)‖ ≤ ‖A ^ j‖ * N := fun j =>
      ((A ^ j).le_opNorm _).trans (by gcongr; exact hx j)
    have hs : Summable fun j => ‖(A ^ j) (x j)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hA.mul_right N)
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    rw [← tsum_mul_right]
    exact hs.tsum_le_tsum hle (hA.mul_right N)
  exact (norm_add_le _ _).trans (add_le_add (hb (x := fun _ => c) fun _ => le_rfl)
    (hb fun j => hu _))

omit [CompleteSpace E] in
/-- Powers of a stable `A` tend to zero in norm. -/
lemma tendsto_norm_pow {A : E →L[ℝ] E} (hA : Stable A) :
    Tendsto (fun j : ℕ => ‖A ^ j‖) atTop (𝓝 0) :=
  hA.tendsto_atTop_zero

omit [CompleteSpace E] in
/-- **Uniqueness of the bounded solution** (Lütkepohl Prop. 2.1): any bounded
path of a stable VAR equals the MA(∞) process. -/
theorem isPath_unique {A : E →L[ℝ] E} (hA : Stable A) {c : E} {u : ℤ → E} {y z : ℤ → E}
    (hy : IsPath c A u y) (hz : IsPath c A u z) {K : ℝ} (hyb : ∀ t, ‖y t‖ ≤ K)
    {K' : ℝ} (hzb : ∀ t, ‖z t‖ ≤ K') : y = z := by
  set d := fun t => y t - z t
  have hd : ∀ t, d t = A (d (t - 1)) := fun t => by
    simp only [d]; rw [hy t, hz t, A.map_sub]; abel
  have hdn : ∀ (n : ℕ) t, d t = (A ^ n) (d (t - n)) := by
    intro n; induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [ih t, hd (t - n), pow_succ]
      show _ = (A ^ n) (A (d (t - (n + 1 : ℕ))))
      congr 3; push_cast; ring
  funext t
  have hle : ∀ n : ℕ, ‖d t‖ ≤ ‖A ^ n‖ * (K + K') := by
    intro n
    rw [hdn n t]
    have hdb : ‖d (t - n)‖ ≤ K + K' := (norm_sub_le _ _).trans (add_le_add (hyb _) (hzb _))
    exact ((A ^ n).le_opNorm _).trans (by gcongr)
  have hlim : Tendsto (fun n : ℕ => ‖A ^ n‖ * (K + K')) atTop (𝓝 0) := by
    simpa using (tendsto_norm_pow hA).mul_const (K + K')
  have : ‖d t‖ ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hle)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- The mean is the unique fixed point of `x ↦ c + A x`. -/
theorem fixed_unique {A : E →L[ℝ] E} (hA : Stable A) {c x : E} (hx : x = c + A x) :
    x = mean c A := by
  have := isPath_unique hA (u := 0) (y := fun _ => x) (z := fun _ => mean c A)
    (fun t => by simpa using hx) (fun t => by simpa using mean_fixed hA c)
    (K := ‖x‖) (fun _ => le_rfl) (K' := ‖mean c A‖) (fun _ => le_rfl)
  exact congrFun this 0

/-- **Impulse responses** (Lütkepohl §2.3.2): adding a one-time shock `v` at date
`s` to a bounded shock path changes the MA(∞) path at date `s + h` by `A^h v`
(and not at all before `s`). -/
theorem ma_impulse {A : E →L[ℝ] E} (hA : Stable A) (c : E) {u : ℤ → E} {M : ℝ}
    (hu : ∀ t, ‖u t‖ ≤ M) (s : ℤ) (v : E) (h : ℕ) :
    ma c A (fun t => u t + if t = s then v else 0) (s + h) - ma c A u (s + h) = (A ^ h) v := by
  have hb : ∀ t, ‖u t + (if t = s then v else 0)‖ ≤ M + ‖v‖ := fun t => by
    refine (norm_add_le _ _).trans (add_le_add (hu t) ?_)
    split_ifs <;> simp
  rw [ma, ma, add_sub_add_left_eq_sub, ← (summable_pow_apply hA fun j => hb _).tsum_sub
    (summable_pow_apply hA fun j => hu _)]
  simp only [map_add, add_sub_cancel_left]
  rw [tsum_eq_single h]
  · simp
  · intro j hj
    have : (s : ℤ) + h - j ≠ s := by omega
    simp [this]

omit [CompleteSpace E] in
/-- Impulse responses die out: `A^h v → 0`. -/
theorem tendsto_irf_zero {A : E →L[ℝ] E} (hA : Stable A) (v : E) :
    Tendsto (fun h : ℕ => (A ^ h) v) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun h => (A ^ h).le_opNorm v) ?_
  simpa using (tendsto_norm_pow hA).mul_const ‖v‖

end Econ.TimeSeries.VAR
