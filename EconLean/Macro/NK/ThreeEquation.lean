/-
# The New Keynesian three-equation model: determinacy and the Taylor principle

Galí, *Monetary Policy, Inflation, and the Business Cycle*, ch. 3–4;
Woodford, *Interest and Prices*, ch. 4; Blanchard–Kahn (1980);
Bullard–Mitra (2002).

**Blanchard–Kahn for two jump variables.** Write a linear perfect-foresight
system as `z_{t+1} = M z_t` with `z_t ∈ ℝ²` and no predetermined variable.
The system is **determinate** if its only bounded solution is `z = 0`
(`Determinate`). `determinate_iff` proves, for `det M > 0`, that this holds iff
`1 < det M` and `|tr M| < 1 + det M`. These are the Schur–Cohn conditions for
both eigenvalues of `M` to lie outside the unit circle, i.e. the Blanchard–Kahn
condition that the number of unstable roots equals the number of jump
variables. The proof treats complex roots with the invariant quadratic form
`Q(z) = det[z, Mz]`, which satisfies `Q(Mz) = det M · Q(z)`, and real roots
with eigenvectors.

**The model** (deviations from steady state, no shocks):
* dynamic IS curve `x_t = x_{t+1} − (i_t − π_{t+1})/σ`;
* New Keynesian Phillips curve `π_t = β π_{t+1} + κ x_t`;
* Taylor rule `i_t = φ_π π_t + φ_x x_t`.

**Result.** `taylor_principle`: with `σ, κ > 0`, `β ∈ (0,1)` and
`φ_π, φ_x ≥ 0`, the model is determinate iff
`κ (φ_π − 1) + (1 − β) φ_x > 0`. With `φ_x = 0` this is the Taylor
principle `φ_π > 1` (`taylor_principle_strict`).

**Deviations.** Perfect foresight with no shocks; determinacy means uniqueness
of the bounded solution of the homogeneous system, which is the condition that
decides uniqueness of the bounded rational-expectations solution when shocks
are added. The general Blanchard–Kahn lemma is proved for `2 × 2` systems with
positive determinant (the NK case).
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

namespace Econ
namespace NK

open Matrix

/-! ### Blanchard–Kahn for a `2 × 2` forward map -/

/-- `z` solves the forward system `z_{t+1} = M z_t`. -/
def IsOrbit (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℕ → Fin 2 → ℝ) : Prop := ∀ t, z (t + 1) = M *ᵥ z t

/-- `z` is bounded. -/
def Bounded (z : ℕ → Fin 2 → ℝ) : Prop := ∃ B, ∀ t i, |z t i| ≤ B

/-- **Determinacy:** the only bounded solution is zero. -/
def Determinate (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ z, IsOrbit M z → Bounded z → ∀ t, z t = 0

section BK

variable (M : Matrix (Fin 2) (Fin 2) ℝ)

theorem mulVec_zero' (v : Fin 2 → ℝ) : (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_one' (v : Fin 2 → ℝ) : (M *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- Cayley–Hamilton for `2 × 2` matrices, applied to a vector. -/
theorem cayley_hamilton (v : Fin 2 → ℝ) (i : Fin 2) :
    (M *ᵥ (M *ᵥ v)) i = M.trace * (M *ᵥ v) i - M.det * v i := by
  fin_cases i <;> simp [mulVec_zero', mulVec_one', det_fin_two, trace_fin_two] <;> ring

/-- A geometric sequence with ratio `|r| > 1` is bounded only if it is zero. -/
theorem eq_zero_of_geom {r x C : ℝ} (hr : 1 < |r|) (h : ∀ t : ℕ, |r ^ t * x| ≤ C) : x = 0 := by
  by_contra hx
  have hx' : 0 < |x| := abs_pos.2 hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / |x|) hr
  have := h n
  rw [abs_mul, abs_pow] at this
  rw [div_lt_iff₀ hx'] at hn
  linarith

theorem orbit_eq_zero {z : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (h0 : z 0 = 0) : ∀ t, z t = 0 := by
  intro t; induction t with
  | zero => exact h0
  | succ t ih => rw [hz, ih, mulVec_zero]

theorem bound_mulVec {v : Fin 2 → ℝ} {B : ℝ} (hv : ∀ i, |v i| ≤ B) (i : Fin 2) :
    |(M *ᵥ v) i| ≤ (|M i 0| + |M i 1|) * B := by
  have e : (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 := by
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  rw [e]
  calc |M i 0 * v 0 + M i 1 * v 1| ≤ |M i 0| * |v 0| + |M i 1| * |v 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |M i 0| * B + |M i 1| * B := by gcongr <;> exact hv _
    _ = _ := by ring

/-- **Real roots, both unstable.** If `μ₁ + μ₂ = tr M`, `μ₁ μ₂ = det M` and
`|μ₁|, |μ₂| > 1`, every bounded solution is zero. -/
theorem zero_of_real {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : 1 < |μ₁|) (h₂ : 1 < |μ₂|) {z : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (hb : Bounded z) :
    ∀ t, z t = 0 := by
  obtain ⟨B, hB⟩ := hb
  -- `p_t = (M − μ₁) z_t` grows like `μ₂^t`
  set p : ℕ → Fin 2 → ℝ := fun t i => (M *ᵥ z t) i - μ₁ * z t i
  have hstep : ∀ t i, p (t + 1) i = μ₂ * p t i := fun t i => by
    simp only [p, hz t, cayley_hamilton, ← hs, ← hp]; ring
  have hgeom : ∀ t i, p t i = μ₂ ^ t * p 0 i := fun t i => by
    induction t with
    | zero => simp
    | succ t ih => rw [hstep, ih, pow_succ]; ring
  have hp0 : ∀ i, p 0 i = 0 := fun i => by
    refine eq_zero_of_geom h₂ (C := (|M i 0| + |M i 1|) * B + |μ₁| * B) fun t => ?_
    rw [← hgeom]
    calc |p t i| ≤ |(M *ᵥ z t) i| + |μ₁ * z t i| := abs_sub _ _
      _ ≤ _ := add_le_add ((bound_mulVec M) (hB t) i)
          (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB t i) (abs_nonneg _))
  -- hence `z_{t+1} = μ₁ z_t`
  have hz1 : ∀ t i, z t i = μ₁ ^ t * z 0 i := fun t i => by
    induction t with
    | zero => simp
    | succ t ih =>
      have := hgeom t i
      rw [hp0, mul_zero] at this
      simp only [p, sub_eq_zero] at this
      rw [hz t, this, ih, pow_succ]; ring
  have h0 : z 0 = 0 := funext fun i =>
    eq_zero_of_geom h₁ (C := B) fun t => by rw [← hz1]; exact hB t i
  exact (orbit_eq_zero M) hz h0

/-- An eigenvector for any real root of the characteristic polynomial. -/
theorem exists_eigenvector {μ : ℝ} (hμ : μ ^ 2 - M.trace * μ + M.det = 0) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [det_fin_two, trace_fin_two] at hμ
  by_cases h : M 0 1 = 0 ∧ M 0 0 - μ = 0
  · by_cases h' : M 1 0 = 0 ∧ M 1 1 - μ = 0
    · refine ⟨![1, 0], by simp [funext_iff], funext fun i => ?_⟩
      fin_cases i <;> simp [mulVec_zero', mulVec_one'] <;> linarith [h.1, h.2, h'.1, h'.2]
    · refine ⟨![M 1 1 - μ, -M 1 0], fun hv => h' ?_, funext fun i => ?_⟩
      · have a := congrFun hv 0; have b := congrFun hv 1
        simp at a b; exact ⟨b, a⟩
      · fin_cases i <;> simp [mulVec_zero', mulVec_one'] <;>
          nlinarith [h.1, h.2]
  · refine ⟨![M 0 1, -(M 0 0 - μ)], fun hv => h ?_, funext fun i => ?_⟩
    · have a := congrFun hv 0; have b := congrFun hv 1
      simp at a b; exact ⟨a, by linarith⟩
    · fin_cases i <;> simp [mulVec_zero', mulVec_one'] <;> nlinarith

/-- The invariant quadratic form `Q(z) = det[z, Mz]`. -/
def Q (v : Fin 2 → ℝ) : ℝ := M 1 0 * v 0 ^ 2 + (M 1 1 - M 0 0) * v 0 * v 1 - M 0 1 * v 1 ^ 2

theorem Q_mulVec (v : Fin 2 → ℝ) : (Q M) (M *ᵥ v) = M.det * (Q M) v := by
  simp only [Q, mulVec_zero', mulVec_one', det_fin_two]; ring

theorem Q_orbit {z : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (t : ℕ) : (Q M) (z t) = M.det ^ t * (Q M) (z 0) := by
  induction t with
  | zero => simp
  | succ t ih => rw [hz, Q_mulVec, ih, pow_succ]; ring

/-- Completing the square: `4 a Q = (2 a x + b y)² − Δ y²` with `Δ = tr² − 4 det`. -/
theorem Q_square₁ (v : Fin 2 → ℝ) :
    4 * M 1 0 * (Q M) v = (2 * M 1 0 * v 0 + (M 1 1 - M 0 0) * v 1) ^ 2 -
      (M.trace ^ 2 - 4 * M.det) * v 1 ^ 2 := by
  simp only [Q, det_fin_two, trace_fin_two]; ring

theorem Q_square₂ (v : Fin 2 → ℝ) :
    -4 * M 0 1 * (Q M) v = (-2 * M 0 1 * v 1 + (M 1 1 - M 0 0) * v 0) ^ 2 -
      (M.trace ^ 2 - 4 * M.det) * v 0 ^ 2 := by
  simp only [Q, det_fin_two, trace_fin_two]; ring

/-- With complex roots, `Q` controls the size of `v`. -/
theorem sq_le_Q (v : Fin 2 → ℝ) :
    -(M.trace ^ 2 - 4 * M.det) * v 1 ^ 2 ≤ 4 * |M 1 0| * |(Q M) v| ∧
      -(M.trace ^ 2 - 4 * M.det) * v 0 ^ 2 ≤ 4 * |M 0 1| * |(Q M) v| := by
  have h1 := (Q_square₁ M) v
  have h2 := (Q_square₂ M) v
  constructor
  · have : 4 * M 1 0 * (Q M) v ≤ 4 * |M 1 0| * |(Q M) v| := by
      rw [mul_assoc, mul_assoc, ← abs_mul]
      nlinarith [le_abs_self (M 1 0 * (Q M) v)]
    nlinarith [sq_nonneg (2 * M 1 0 * v 0 + (M 1 1 - M 0 0) * v 1)]
  · have : -4 * M 0 1 * (Q M) v ≤ 4 * |M 0 1| * |(Q M) v| := by
      rw [mul_assoc, mul_assoc, ← abs_mul]
      nlinarith [neg_abs_le (M 0 1 * (Q M) v)]
    nlinarith [sq_nonneg (-2 * M 0 1 * v 1 + (M 1 1 - M 0 0) * v 0)]

theorem Q_eq_zero (hΔ : M.trace ^ 2 - 4 * M.det < 0) {v : Fin 2 → ℝ} (h : (Q M) v = 0) : v = 0 := by
  obtain ⟨h1, h0⟩ := (sq_le_Q M) v
  rw [h, abs_zero, mul_zero] at h1 h0
  have hp : 0 < -(M.trace ^ 2 - 4 * M.det) := by linarith
  have a : v 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm (by nlinarith [sq_nonneg (v 0)]) (sq_nonneg _))
  have b : v 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm (by nlinarith [sq_nonneg (v 1)]) (sq_nonneg _))
  funext i; fin_cases i <;> simp [a, b]

/-- The orbit started at `v`. -/
def orbit (v : Fin 2 → ℝ) : ℕ → Fin 2 → ℝ
  | 0 => v
  | t + 1 => M *ᵥ orbit v t

theorem isOrbit_orbit (v : Fin 2 → ℝ) : IsOrbit M ((orbit M) v) := fun _ => rfl

/-- **Schur–Cohn for real roots.** With `μ₁ μ₂ > 0`, both roots lie outside the
unit circle iff `1 < μ₁ μ₂` and `|μ₁ + μ₂| < 1 + μ₁ μ₂`. -/
theorem roots_outside_iff {μ₁ μ₂ : ℝ} (hD : 0 < μ₁ * μ₂) :
    (1 < |μ₁| ∧ 1 < |μ₂|) ↔ (1 < μ₁ * μ₂ ∧ |μ₁ + μ₂| < 1 + μ₁ * μ₂) := by
  rcases lt_or_gt_of_ne (show μ₁ ≠ 0 by rintro rfl; simp at hD) with h1 | h1
  · have h2 : μ₂ < 0 := by nlinarith
    rw [abs_of_neg h1, abs_of_neg h2, abs_of_neg (by linarith)]
    constructor
    · rintro ⟨a, b⟩; constructor <;> nlinarith
    · rintro ⟨a, b⟩
      by_contra hc
      rcases not_and_or.1 hc with c | c <;> push Not at c <;> nlinarith
  · have h2 : 0 < μ₂ := by nlinarith
    rw [abs_of_pos h1, abs_of_pos h2, abs_of_pos (by linarith)]
    constructor
    · rintro ⟨a, b⟩; constructor <;> nlinarith
    · rintro ⟨a, b⟩
      by_contra hc
      rcases not_and_or.1 hc with c | c <;> push Not at c <;> nlinarith

/-- **Blanchard–Kahn for a `2 × 2` system with positive determinant.** The
only bounded solution of `z_{t+1} = M z_t` is zero iff both eigenvalues of `M`
lie outside the unit circle, i.e. iff `1 < det M` and `|tr M| < 1 + det M`. -/
theorem determinate_iff (hD : 0 < M.det) :
    Determinate M ↔ 1 < M.det ∧ |M.trace| < 1 + M.det := by
  set T := M.trace
  set D := M.det
  by_cases hΔ : T ^ 2 - 4 * D < 0
  · -- complex roots: Jury reduces to `D > 1`
    have hT : 1 < D → |T| < 1 + D := fun h => by
      rw [abs_lt]; constructor <;> nlinarith
    constructor
    · intro hdet
      by_contra hc
      have hD1 : D ≤ 1 := by
        by_contra h; push Not at h; exact hc ⟨h, hT h⟩
      -- the orbit from `e₀` stays bounded
      set e : Fin 2 → ℝ := ![1, 0]
      set q := |(Q M) e|
      have hq : ∀ t, |(Q M) ((orbit M) e t)| ≤ q := fun t => by
        rw [(Q_orbit M) ((isOrbit_orbit M) e), abs_mul, abs_pow, abs_of_pos hD]
        exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hD.le hD1)
      have hb : Bounded ((orbit M) e) := by
        refine ⟨1 + 4 * (|M 1 0| + |M 0 1|) * q / -(T ^ 2 - 4 * D), fun t i => ?_⟩
        obtain ⟨h1, h0⟩ := (sq_le_Q M) ((orbit M) e t)
        have hpos : 0 < -(T ^ 2 - 4 * D) := by linarith
        have hqt := hq t
        have hab : ∀ x : ℝ, |x| ≤ 1 + x ^ 2 := fun x => by
          nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
        refine (hab _).trans ((add_le_add_iff_left 1).2 ?_)
        rw [le_div_iff₀ hpos]
        fin_cases i
        · simp only [Fin.zero_eta]
          nlinarith [abs_nonneg (M 1 0), abs_nonneg (M 0 1), abs_nonneg ((Q M) ((orbit M) e t))]
        · simp only [Fin.mk_one]
          nlinarith [abs_nonneg (M 1 0), abs_nonneg (M 0 1), abs_nonneg ((Q M) ((orbit M) e t))]
      have := congrFun (hdet _ ((isOrbit_orbit M) e) hb 0) 0
      simp [orbit, e] at this
    · rintro ⟨hD1, -⟩ z hz ⟨B, hB⟩
      apply (orbit_eq_zero M) hz
      apply (Q_eq_zero M) hΔ
      refine eq_zero_of_geom (r := D) (by rwa [abs_of_pos hD])
        (C := (|M 1 0| + |M 1 1 - M 0 0| + |M 0 1|) * B ^ 2) fun t => ?_
      rw [← (Q_orbit M) hz]
      have h0 := hB t 0
      have h1 := hB t 1
      have hB0 : 0 ≤ B := (abs_nonneg _).trans h0
      simp only [Q]
      calc |M 1 0 * z t 0 ^ 2 + (M 1 1 - M 0 0) * z t 0 * z t 1 - M 0 1 * z t 1 ^ 2|
          ≤ |M 1 0| * |z t 0| ^ 2 + |M 1 1 - M 0 0| * (|z t 0| * |z t 1|) +
              |M 0 1| * |z t 1| ^ 2 := by
            rw [← abs_pow, ← abs_pow, ← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul, mul_assoc]
            exact (abs_sub _ _).trans ((add_le_add_iff_right _).2 (abs_add_le _ _))
        _ ≤ |M 1 0| * B ^ 2 + |M 1 1 - M 0 0| * (B * B) + |M 0 1| * B ^ 2 := by
            gcongr
        _ = _ := by ring
  · -- real roots
    push Not at hΔ
    set s := √(T ^ 2 - 4 * D)
    have hs : s ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hΔ
    set μ₁ := (T - s) / 2
    set μ₂ := (T + s) / 2
    have hsum : μ₁ + μ₂ = T := by simp only [μ₁, μ₂]; ring
    have hprod : μ₁ * μ₂ = D := by simp only [μ₁, μ₂]; nlinarith
    have hroot : ∀ μ, μ = μ₁ ∨ μ = μ₂ → μ ^ 2 - T * μ + D = 0 := by
      rintro μ (rfl | rfl) <;> simp only [μ₁, μ₂] <;> nlinarith
    rw [← hsum, ← hprod, ← roots_outside_iff (hprod ▸ hD)]
    constructor
    · intro hdet
      by_contra hc
      obtain ⟨μ, hμ, hle⟩ : ∃ μ, (μ = μ₁ ∨ μ = μ₂) ∧ |μ| ≤ 1 := by
        rcases not_and_or.1 hc with c | c <;> push Not at c
        · exact ⟨μ₁, Or.inl rfl, c⟩
        · exact ⟨μ₂, Or.inr rfl, c⟩
      obtain ⟨v, hv, hMv⟩ := (exists_eigenvector M) (hroot μ hμ)
      have hz : IsOrbit M fun t => μ ^ t • v := fun t => by
        show μ ^ (t + 1) • v = M *ᵥ (μ ^ t • v)
        rw [mulVec_smul, hMv, smul_smul, pow_succ, mul_comm]
      have hb : Bounded fun t => μ ^ t • v := ⟨|v 0| + |v 1|, fun t i => by
        show |(μ ^ t • v) i| ≤ _
        rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
        have : |v i| ≤ |v 0| + |v 1| := by
          fin_cases i
          · simp [abs_nonneg]
          · simp [abs_nonneg]
        exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hle)).trans this⟩
      exact hv (by simpa using hdet _ hz hb 0)
    · rintro ⟨h1, h2⟩
      exact fun z hz hb => (zero_of_real M) hsum hprod h1 h2 hz hb

end BK

/-! ### The three-equation model -/

/-- Parameters of the three-equation New Keynesian model. -/
structure Model where
  /-- Inverse intertemporal elasticity of substitution. -/
  σ : ℝ
  /-- Slope of the Phillips curve. -/
  κ : ℝ
  /-- Discount factor. -/
  β : ℝ
  /-- Taylor-rule responses to inflation and to the output gap. -/
  φπ : ℝ
  φx : ℝ
  hσ : 0 < σ
  hκ : 0 < κ
  hβ₀ : 0 < β
  hβ₁ : β < 1
  hφπ : 0 ≤ φπ
  hφx : 0 ≤ φx

namespace Model

variable (E : Model)

/-- A perfect-foresight equilibrium path of output gap `x`, inflation `p` and
the nominal rate `i`. -/
def IsEquilibrium (x p i : ℕ → ℝ) : Prop :=
  ∀ t, x t = x (t + 1) - (i t - p (t + 1)) / E.σ ∧
    p t = E.β * p (t + 1) + E.κ * x t ∧
    i t = E.φπ * p t + E.φx * x t

/-- The model is **determinate** if the only bounded equilibrium is the steady state. -/
def Determinate : Prop :=
  ∀ x p i, E.IsEquilibrium x p i → (∃ B, ∀ t, |x t| ≤ B ∧ |p t| ≤ B ∧ |i t| ≤ B) →
    ∀ t, x t = 0 ∧ p t = 0 ∧ i t = 0

/-- The forward map `(x_t, π_t) ↦ (x_{t+1}, π_{t+1})`. -/
def forward : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + E.φx / E.σ + E.κ / (E.σ * E.β), (E.φπ - 1 / E.β) / E.σ; -E.κ / E.β, 1 / E.β]

theorem forward_det : E.forward.det = (E.σ + E.φx + E.κ * E.φπ) / (E.σ * E.β) := by
  have := E.hσ.ne'; have := E.hβ₀.ne'
  rw [forward, det_fin_two_of]; field_simp; ring

theorem forward_trace :
    E.forward.trace = 1 + E.φx / E.σ + E.κ / (E.σ * E.β) + 1 / E.β := by
  rw [forward, trace_fin_two_of]

theorem isEquilibrium_iff (x p i : ℕ → ℝ) :
    E.IsEquilibrium x p i ↔ (∀ t, i t = E.φπ * p t + E.φx * x t) ∧
      IsOrbit E.forward fun t => ![x t, p t] := by
  have hσ := E.hσ.ne'; have hβ := E.hβ₀.ne'
  have e0 : ∀ t, (E.forward *ᵥ ![x t, p t]) 0 =
      (1 + E.φx / E.σ + E.κ / (E.σ * E.β)) * x t + (E.φπ - 1 / E.β) / E.σ * p t := fun t => by
    simp [mulVec_zero', forward]
  have e1 : ∀ t, (E.forward *ᵥ ![x t, p t]) 1 = -E.κ / E.β * x t + 1 / E.β * p t := fun t => by
    simp [mulVec_one', forward]
  constructor
  · intro h
    refine ⟨fun t => (h t).2.2, fun t => funext fun j => ?_⟩
    obtain ⟨h1, h2, h3⟩ := h t
    have hp1 : p (t + 1) = (p t - E.κ * x t) / E.β := by field_simp; linarith
    have hx1 : x (t + 1) = x t + (i t - p (t + 1)) / E.σ := by linarith
    fin_cases j
    · show x (t + 1) = (E.forward *ᵥ ![x t, p t]) 0
      rw [e0, hx1, h3, hp1]; field_simp; ring
    · show p (t + 1) = (E.forward *ᵥ ![x t, p t]) 1
      rw [e1, hp1]; field_simp; ring
  · rintro ⟨hi, ho⟩ t
    have h0 : x (t + 1) = _ := (congrFun (ho t) 0).trans (e0 t)
    have h1 : p (t + 1) = _ := (congrFun (ho t) 1).trans (e1 t)
    refine ⟨?_, ?_, hi t⟩
    · rw [hi t, h0, h1]; field_simp; ring
    · rw [h1]; field_simp; ring

theorem determinate_iff_forward : E.Determinate ↔ NK.Determinate E.forward := by
  constructor
  · intro h z hz ⟨B, hB⟩ t
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
    have heq : E.IsEquilibrium (fun t => z t 0) (fun t => z t 1)
        (fun t => E.φπ * z t 1 + E.φx * z t 0) := by
      rw [isEquilibrium_iff]
      refine ⟨fun _ => rfl, fun t => ?_⟩
      have : ∀ t, ![z t 0, z t 1] = z t := fun t => by
        funext j; fin_cases j <;> rfl
      simp only [this]; exact hz t
    have hbd : ∀ t, |z t 0| ≤ B + (E.φπ + E.φx) * B ∧ |z t 1| ≤ B + (E.φπ + E.φx) * B ∧
        |E.φπ * z t 1 + E.φx * z t 0| ≤ B + (E.φπ + E.φx) * B := fun t => by
      have h0 := hB t 0; have h1 := hB t 1
      have hφ : 0 ≤ (E.φπ + E.φx) * B := mul_nonneg (add_nonneg E.hφπ E.hφx) hB0
      refine ⟨by linarith, by linarith, ?_⟩
      calc |E.φπ * z t 1 + E.φx * z t 0| ≤ |E.φπ * z t 1| + |E.φx * z t 0| := abs_add_le _ _
        _ = E.φπ * |z t 1| + E.φx * |z t 0| := by
          rw [abs_mul, abs_mul, abs_of_nonneg E.hφπ, abs_of_nonneg E.hφx]
        _ ≤ E.φπ * B + E.φx * B := by
          gcongr
          · exact E.hφπ
          · exact E.hφx
        _ ≤ _ := by nlinarith
    obtain ⟨a, b, -⟩ := h _ _ _ heq ⟨_, hbd⟩ t
    funext j; fin_cases j
    · exact a
    · exact b
  · intro h x p i heq ⟨B, hB⟩ t
    obtain ⟨hi, ho⟩ := (E.isEquilibrium_iff x p i).1 heq
    have hz := h _ ho ⟨B, fun t j => by fin_cases j <;> simp [(hB t).1, (hB t).2.1]⟩ t
    have a : x t = 0 := by simpa using congrFun hz 0
    have b : p t = 0 := by simpa using congrFun hz 1
    exact ⟨a, b, by rw [hi, a, b]; ring⟩

/-- **Determinacy in the NK model** (Bullard–Mitra 2002; Galí, Prop. 4.1 form):
the equilibrium is locally unique iff `κ (φ_π − 1) + (1 − β) φ_x > 0`. -/
theorem taylor_principle :
    E.Determinate ↔ 0 < E.κ * (E.φπ - 1) + (1 - E.β) * E.φx := by
  have hσ := E.hσ; have hβ₀ := E.hβ₀; have hβ₁ := E.hβ₁
  have hφπ := E.hφπ; have hφx := E.hφx; have hκ := E.hκ
  have hσβ : 0 < E.σ * E.β := mul_pos hσ hβ₀
  have hD : E.forward.det - 1 = (E.σ * (1 - E.β) + E.φx + E.κ * E.φπ) / (E.σ * E.β) := by
    rw [forward_det]; field_simp; ring
  have hT : 1 + E.forward.det - E.forward.trace =
      (E.κ * (E.φπ - 1) + (1 - E.β) * E.φx) / (E.σ * E.β) := by
    rw [forward_det, forward_trace]; field_simp; ring
  have hD1 : 1 < E.forward.det := by
    have : 0 < (E.σ * (1 - E.β) + E.φx + E.κ * E.φπ) / (E.σ * E.β) :=
      div_pos (by nlinarith) hσβ
    linarith
  have hTpos : 0 < E.forward.trace := by rw [forward_trace]; positivity
  rw [determinate_iff_forward, determinate_iff _ (by linarith), abs_of_pos hTpos]
  constructor
  · rintro ⟨-, h⟩
    have : 0 < (E.κ * (E.φπ - 1) + (1 - E.β) * E.φx) / (E.σ * E.β) := by linarith
    exact (div_pos_iff_of_pos_right hσβ).1 this
  · intro h
    exact ⟨hD1, by have := div_pos h hσβ; linarith⟩

/-- **The Taylor principle.** With no response to the output gap, the
equilibrium is determinate iff the nominal rate responds more than one-for-one
to inflation. -/
theorem taylor_principle_strict (h : E.φx = 0) : E.Determinate ↔ 1 < E.φπ := by
  rw [taylor_principle, h, mul_zero, add_zero]
  constructor
  · intro h'; by_contra hc; push Not at hc; nlinarith [E.hκ]
  · intro h'; nlinarith [E.hκ]

end Model

/-- **Non-vacuity.** A standard calibration (`σ = 1`, `κ = 1/10`, `β = 99/100`)
is determinate under `φ_π = 3/2` and indeterminate under `φ_π = 1/2` (`φ_x = 0`). -/
example : (⟨1, 1 / 10, 99 / 100, 3 / 2, 0, one_pos, by norm_num, by norm_num, by norm_num,
      by norm_num, le_rfl⟩ : Model).Determinate ∧
    ¬ (⟨1, 1 / 10, 99 / 100, 1 / 2, 0, one_pos, by norm_num, by norm_num, by norm_num,
      by norm_num, le_rfl⟩ : Model).Determinate := by
  constructor
  · rw [Model.taylor_principle_strict _ rfl]; norm_num
  · rw [Model.taylor_principle_strict _ rfl]; norm_num

end NK
end Econ

end
