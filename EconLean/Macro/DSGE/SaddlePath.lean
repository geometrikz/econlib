/-
# Blanchard–Kahn with a predetermined variable: the saddle path

Blanchard and Kahn (1980), "The Solution of Linear Difference Models under
Rational Expectations", Econometrica, Propositions 1–3 (the 2×2 case);
Ljungqvist–Sargent ch. 2 and 11; the Ramsey/RBC saddle path.

**Setting.** A linear perfect-foresight system `z_{t+1} = M z_t` in two
variables: `z 0 = k` is **predetermined** (its initial value `k₀` is given,
like capital) and `z 1 = y` is a **jump** variable (free at date 0, like
consumption). A solution from `k₀` is a bounded orbit with `z₀ 0 = k₀`
(`IsSolution`). The roots of `M` are real, `μ₁ + μ₂ = tr M`, `μ₁ μ₂ = det M`.

**Results (the Blanchard–Kahn counting rule).**
* `bounded_mem_span`: with exactly one stable root (`|μ₁| < 1 < |μ₂|`) every
  bounded orbit starts on the stable eigenvector `v` (the **saddle path**).
* `saddle`: one stable and one unstable root (number of unstable roots =
  number of jump variables) and the rank condition `v₀ ≠ 0` give, for every
  `k₀`, a **unique** solution, `z_t = μ₁ᵗ (k₀/v₀) v`.
* `no_solution_of_rank`: if the rank condition fails (`v₀ = 0`), there is no
  solution from any `k₀ ≠ 0`.
* `no_solution_of_explosive`: two unstable roots (too many) leave no solution
  from any `k₀ ≠ 0`.
* `indeterminate`: two stable, distinct roots (too few unstable roots): every
  solution has another solution with the same `k₀` (sunspot indeterminacy).

**Deviations.** "Solution" means a bounded orbit (Blanchard–Kahn allow
non-explosive growth; for these 2×2 systems with real roots the two notions
agree on the eigen-orbits used here). `indeterminate` assumes distinct roots
for its proof; a repeated stable root is also indeterminate. Two variables,
real roots; the general `n`-variable
statement with `n_k` predetermined variables is not formalized
(`Macro/NK/BlanchardKahn.lean` treats the all-jump case in `n` dimensions).
-/
module

public import EconLean.Macro.NK.ThreeEquation

@[expose] public section

noncomputable section

namespace Econ
namespace Saddle

open Matrix NK

variable (M : Matrix (Fin 2) (Fin 2) ℝ)

/-- A **solution** from predetermined value `k₀`: a bounded orbit whose
predetermined coordinate starts at `k₀`. -/
def IsSolution (k₀ : ℝ) (z : ℕ → Fin 2 → ℝ) : Prop :=
  IsOrbit M z ∧ Bounded z ∧ z 0 0 = k₀

variable {M}

/-- The orbit along an eigenvector. -/
theorem isOrbit_eig {μ : ℝ} {v : Fin 2 → ℝ} (hv : M *ᵥ v = μ • v) :
    IsOrbit M fun t => μ ^ t • v := fun t => by
  show μ ^ (t + 1) • v = M *ᵥ (μ ^ t • v)
  rw [mulVec_smul, hv, smul_smul, pow_succ]

theorem bounded_eig {μ : ℝ} (hμ : |μ| ≤ 1) (v : Fin 2 → ℝ) : Bounded fun t => μ ^ t • v := by
  refine ⟨|v 0| + |v 1|, fun t i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  have h1 : |μ| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) hμ
  have h2 : |v i| ≤ |v 0| + |v 1| := by
    fin_cases i <;> simp [abs_nonneg]
  calc |μ| ^ t * |v i| ≤ 1 * |v i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ _ := by linarith

theorem isOrbit_add {z w : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (hw : IsOrbit M w) :
    IsOrbit M (z + w) := fun t => by simp [hz t, hw t, mulVec_add]

theorem isOrbit_sub {z w : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (hw : IsOrbit M w) :
    IsOrbit M (z - w) := fun t => by simp [hz t, hw t, mulVec_sub]

theorem bounded_add {z w : ℕ → Fin 2 → ℝ} (hz : Bounded z) (hw : Bounded w) : Bounded (z + w) := by
  obtain ⟨B, hB⟩ := hz; obtain ⟨C, hC⟩ := hw
  exact ⟨B + C, fun t i => (abs_add_le _ _).trans (add_le_add (hB t i) (hC t i))⟩

theorem bounded_sub {z w : ℕ → Fin 2 → ℝ} (hz : Bounded z) (hw : Bounded w) : Bounded (z - w) := by
  obtain ⟨B, hB⟩ := hz; obtain ⟨C, hC⟩ := hw
  exact ⟨B + C, fun t i => (abs_sub _ _).trans (add_le_add (hB t i) (hC t i))⟩

/-- With an unstable root `μ₂`, a bounded orbit starts on the eigenline of the
other root: `M z₀ = μ₁ z₀`. -/
theorem mulVec_eq_of_bounded {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₂ : 1 < |μ₂|) {z : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (hb : Bounded z) :
    M *ᵥ z 0 = μ₁ • z 0 := by
  obtain ⟨B, hB⟩ := hb
  -- `p_t = z_{t+1} − μ₁ z_t` grows by the factor `μ₂`
  have hp' : ∀ t i, z (t + 1) i - μ₁ * z t i = μ₂ ^ t * (z 1 i - μ₁ * z 0 i) := by
    intro t i
    induction t with
    | zero => simp
    | succ t ih =>
      have h2 : z (t + 2) = M *ᵥ (M *ᵥ z t) := by rw [hz (t + 1), hz t]
      have := cayley_hamilton M (z t) i
      rw [← h2, ← hz t] at this
      rw [show t + 1 + 1 = t + 2 from rfl, this, ← hs, ← hp]
      linear_combination μ₂ * ih
  funext i
  have h0 : z 1 i - μ₁ * z 0 i = 0 := by
    refine eq_zero_of_geom h₂ (C := B + |μ₁| * B) fun t => ?_
    rw [← hp' t i]
    calc |z (t + 1) i - μ₁ * z t i| ≤ |z (t + 1) i| + |μ₁ * z t i| := abs_sub _ _
      _ ≤ B + |μ₁| * B := by
        rw [abs_mul]
        exact add_le_add (hB _ _) (mul_le_mul_of_nonneg_left (hB _ _) (abs_nonneg _))
  rw [hz 0] at h0
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- Two eigenvectors of a root `μ` are proportional unless `M = μ I`. -/
theorem cross_eq_zero {μ : ℝ} {v w : Fin 2 → ℝ} (hv : M *ᵥ v = μ • v) (hw : M *ᵥ w = μ • w)
    (hM : ¬ (M 0 0 = μ ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = μ)) : v 0 * w 1 = v 1 * w 0 := by
  by_contra hc
  have hc' : v 0 * w 1 - v 1 * w 0 ≠ 0 := sub_ne_zero.2 hc
  have v0 := congrFun hv 0; have v1 := congrFun hv 1
  have w0 := congrFun hw 0; have w1 := congrFun hw 1
  simp only [mulVec_zero', mulVec_one', Pi.smul_apply, smul_eq_mul] at v0 v1 w0 w1
  apply hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (M 0 0 - μ) * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination w 1 * v0 - v 1 * w0
    have := (mul_eq_zero.1 this).resolve_right hc'; linarith
  · have : M 0 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * w0 - w 0 * v0
    exact (mul_eq_zero.1 this).resolve_right hc'
  · have : M 1 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination w 1 * v1 - v 1 * w1
    exact (mul_eq_zero.1 this).resolve_right hc'
  · have : (M 1 1 - μ) * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * w1 - w 0 * v1
    have := (mul_eq_zero.1 this).resolve_right hc'; linarith

/-- If `M = μ₁ I` then both roots equal `μ₁`. -/
theorem not_scalar {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hne : μ₁ ≠ μ₂) :
    ¬ (M 0 0 = μ₁ ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = μ₁) := by
  rintro ⟨h0, -, -, h1⟩
  rw [trace_fin_two, h0, h1] at hs
  exact hne (by linarith)

/-- **The saddle path.** With one stable and one unstable root, every bounded
orbit starts on the stable eigenvector `v`. -/
theorem bounded_mem_span {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : |μ₁| < 1) (h₂ : 1 < |μ₂|) {v : Fin 2 → ℝ} (hv : M *ᵥ v = μ₁ • v)
    {z : ℕ → Fin 2 → ℝ} (hz : IsOrbit M z) (hb : Bounded z) :
    v 0 * z 0 1 = v 1 * z 0 0 := by
  have hne : μ₁ ≠ μ₂ := by
    rintro rfl; linarith
  exact cross_eq_zero hv (mulVec_eq_of_bounded hs hp h₂ hz hb) (not_scalar hs hne)

/-- **Blanchard–Kahn, saddle-path case.** One stable root, one unstable root
(as many unstable roots as jump variables), and the rank condition `v₀ ≠ 0`:
from every predetermined `k₀` there is exactly one solution, and it moves
along the stable eigenvector, `z_t = μ₁ᵗ (k₀/v₀) v`. -/
theorem saddle {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : |μ₁| < 1) (h₂ : 1 < |μ₂|) {v : Fin 2 → ℝ} (hv : M *ᵥ v = μ₁ • v) (hv0 : v 0 ≠ 0)
    (k₀ : ℝ) :
    ∃! z, IsSolution M k₀ z := by
  refine ⟨fun t => μ₁ ^ t • ((k₀ / v 0) • v), ⟨isOrbit_eig ?_, bounded_eig h₁.le _, ?_⟩, ?_⟩
  · rw [mulVec_smul, hv, smul_comm]
  · simp [hv0]
  · rintro z ⟨hz, hb, hk⟩
    -- the difference is a bounded orbit with zero predetermined part
    set w := z - fun t => μ₁ ^ t • ((k₀ / v 0) • v)
    have hw : IsOrbit M w := isOrbit_sub hz (isOrbit_eig (by rw [mulVec_smul, hv, smul_comm]))
    have hwb : Bounded w := bounded_sub hb (bounded_eig h₁.le _)
    have hw00 : w 0 0 = 0 := by simp [w, hk, hv0]
    have hspan := bounded_mem_span hs hp h₁ h₂ hv hw hwb
    rw [hw00, mul_zero] at hspan
    have hw01 : w 0 1 = 0 := (mul_eq_zero.1 hspan).resolve_left hv0
    have hw0 : w 0 = 0 := by
      funext i; fin_cases i
      · exact hw00
      · exact hw01
    have := orbit_eq_zero M hw hw0
    funext t
    have h := this t
    exact sub_eq_zero.1 h

/-- **Rank condition fails.** If the stable eigenvector has no predetermined
component, no solution starts from `k₀ ≠ 0`. -/
theorem no_solution_of_rank {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : |μ₁| < 1) (h₂ : 1 < |μ₂|) {v : Fin 2 → ℝ} (hv : M *ᵥ v = μ₁ • v) (hvne : v ≠ 0)
    (hv0 : v 0 = 0) {k₀ : ℝ} (hk : k₀ ≠ 0) (z : ℕ → Fin 2 → ℝ) : ¬ IsSolution M k₀ z := by
  rintro ⟨hz, hb, hz0⟩
  have hspan := bounded_mem_span hs hp h₁ h₂ hv hz hb
  rw [hv0, zero_mul, hz0] at hspan
  have hv1 : v 1 ≠ 0 := by
    intro h1; apply hvne; funext i; fin_cases i
    · exact hv0
    · exact h1
  exact hk ((mul_eq_zero.1 hspan.symm).resolve_left hv1)

/-- **Too many unstable roots.** With both roots outside the unit circle, the
only bounded orbit is zero: no solution from `k₀ ≠ 0`. -/
theorem no_solution_of_explosive {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : 1 < |μ₁|) (h₂ : 1 < |μ₂|) {k₀ : ℝ} (hk : k₀ ≠ 0) (z : ℕ → Fin 2 → ℝ) :
    ¬ IsSolution M k₀ z := by
  rintro ⟨hz, hb, hz0⟩
  have h0 := zero_of_real M hs hp h₁ h₂ hz hb
  exact hk (by rw [← hz0, h0]; rfl)

/-- **Too few unstable roots: indeterminacy.** With two distinct stable roots,
next to any solution from `k₀` there is a different solution from the same `k₀`. -/
theorem indeterminate {μ₁ μ₂ : ℝ} (hs : μ₁ + μ₂ = M.trace) (hp : μ₁ * μ₂ = M.det)
    (h₁ : |μ₁| < 1) (h₂ : |μ₂| < 1) (hne : μ₁ ≠ μ₂) {k₀ : ℝ} {z : ℕ → Fin 2 → ℝ}
    (hz : IsSolution M k₀ z) : ∃ z', IsSolution M k₀ z' ∧ z' ≠ z := by
  have e₁ : μ₁ ^ 2 - M.trace * μ₁ + M.det = 0 := by rw [← hs, ← hp]; ring
  have e₂ : μ₂ ^ 2 - M.trace * μ₂ + M.det = 0 := by rw [← hs, ← hp]; ring
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector M e₁
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector M e₂
  -- a bounded orbit `u` with zero predetermined part and `u 0 ≠ 0`
  obtain ⟨u, hu, hub, hu00, hu0⟩ : ∃ u : ℕ → Fin 2 → ℝ, IsOrbit M u ∧ Bounded u ∧ u 0 0 = 0 ∧
      u 0 ≠ 0 := by
    by_cases hv00 : v 0 = 0
    · exact ⟨fun t => μ₁ ^ t • v, isOrbit_eig hv, bounded_eig h₁.le v, by simp [hv00],
        by simpa using hv0⟩
    · refine ⟨(fun t => μ₁ ^ t • ((w 0 / v 0) • v)) - fun t => μ₂ ^ t • w,
        isOrbit_sub (isOrbit_eig (by rw [mulVec_smul, hv, smul_comm])) (isOrbit_eig hw),
        bounded_sub (bounded_eig h₁.le _) (bounded_eig h₂.le _), by simp [hv00], ?_⟩
      intro h
      simp only [Pi.sub_apply, pow_zero, one_smul, sub_eq_zero] at h
      -- then `w` is an eigenvector of both roots
      apply hw0
      have h1 : M *ᵥ w = μ₁ • w := by rw [← h, mulVec_smul, hv, smul_comm]
      have : (μ₁ - μ₂) • w = 0 := by rw [sub_smul, ← h1, hw, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  refine ⟨z + u, ⟨isOrbit_add hz.1 hu, bounded_add hz.2.1 hub, by simp [hz.2.2, hu00]⟩, ?_⟩
  intro h
  apply hu0
  have := congrFun h 0
  simpa using this

end Saddle
end Econ

end
