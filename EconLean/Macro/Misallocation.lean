/-
# Misallocation and TFP (Hsieh–Klenow)

Hsieh and Klenow (2009), "Misallocation and Manufacturing TFP in China and
India", QJE, §I; Restuccia–Rogerson (2008).

**The economics.** An industry has firms `i` with physical productivity
`Aᵢ > 0`. Each produces `Yᵢ = Aᵢ Lᵢ` and industry output is the CES aggregate

    Y = (Σᵢ Yᵢ^ρ)^{1/ρ},   ρ = (σ − 1)/σ,   σ > 1 the elasticity of substitution.

Normalize total labour to `1` and write `sᵢ = Lᵢ` for firm `i`'s labour share.
Then `Y(s)` is industry TFP. Hsieh–Klenow's results:

* **Efficient TFP** is `(Σᵢ Aᵢ^{σ−1})^{1/(σ−1)}`, attained exactly when labour
  shares are proportional to `Aᵢ^{σ−1}` (`tfp_le_efficient`, `tfp_eq_efficient_iff`).
* With CES demand, firm `i`'s **revenue productivity** is
  `TFPRᵢ = Pᵢ Yᵢ / Lᵢ ∝ Yᵢ^ρ / Lᵢ = Aᵢ^ρ sᵢ^{ρ−1}` (`tfpr`). Allocation is
  efficient **iff TFPR is equalized across firms** (`tfpr_equal_iff`), and any
  dispersion in TFPR strictly lowers TFP (`tfp_lt_of_tfpr_dispersion`): the
  headline of the paper.
* With firm-specific output wedges `τᵢ < 1`, profit maximization gives labour
  shares `∝ Aᵢ^{σ−1}(1 − τᵢ)^σ` (`wedgeAlloc`, taken from HK eq. (8)–(9)).
  Then `TFPRᵢ ∝ 1/(1 − τᵢ)` (`tfpr_wedgeAlloc`), so the economy is efficient
  iff all wedges are equal (`wedgeAlloc_efficient_iff`).

**The Lean.** The inequality is Jensen's inequality for the concave
`x ↦ x^ρ`, with weights proportional to `Aᵢ^{σ−1}`; the equality case is
Mathlib's strict Jensen.

**Deviations from the paper.** Labour is the only input (HK also have capital
with a separate capital wedge; the labour-only case already contains the
mechanism). The firm problem leading to `wedgeAlloc` is not re-derived; we
start from the resulting labour allocation. HK's log-normal approximation
`log TFP_e − log TFP = (σ/2) var(log TFPR)` is not formalized.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

noncomputable section

namespace Econ
namespace Misallocation

open Finset Set Real

/-- An industry: firms indexed by a finite nonempty type, productivities
`A i > 0`, and the elasticity of substitution `σ > 1`. -/
structure Industry (ι : Type*) [Fintype ι] where
  A : ι → ℝ
  σ : ℝ
  hA : ∀ i, 0 < A i
  hσ : 1 < σ

variable {ι : Type*} [Fintype ι] (I : Industry ι)

namespace Industry

/-- `ρ = (σ − 1)/σ ∈ (0, 1)`. -/
def ρ : ℝ := (I.σ - 1) / I.σ

theorem ρ_pos : 0 < I.ρ := div_pos (by linarith [I.hσ]) (by linarith [I.hσ])
theorem ρ_lt_one : I.ρ < 1 := by
  rw [ρ, div_lt_one (by linarith [I.hσ])]; linarith

/-- An allocation of the unit labour endowment: shares `s i ≥ 0` summing to 1. -/
def IsAlloc (s : ι → ℝ) : Prop := (∀ i, 0 ≤ s i) ∧ ∑ i, s i = 1

/-- Industry TFP (= output, since total labour is 1) under allocation `s`:
`(Σᵢ (Aᵢ sᵢ)^ρ)^{1/ρ}`. -/
def tfp (s : ι → ℝ) : ℝ := (∑ i, (I.A i * s i) ^ I.ρ) ^ (1 / I.ρ)

/-- `πᵢ = Aᵢ^{σ−1}`, the efficient weights. -/
def wt (i : ι) : ℝ := I.A i ^ (I.σ - 1)

/-- `Π = Σᵢ Aᵢ^{σ−1}`. -/
def wtSum : ℝ := ∑ i, I.wt i

/-- Efficient TFP `(Σᵢ Aᵢ^{σ−1})^{1/(σ−1)}`. -/
def tfpEfficient : ℝ := I.wtSum ^ (1 / (I.σ - 1))

/-- The efficient allocation `sᵢ = Aᵢ^{σ−1} / Σⱼ Aⱼ^{σ−1}`. -/
def effAlloc (i : ι) : ℝ := I.wt i / I.wtSum

theorem wt_pos (i : ι) : 0 < I.wt i := rpow_pos_of_pos (I.hA i) _

theorem wtSum_pos [Nonempty ι] : 0 < I.wtSum :=
  Finset.sum_pos (fun i _ => I.wt_pos i) univ_nonempty

/-- Key rewriting: `(Aᵢ sᵢ)^ρ = πᵢ · (sᵢ / πᵢ)^ρ`. -/
theorem term_eq (i : ι) {x : ℝ} (hx : 0 ≤ x) :
    (I.A i * x) ^ I.ρ = I.wt i * (x / I.wt i) ^ I.ρ := by
  have hA := I.hA i
  have hπ := I.wt_pos i
  have hσ : I.σ ≠ 0 := by linarith [I.hσ]
  rw [mul_rpow hA.le hx, div_rpow hx hπ.le, wt, ← rpow_mul hA.le]
  have : I.A i ^ ((I.σ - 1) * I.ρ) = I.A i ^ (I.σ - 1) / I.A i ^ I.ρ := by
    rw [← rpow_sub hA]; congr 1; simp only [ρ]; field_simp
  rw [this]
  have hAr : 0 < I.A i ^ I.ρ := rpow_pos_of_pos hA _
  have hAs : 0 < I.A i ^ (I.σ - 1) := rpow_pos_of_pos hA _
  field_simp

/-- Jensen form: `Σᵢ (Aᵢ sᵢ)^ρ = Π · Σᵢ (πᵢ/Π) (sᵢ/πᵢ)^ρ`. -/
theorem sum_eq [Nonempty ι] {s : ι → ℝ} (hs : IsAlloc s) :
    ∑ i, (I.A i * s i) ^ I.ρ = I.wtSum * ∑ i, (I.wt i / I.wtSum) * (s i / I.wt i) ^ I.ρ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [I.term_eq i (hs.1 i)]
  have := I.wtSum_pos
  field_simp

theorem weights_sum [Nonempty ι] : ∑ i, I.wt i / I.wtSum = 1 := by
  rw [← Finset.sum_div]; exact div_self I.wtSum_pos.ne'

theorem mean_eq [Nonempty ι] {s : ι → ℝ} (hs : IsAlloc s) :
    ∑ i, (I.wt i / I.wtSum) * (s i / I.wt i) = 1 / I.wtSum := by
  have : ∀ i, (I.wt i / I.wtSum) * (s i / I.wt i) = s i / I.wtSum := fun i => by
    have := I.wt_pos i; have := I.wtSum_pos; field_simp
  simp only [this, ← Finset.sum_div, hs.2]

/-- `Π^{1−ρ}` raised to `1/ρ` is efficient TFP. -/
theorem tfpEfficient_eq [Nonempty ι] :
    (I.wtSum * (1 / I.wtSum) ^ I.ρ) ^ (1 / I.ρ) = I.tfpEfficient := by
  have hW := I.wtSum_pos
  have hρ := I.ρ_pos
  rw [div_rpow zero_le_one hW.le, one_rpow, ← div_eq_mul_one_div, ← rpow_one_sub' hW.le]
  · rw [← rpow_mul hW.le, tfpEfficient]
    congr 1
    have hσ : I.σ ≠ 0 := by linarith [I.hσ]
    have hσ1 : I.σ - 1 ≠ 0 := by linarith [I.hσ]
    simp only [ρ]; field_simp; ring
  · linarith [I.ρ_lt_one]

/-- **Misallocation lowers TFP.** Every allocation achieves at most efficient
TFP `(Σᵢ Aᵢ^{σ−1})^{1/(σ−1)}`. -/
theorem tfp_le_efficient [Nonempty ι] {s : ι → ℝ} (hs : IsAlloc s) :
    I.tfp s ≤ I.tfpEfficient := by
  have hconc := (Real.strictConcaveOn_rpow I.ρ_pos I.ρ_lt_one).concaveOn
  have hJ := hconc.le_map_sum (t := univ) (w := fun i => I.wt i / I.wtSum)
    (p := fun i => s i / I.wt i) (fun i _ => (div_pos (I.wt_pos i) I.wtSum_pos).le) I.weights_sum
    (fun i _ => Set.mem_Ici.2 (div_nonneg (hs.1 i) (I.wt_pos i).le))
  simp only [smul_eq_mul] at hJ
  rw [I.mean_eq hs] at hJ
  rw [tfp, I.sum_eq hs, ← I.tfpEfficient_eq]
  have hsum : 0 ≤ ∑ i, I.wt i / I.wtSum * (s i / I.wt i) ^ I.ρ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (div_pos (I.wt_pos i) I.wtSum_pos).le
      (rpow_nonneg (div_nonneg (hs.1 i) (I.wt_pos i).le) _)
  exact rpow_le_rpow (mul_nonneg I.wtSum_pos.le hsum)
    (mul_le_mul_of_nonneg_left hJ I.wtSum_pos.le) (div_pos one_pos I.ρ_pos).le

theorem effAlloc_isAlloc [Nonempty ι] : IsAlloc I.effAlloc :=
  ⟨fun i => (div_pos (I.wt_pos i) I.wtSum_pos).le, by
    simp only [effAlloc]; exact I.weights_sum⟩

/-- **Equality case:** TFP is efficient iff `sᵢ = Aᵢ^{σ−1}/Σⱼ Aⱼ^{σ−1}` for all `i`. -/
theorem tfp_eq_efficient_iff [Nonempty ι] {s : ι → ℝ} (hs : IsAlloc s) :
    I.tfp s = I.tfpEfficient ↔ s = I.effAlloc := by
  have hW := I.wtSum_pos
  constructor
  · intro h
    by_contra hne
    -- some ratio `sᵢ/πᵢ` differs from another, so Jensen is strict
    have hdiff : ∃ j ∈ (Finset.univ : Finset ι), ∃ k ∈ (Finset.univ : Finset ι),
        s j / I.wt j ≠ s k / I.wt k := by
      by_contra hall
      push Not at hall
      apply hne
      -- all ratios equal a common `r`; summing gives `r = 1/Π`
      obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
      set r := s i₀ / I.wt i₀
      have hr : ∀ i, s i = r * I.wt i := fun i => by
        have h := hall i (Finset.mem_univ _) i₀ (Finset.mem_univ _)
        rw [div_eq_iff (I.wt_pos i).ne'] at h
        exact h
      have hsum : r * I.wtSum = 1 := by
        rw [wtSum, Finset.mul_sum, ← hs.2]; exact Finset.sum_congr rfl fun i _ => (hr i).symm
      funext i
      rw [hr i, effAlloc, eq_div_iff I.wtSum_pos.ne', mul_right_comm, hsum, one_mul]
    have hconc := Real.strictConcaveOn_rpow I.ρ_pos I.ρ_lt_one
    have hJ := hconc.lt_map_sum (t := univ) (w := fun i => I.wt i / I.wtSum)
      (p := fun i => s i / I.wt i) (fun i _ => div_pos (I.wt_pos i) I.wtSum_pos) I.weights_sum
      (fun i _ => Set.mem_Ici.2 (div_nonneg (hs.1 i) (I.wt_pos i).le)) hdiff
    simp only [smul_eq_mul] at hJ
    rw [I.mean_eq hs] at hJ
    rw [tfp, I.sum_eq hs, ← I.tfpEfficient_eq] at h
    have hsum : 0 ≤ ∑ i, I.wt i / I.wtSum * (s i / I.wt i) ^ I.ρ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (div_pos (I.wt_pos i) I.wtSum_pos).le
        (rpow_nonneg (div_nonneg (hs.1 i) (I.wt_pos i).le) _)
    have hlt := rpow_lt_rpow (mul_nonneg hW.le hsum) (mul_lt_mul_of_pos_left hJ hW)
      (div_pos one_pos I.ρ_pos)
    linarith
  · rintro rfl
    rw [tfp, I.sum_eq I.effAlloc_isAlloc, ← I.tfpEfficient_eq]
    have : ∀ i, I.effAlloc i / I.wt i = 1 / I.wtSum := fun i => by
      simp only [effAlloc]; rw [div_div_cancel_left₀ (I.wt_pos i).ne', one_div]
    simp only [this, ← Finset.sum_mul, I.weights_sum, one_mul]

/-! ## Revenue productivity (TFPR) -/

/-- Revenue productivity, up to a factor common to all firms:
`TFPRᵢ ∝ Yᵢ^ρ / Lᵢ = Aᵢ^ρ sᵢ^{ρ−1}` (with CES demand, `Pᵢ ∝ Yᵢ^{−1/σ}`). -/
def tfpr (s : ι → ℝ) (i : ι) : ℝ := (I.A i * s i) ^ I.ρ / s i

/-- `TFPRᵢ = (sᵢ/πᵢ)^{ρ−1}`. -/
theorem tfpr_eq {s : ι → ℝ} {i : ι} (hsi : 0 < s i) :
    I.tfpr s i = (s i / I.wt i) ^ (I.ρ - 1) := by
  rw [tfpr, I.term_eq i hsi.le, rpow_sub_one (div_pos hsi (I.wt_pos i)).ne']
  have := I.wt_pos i
  field_simp

/-- **Efficiency ⟺ TFPR equalized.** For an allocation with all firms active,
TFP is efficient iff revenue productivity is the same in every firm. -/
theorem tfpr_equal_iff [Nonempty ι] {s : ι → ℝ} (hs : IsAlloc s) (hpos : ∀ i, 0 < s i) :
    (∀ i j, I.tfpr s i = I.tfpr s j) ↔ I.tfp s = I.tfpEfficient := by
  rw [I.tfp_eq_efficient_iff hs]
  have hρ1 : I.ρ - 1 < 0 := by linarith [I.ρ_lt_one]
  -- `x ↦ x^{ρ−1}` is injective on `(0, ∞)`
  have hinj : ∀ x y : ℝ, 0 < x → 0 < y → x ^ (I.ρ - 1) = y ^ (I.ρ - 1) → x = y := by
    intro x y hx hy h
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · exact absurd h (rpow_lt_rpow_of_neg hx hxy hρ1).ne'
    · rfl
    · exact absurd h (rpow_lt_rpow_of_neg hy hxy hρ1).ne
  constructor
  · intro h
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    set r := s i₀ / I.wt i₀
    have hr : ∀ i, s i = r * I.wt i := fun i => by
      have h' := hinj _ _ (div_pos (hpos i) (I.wt_pos i)) (div_pos (hpos i₀) (I.wt_pos i₀))
        (by rw [← I.tfpr_eq (hpos i), ← I.tfpr_eq (hpos i₀)]; exact h i i₀)
      rw [div_eq_iff (I.wt_pos i).ne'] at h'
      exact h'
    have hsum : r * I.wtSum = 1 := by
      rw [wtSum, Finset.mul_sum, ← hs.2]; exact Finset.sum_congr rfl fun i _ => (hr i).symm
    funext i
    rw [hr i, effAlloc, eq_div_iff I.wtSum_pos.ne', mul_right_comm, hsum, one_mul]
  · rintro rfl i j
    rw [I.tfpr_eq (hpos i), I.tfpr_eq (hpos j)]
    simp only [effAlloc]
    have := I.wt_pos i; have := I.wt_pos j
    rw [div_div_cancel_left₀ (I.wt_pos i).ne', div_div_cancel_left₀ (I.wt_pos j).ne']

/-- **Hsieh–Klenow's headline:** dispersion in TFPR strictly lowers TFP below
its efficient level. -/
theorem tfp_lt_of_tfpr_dispersion [Nonempty ι] {s : ι → ℝ} (hs : IsAlloc s)
    (hpos : ∀ i, 0 < s i) (hdisp : ∃ i j, I.tfpr s i ≠ I.tfpr s j) :
    I.tfp s < I.tfpEfficient := by
  refine lt_of_le_of_ne (I.tfp_le_efficient hs) fun h => ?_
  obtain ⟨i, j, hij⟩ := hdisp
  exact hij (((I.tfpr_equal_iff hs hpos).2 h) i j)

/-! ## Wedges -/

/-- The labour allocation induced by firm-specific output wedges `τᵢ < 1`
(Hsieh–Klenow eq. (8)–(9), labour only): `sᵢ ∝ Aᵢ^{σ−1}(1 − τᵢ)^σ`. -/
def wedgeAlloc (τ : ι → ℝ) (i : ι) : ℝ :=
  I.wt i * (1 - τ i) ^ I.σ / ∑ j, I.wt j * (1 - τ j) ^ I.σ

theorem wedgeAlloc_isAlloc [Nonempty ι] {τ : ι → ℝ} (hτ : ∀ i, τ i < 1) :
    IsAlloc (I.wedgeAlloc τ) ∧ ∀ i, 0 < I.wedgeAlloc τ i := by
  have hZ : 0 < ∑ j, I.wt j * (1 - τ j) ^ I.σ :=
    Finset.sum_pos (fun j _ => mul_pos (I.wt_pos j) (rpow_pos_of_pos (by linarith [hτ j]) _))
      univ_nonempty
  refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · exact (div_pos (mul_pos (I.wt_pos i) (rpow_pos_of_pos (by linarith [hτ i]) _)) hZ).le
  · simp only [wedgeAlloc, ← Finset.sum_div]; exact div_self hZ.ne'
  · exact div_pos (mul_pos (I.wt_pos i) (rpow_pos_of_pos (by linarith [hτ i]) _)) hZ

/-- **TFPR reflects the wedge:** `TFPRᵢ = Z^{1−ρ} / (1 − τᵢ)` with a factor `Z`
common to all firms. -/
theorem tfpr_wedgeAlloc [Nonempty ι] {τ : ι → ℝ} (hτ : ∀ i, τ i < 1) (i : ι) :
    I.tfpr (I.wedgeAlloc τ) i =
      (∑ j, I.wt j * (1 - τ j) ^ I.σ) ^ (1 - I.ρ) / (1 - τ i) := by
  have hZ : 0 < ∑ j, I.wt j * (1 - τ j) ^ I.σ :=
    Finset.sum_pos (fun j _ => mul_pos (I.wt_pos j) (rpow_pos_of_pos (by linarith [hτ j]) _))
      univ_nonempty
  have h1τ : 0 < 1 - τ i := by linarith [hτ i]
  rw [I.tfpr_eq ((I.wedgeAlloc_isAlloc hτ).2 i)]
  have : I.wedgeAlloc τ i / I.wt i = (1 - τ i) ^ I.σ / ∑ j, I.wt j * (1 - τ j) ^ I.σ := by
    have := I.wt_pos i
    simp only [wedgeAlloc]; field_simp
  rw [this, div_rpow (rpow_pos_of_pos h1τ _).le hZ.le, ← rpow_mul h1τ.le]
  have hσ : I.σ ≠ 0 := by linarith [I.hσ]
  have e : I.σ * (I.ρ - 1) = -1 := by simp only [ρ]; field_simp; ring
  rw [e, rpow_neg_one, show I.ρ - 1 = -(1 - I.ρ) by ring, rpow_neg hZ.le]
  field_simp

/-- **Wedges cause misallocation iff they differ:** the wedge-distorted
allocation is efficient iff all firms face the same wedge. -/
theorem wedgeAlloc_efficient_iff [Nonempty ι] {τ : ι → ℝ} (hτ : ∀ i, τ i < 1) :
    I.tfp (I.wedgeAlloc τ) = I.tfpEfficient ↔ ∀ i j, τ i = τ j := by
  rw [← I.tfpr_equal_iff (I.wedgeAlloc_isAlloc hτ).1 (I.wedgeAlloc_isAlloc hτ).2]
  have hZ : 0 < ∑ j, I.wt j * (1 - τ j) ^ I.σ :=
    Finset.sum_pos (fun j _ => mul_pos (I.wt_pos j) (rpow_pos_of_pos (by linarith [hτ j]) _))
      univ_nonempty
  have hZρ : 0 < (∑ j, I.wt j * (1 - τ j) ^ I.σ) ^ (1 - I.ρ) := rpow_pos_of_pos hZ _
  simp only [I.tfpr_wedgeAlloc hτ]
  constructor
  · intro h i j
    have := h i j
    have hi : 0 < 1 - τ i := by linarith [hτ i]
    have hj : 0 < 1 - τ j := by linarith [hτ j]
    rw [div_eq_div_iff hi.ne' hj.ne'] at this
    have := mul_left_cancel₀ hZρ.ne' this
    linarith
  · intro h i j; rw [h i j]

end Industry

/-- **Non-vacuity.** Two firms with `A = (1, 2)`, `σ = 3`, and unequal wedges
`τ = (0, 1/2)` lose TFP relative to the efficient allocation. -/
example : (⟨![1, 2], 3, fun i => by fin_cases i <;> norm_num, by norm_num⟩ : Industry (Fin 2)).tfp
    ((⟨![1, 2], 3, fun i => by fin_cases i <;> norm_num, by norm_num⟩ : Industry (Fin 2)).wedgeAlloc
      ![0, 1 / 2]) ≠
    (⟨![1, 2], 3, fun i => by fin_cases i <;> norm_num, by norm_num⟩ : Industry (Fin 2)).tfpEfficient := by
  rw [Ne, Industry.wedgeAlloc_efficient_iff _ (fun i => by fin_cases i <;> norm_num)]
  intro h
  have := h 0 1
  norm_num at this

end Misallocation
end Econ

end
