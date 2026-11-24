/-
# Rademacher white noise

A concrete square-integrable white noise used as a non-vacuity witness for the
time-series results: on the infinite product of fair coins indexed by a
type `ι`, the signs `r i = ±1` satisfy `E[r_i r_j] = [i = j]`.
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

namespace Econ.TimeSeries.WhiteNoise

open MeasureTheory ProbabilityTheory

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := ⟨by
  simp only [coin, smul_apply, add_apply, Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul]
  rw [← two_mul, mul_one, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]⟩

variable {ι : Type*}

/-- The product of fair coins indexed by `ι`. -/
noncomputable def coins (ι : Type*) : Measure (ι → Bool) := Measure.infinitePi fun _ : ι => coin

instance : IsProbabilityMeasure (coins ι) := by unfold coins; infer_instance

/-- The sign of a coin. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The Rademacher variables `r i ω = ±1`. -/
def rad (i : ι) (ω : ι → Bool) : ℝ := sgn (ω i)

lemma measurable_rad (i : ι) : Measurable (rad i) :=
  (measurable_of_countable sgn).comp (measurable_pi_apply i)

lemma rad_mul_self (i : ι) (ω : ι → Bool) : rad i ω * rad i ω = 1 := by
  simp only [rad, sgn]; split_ifs <;> norm_num

lemma integral_rad (i : ι) : ∫ ω, rad i ω ∂(coins ι) = 0 := by
  have : (coins ι).map (fun ω => ω i) = coin := Measure.infinitePi_map_eval _ i
  calc ∫ ω, rad i ω ∂(coins ι)
      = ∫ b, sgn b ∂((coins ι).map (fun ω => ω i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable
          (measurable_of_countable sgn).aestronglyMeasurable).symm
    _ = ∫ b, sgn b ∂coin := by rw [this]
    _ = 0 := by
      rw [coin, integral_smul_measure, integral_add_measure Integrable.of_finite
        Integrable.of_finite, integral_dirac, integral_dirac]
      simp [sgn]

lemma memLp_rad (i : ι) (p : ENNReal) : MemLp (rad i) p (coins ι) :=
  MemLp.of_bound (measurable_rad i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by simp only [rad, sgn]; split_ifs <;> norm_num)

/-- **Rademacher white noise**: `E[r_i r_j] = 1` if `i = j` and `0` otherwise. -/
theorem integral_rad_mul [DecidableEq ι] (i j : ι) :
    ∫ ω, rad i ω * rad j ω ∂(coins ι) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; simp [rad_mul_self]
  · have hind : iIndepFun (fun k (ω : ι → Bool) => ω k) (coins ι) := by
      rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => measurable_pi_apply k)]
      simp only [coins, Measure.infinitePi_map_eval]
      exact Measure.map_id
    have hij := (hind.indepFun h).comp (measurable_of_countable sgn)
      (measurable_of_countable sgn)
    have := hij.integral_mul_eq_mul_integral (measurable_rad i).aestronglyMeasurable
      (measurable_rad j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    change ∫ ω, (sgn ∘ fun ω => ω i) ω * (sgn ∘ fun ω => ω j) ω ∂(coins ι) = 0
    rw [this]
    change (∫ ω, rad i ω ∂(coins ι)) * ∫ ω, rad j ω ∂(coins ι) = 0
    rw [integral_rad, zero_mul]

end Econ.TimeSeries.WhiteNoise
