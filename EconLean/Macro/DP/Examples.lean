/-
# Non-vacuity witnesses for the dynamic-programming theorems

Every hypothesis bundle used in `Macro/DP` is satisfiable: here is a concrete
dynamic program meeting SL Assumptions 4.3–4.4 (so `DynProg` is inhabited),
monotonicity (SL 4.7), convex technology and strictly concave returns
(SL 4.7–4.8, used for Thm 4.8), and the Benveniste–Scheinkman hypotheses
(SL 4.11). The unbounded verification theorems and Euler/transversality are
witnessed by the Brock–Mirman model (`BrockMirman.lean`).

**The example.** State space `S = [0, 1]`, any next state feasible
(`Γ x = S`), return `F(x, y) = -(x - 2)² - y²` (strictly increasing and
strictly concave in the state on `[0, 1]`, concave in `y`), `β = 1/2`.
-/
module

public import EconLean.Macro.DP.Concavity
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

namespace Econ

namespace DPExample

open Set Filter Topology

/-- State space `[0, 1]`. -/
abbrev S : Set ℝ := Icc 0 1

/-- The return `F(x, y) = -(x - 2)² - y²`. -/
def F (x y : S) : ℝ := -((x : ℝ) - 2) ^ 2 - (y : ℝ) ^ 2

/-- The example satisfies SL Assumptions 4.3–4.4. -/
noncomputable def P : DynProg S where
  Γ := fun _ => univ
  F := F
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => univ_nonempty
  Γ_compact := fun _ => isCompact_univ
  Γ_continuous := ⟨UpperHemicontinuous.const, LowerHemicontinuous.const⟩
  F_continuous := by unfold Function.uncurry F; fun_prop
  F_bounded := ⟨5, fun x y _ => by
    obtain ⟨hx0, hx1⟩ := x.2
    obtain ⟨hy0, hy1⟩ := y.2
    simp only [F]
    rw [abs_le]
    constructor <;> nlinarith⟩

/-- Monotonicity hypotheses of SL Thm 4.7 hold, so `V` is strictly increasing. -/
example : (∀ x x' y, x < x' → y ∈ P.Γ x → P.F x y < P.F x' y) ∧
    (∀ x x', x ≤ x' → P.Γ x ⊆ P.Γ x') ∧ StrictMono P.value := by
  have hF : ∀ x x' y, x < x' → y ∈ P.Γ x → P.F x y < P.F x' y := by
    intro x x' y hxx' _
    have h1 : (x : ℝ) < x' := hxx'
    have := x'.2.2
    show F x y < F x' y
    simp only [F]
    nlinarith
  have hΓ : ∀ x x', x ≤ x' → P.Γ x ⊆ P.Γ x' := fun _ _ _ => subset_rfl
  exact ⟨hF, hΓ, P.value_strictMono hF hΓ⟩

theorem convexGraph : ConvexGraph P.Γ := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mem_univ _

theorem strictlyConcaveReturn : StrictlyConcaveReturn P.Γ P.F := by
  intro x y x' y' z w _ _ a b ha hb hab hz hw
  have hz' : (z : ℝ) = a * x + b * x' := by simpa using hz
  have hw' : (w : ℝ) = a * y + b * y' := by simpa using hw
  show a * F x y + b * F x' y' ≤ F z w ∧ (x ≠ x' → a * F x y + b * F x' y' < F z w)
  simp only [F, hz', hw']
  obtain rfl : b = 1 - a := by linarith
  -- `a f(x) + b f(x') - f(ax + bx') = -ab (x - x')²` for `f = -(·)²` etc.
  have key : -(a * x + (1 - a) * x' - 2) ^ 2 - (a * y + (1 - a) * y') ^ 2 -
      (a * (-((x : ℝ) - 2) ^ 2 - (y : ℝ) ^ 2) + (1 - a) * (-((x' : ℝ) - 2) ^ 2 - (y' : ℝ) ^ 2)) =
      a * (1 - a) * (((x : ℝ) - x') ^ 2 + ((y : ℝ) - y') ^ 2) := by ring
  have hab' : 0 < a * (1 - a) := mul_pos ha hb
  refine ⟨by nlinarith [sq_nonneg ((x : ℝ) - x'), sq_nonneg ((y : ℝ) - y')], fun hne => ?_⟩
  have : (x : ℝ) ≠ x' := fun h => hne (Subtype.ext h)
  have : 0 < ((x : ℝ) - x') ^ 2 := by positivity
  nlinarith [sq_nonneg ((y : ℝ) - y')]

/-- SL Thm 4.8 applies: `V` strictly concave, policy a continuous function. -/
example : StrictlyConcaveFn (P.value : S → ℝ) ∧
    ∃ g : S → S, Continuous g ∧ ∀ x, P.policy x = {g x} :=
  ⟨P.value_strictlyConcave (convex_Icc 0 1) convexGraph strictlyConcaveReturn,
    P.exists_continuous_policy (convex_Icc 0 1) convexGraph strictlyConcaveReturn⟩

/-- The Benveniste–Scheinkman hypotheses hold at the interior point `x₀ = 1/2`
for an optimal choice `y₀`, and the theorem gives `V'(1/2) = F_x(1/2, y₀) = 3`. -/
example : ∃ y₀ : S, y₀ ∈ P.policy ⟨1 / 2, by norm_num, by norm_num⟩ ∧
    (1 / 2 : ℝ) ∈ interior S ∧
    (∀ᶠ r in 𝓝 (1 / 2 : ℝ), ∀ h : r ∈ S, y₀ ∈ P.Γ ⟨r, h⟩) ∧
    HasDerivAt (extendS fun x => P.F x y₀) 3 (1 / 2) ∧
    HasDerivAt (extendS (P.value : S → ℝ)) 3 (1 / 2) := by
  set x₀ : S := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨y₀, hy₀⟩ := P.policy_nonempty x₀
  have hint : (1 / 2 : ℝ) ∈ interior S := by
    rw [interior_Icc]; constructor <;> norm_num
  have hloc : ∀ᶠ r in 𝓝 (1 / 2 : ℝ), ∀ h : r ∈ S, y₀ ∈ P.Γ ⟨r, h⟩ :=
    Eventually.of_forall fun _ _ => mem_univ _
  have hFx : HasDerivAt (extendS fun x => P.F x y₀) 3 (1 / 2) := by
    have hd : HasDerivAt (fun r : ℝ => -(r - 2) ^ 2 - (y₀ : ℝ) ^ 2) 3 (1 / 2) := by
      have h1 : HasDerivAt (fun r : ℝ => r - 2) 1 (1 / 2) := (hasDerivAt_id' _).sub_const 2
      have := ((h1.mul h1).neg).sub_const ((y₀ : ℝ) ^ 2)
      convert this using 1
      · funext r; simp only [Pi.mul_apply, Pi.neg_apply]; ring
      · norm_num
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [mem_interior_iff_mem_nhds.1 hint] with r hr
    simp only [extendS, hr, dite_true]
    rfl
  exact ⟨y₀, hy₀, hint, hloc, hFx,
    P.hasDerivAt_value (convex_Icc 0 1) convexGraph strictlyConcaveReturn
      (x₀ := x₀) hint hy₀ hloc hFx⟩

end DPExample

end Econ
