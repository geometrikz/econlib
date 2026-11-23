/-
# Blackwell's sufficient conditions for a contraction

Stokey–Lucas (SL), *Recursive Methods in Economic Dynamics*, Thm 3.3;
Blackwell (1965).

**The economics.** Dynamic programming turns an infinite-horizon problem into
a fixed-point problem `v = T v` for a *Bellman operator* `T`. The contraction
mapping theorem (SL Thm 3.2; Mathlib's `ContractingWith.fixedPoint`) then gives
a unique fixed point and convergence of value-function iteration. Checking
directly that `T` is a contraction is often awkward; Blackwell's theorem says
two easy-to-check properties are enough:

* **monotonicity**: `f ≤ g` pointwise implies `T f ≤ T g` pointwise
  (a better continuation value never hurts);
* **discounting**: adding a constant `a ≥ 0` to `f` raises `T f` by at most
  `β a`, with `β < 1` (the future is worth less than the present).

Then `T` is a contraction of modulus `β` in the sup norm.

**The space.** SL state the theorem on `B(X)`, the bounded real functions on
`X`, "or a subspace of it" (any `T` that maps the subspace into itself). We use
Mathlib's `X →ᵇ ℝ`, the *bounded continuous* functions with the sup distance,
which is the space SL ch. 4 works in. `B(X)` itself is the special case where
`X` carries the discrete topology (then every function is continuous), so
nothing is lost.
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

@[expose] public section

namespace Econ

open BoundedContinuousFunction NNReal

variable {X : Type*} [TopologicalSpace X]

/-- **Blackwell's sufficient conditions** (SL Thm 3.3).
Let `T` map bounded continuous functions to bounded continuous functions,
and let `0 ≤ β < 1`. If `T` is
* monotone: `f ≤ g` pointwise ⇒ `T f ≤ T g` pointwise, and
* discounting: `T (f + a) ≤ T f + β a` pointwise for every constant `a ≥ 0`,

then `T` is a contraction with modulus `β` (in the sup distance). -/
theorem blackwell {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : (X →ᵇ ℝ) → (X →ᵇ ℝ))
    (hmono : ∀ f g : X →ᵇ ℝ, (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    (hdisc : ∀ (f : X →ᵇ ℝ) (a : ℝ), 0 ≤ a → ∀ x, T (f + const X a) x ≤ T f x + β * a) :
    ContractingWith ⟨β, hβ0⟩ T := by
  refine ⟨by exact_mod_cast hβ1, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  -- Key step (SL's proof): with `a = ‖f - g‖`, we have `f ≤ g + a`, so by
  -- monotonicity and then discounting `T f ≤ T (g + a) ≤ T g + β a`.
  set a := dist f g with ha
  have ha0 : 0 ≤ a := dist_nonneg
  have hside : ∀ f g : X →ᵇ ℝ, dist f g = a → ∀ x, T f x ≤ T g x + β * a := by
    intro f g hfg x
    have h1 : ∀ y, f y ≤ (g + const X a) y := fun y => by
      rw [add_apply, const_apply, ← hfg]; exact coe_le_coe_add_dist
    exact (hmono _ _ h1 x).trans (hdisc g a ha0 x)
  have hfg := hside f g rfl
  have hgf := hside g f (by rw [dist_comm])
  -- So `|T f x - T g x| ≤ β a` at every `x`, which bounds the sup distance.
  refine (dist_le (mul_nonneg hβ0 ha0)).2 fun x => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith [hfg x, hgf x]

/-- **Contraction mapping theorem, as used in DP** (SL Thm 3.2).
A Blackwell operator on bounded continuous functions has a unique fixed point
`v`, and iterating `T` from any starting guess converges to it at the
geometric rate `β ^ n` (value-function iteration). Here `T^[n]` is the
`n`-fold iterate. -/
theorem blackwell_fixedPoint {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : (X →ᵇ ℝ) → (X →ᵇ ℝ))
    (hmono : ∀ f g : X →ᵇ ℝ, (∀ x, f x ≤ g x) → ∀ x, T f x ≤ T g x)
    (hdisc : ∀ (f : X →ᵇ ℝ) (a : ℝ), 0 ≤ a → ∀ x, T (f + const X a) x ≤ T f x + β * a) :
    ∃! v : X →ᵇ ℝ, T v = v ∧
      ∀ v₀ : X →ᵇ ℝ, ∀ n : ℕ, dist (T^[n] v₀) v ≤ dist v₀ (T v₀) * β ^ n / (1 - β) := by
  have hT := blackwell hβ0 hβ1 T hmono hdisc
  refine ⟨ContractingWith.fixedPoint T hT, ⟨ContractingWith.fixedPoint_isFixedPt hT,
    fun v₀ n => ContractingWith.apriori_dist_iterate_fixedPoint_le hT v₀ n⟩, ?_⟩
  rintro v ⟨hv, -⟩
  exact ContractingWith.fixedPoint_unique hT hv

end Econ
