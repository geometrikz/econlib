/-
# The supporting hyperplane theorem in `ℝ^ι`, stated with price vectors

MWG Mathematical Appendix, Theorem M.G.3 (supporting hyperplane theorem);
Rockafellar, *Convex Analysis*, Thm. 11.6.

**The math.** Let `C ⊆ ℝ^ι` be convex and let `x` be a point that is *not in
the interior* of `C` (for example, any point outside `C`). Then there is a
nonzero vector `p` with

    p · x ≤ p · c   for every c ∈ C,

i.e. the hyperplane `{z | p · z = p · x}` through `x` has all of `C` on one
side. In economics `p` is a price vector: this is the step that turns "no
feasible Pareto improvement" into "supporting prices" in the Second Welfare
Theorem, and it is used again for production sets and core convergence.

**Why it is not just Hahn–Banach.** Mathlib's `geometric_hahn_banach_*`
theorems separate a point from an *open* or *closed* convex set, or from a set
with *nonempty interior*. The set we need (strictly preferred aggregate
bundles) need not be open, closed, or full-dimensional. Finite dimension saves
us:
* if `C` has nonempty interior, use
  `geometric_hahn_banach_of_nonempty_interior_point`;
* if `C` has empty interior, then (finite dimension!) `C` lies in a proper
  affine subspace, and any nonzero linear functional vanishing on its direction
  is constant on `C`; flip its sign if needed.

**The Lean.** A linear functional on `ι → ℝ` is the same thing as a price
vector: `f z = ∑ᵢ pᵢ zᵢ` with `pᵢ = f(eᵢ)` (`LinearMap.pi_apply_eq_sum_univ`).
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import EconLean.Consumer.Budget

@[expose] public section

namespace Econ

variable {ι : Type*} [Fintype ι]

/-- Every linear functional on `ℝ^ι` is "valuation at some prices": its
values are `cost p` for `pᵢ = f(eᵢ)`. -/
theorem exists_cost_eq_linearMap (f : (ι → ℝ) →ₗ[ℝ] ℝ) :
    ∃ p : ι → ℝ, ∀ z, f z = cost p z := by
  classical
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun z => ?_⟩
  -- `pi_apply_eq_sum_univ`: `f z = ∑ᵢ zᵢ • f(eᵢ)`.
  rw [LinearMap.pi_apply_eq_sum_univ f z, cost]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul, mul_comm])

/-- A nonzero linear functional corresponds to a nonzero price vector. -/
theorem exists_cost_eq_linearMap_ne_zero {f : (ι → ℝ) →ₗ[ℝ] ℝ} (hf : f ≠ 0) :
    ∃ p : ι → ℝ, p ≠ 0 ∧ ∀ z, f z = cost p z := by
  obtain ⟨p, hp⟩ := exists_cost_eq_linearMap f
  refine ⟨p, fun h0 => hf ?_, hp⟩
  -- If `p = 0` then `f z = 0 · z = 0` for all `z`.
  refine LinearMap.ext fun z => ?_
  simp [hp, h0, cost]

/-- **Supporting hyperplane theorem, linear-functional form.** A point outside
the interior of a convex set in `ℝ^ι` (with at least one good) is supported by
a nonzero linear functional. -/
theorem exists_linearMap_support [Nonempty ι] {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    {x : ι → ℝ} (hx : x ∉ interior C) :
    ∃ f : (ι → ℝ) →ₗ[ℝ] ℝ, f ≠ 0 ∧ ∀ c ∈ C, f x ≤ f c := by
  by_cases hint : (interior C).Nonempty
  · -- Case 1: nonempty interior. Mathlib's Hahn–Banach gives a continuous
    -- `g ≠ 0` with `g c ≤ g x` on `C`; use `-g`.
    obtain ⟨g, hg0, hg⟩ := geometric_hahn_banach_of_nonempty_interior_point hC hx hint
    refine ⟨-(g : (ι → ℝ) →ₗ[ℝ] ℝ), fun h => hg0 ?_, fun c hc => ?_⟩
    · refine ContinuousLinearMap.ext fun z => ?_
      have := congrArg (fun φ : (ι → ℝ) →ₗ[ℝ] ℝ => φ z) h
      simpa using this
    · simpa using hg c hc
  · -- Case 2: empty interior.
    rcases C.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
    · -- `C = ∅`: any nonzero functional works, e.g. a coordinate projection.
      obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨LinearMap.proj i, fun h => ?_, fun c hc => hc.elim⟩
      have := congrArg (fun φ : (ι → ℝ) →ₗ[ℝ] ℝ => φ (fun _ => 1)) h
      simp at this
    · -- The affine span of `C` is a proper affine subspace (finite dimension).
      have hspan : affineSpan ℝ C ≠ ⊤ := fun h =>
        hint ((hC.interior_nonempty_iff_affineSpan_eq_top).2 h)
      -- Hence its direction is a proper linear subspace ...
      have hdir : (affineSpan ℝ C).direction < ⊤ := by
        refine lt_top_iff_ne_top.2 fun h => hspan ?_
        exact (AffineSubspace.direction_eq_top_iff_of_nonempty
          ⟨c₀, subset_affineSpan ℝ C hc₀⟩).1 h
      -- ... so some nonzero functional `g` kills it.
      obtain ⟨g, hg0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
      -- `g` is constant on `C`: `c - c₀` lies in the direction.
      have hconst : ∀ c ∈ C, g c = g c₀ := by
        intro c hc
        have hmem : c -ᵥ c₀ ∈ (affineSpan ℝ C).direction :=
          AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hc)
            (subset_affineSpan ℝ C hc₀)
        have h0 : g (c - c₀) = 0 := hker hmem
        rw [map_sub, sub_eq_zero] at h0
        exact h0
      -- Use `g` or `-g`, whichever puts `x` on the low side.
      by_cases hle : g x ≤ g c₀
      · exact ⟨g, hg0, fun c hc => (hconst c hc).symm ▸ hle⟩
      · refine ⟨-g, neg_ne_zero.2 hg0, fun c hc => ?_⟩
        simp only [LinearMap.neg_apply, neg_le_neg_iff, hconst c hc]
        exact (not_le.1 hle).le

/-- **Supporting hyperplane theorem, price form** (MWG Thm. M.G.3). If `C ⊆ ℝ^ι`
is convex and `x` is not in its interior, there are nonzero prices `p` at which
`x` is (weakly) cheapest among `C ∪ {x}`: `p · x ≤ p · c` for all `c ∈ C`. -/
theorem exists_price_support [Nonempty ι] {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    {x : ι → ℝ} (hx : x ∉ interior C) :
    ∃ p : ι → ℝ, p ≠ 0 ∧ ∀ c ∈ C, cost p x ≤ cost p c := by
  obtain ⟨f, hf0, hf⟩ := exists_linearMap_support hC hx
  obtain ⟨p, hp0, hp⟩ := exists_cost_eq_linearMap_ne_zero hf0
  exact ⟨p, hp0, fun c hc => by simpa [hp] using hf c hc⟩

end Econ
