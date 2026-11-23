/-
# Brouwer's and Kakutani's fixed-point theorems (Econ-facing statements)

PLAN.md §1, `Foundations/FixedPoint/`. The proofs are vendored from
vltanh/lean4-fixed-point (Apache 2.0, The-Anh Vu-Le); see
`Foundations/FixedPoint/README.md`. They go through Sperner's lemma and the
Knaster–Kuratowski–Mazurkiewicz lemma.

This file restates the two headline theorems under `Econ` names, so economics
files depend on one stable statement rather than on the upstream names.

* `Econ.brouwer_fixedPoint`: a map continuous on a nonempty compact convex
  set `s` of a finite-dimensional real normed space, mapping `s` into itself,
  has a fixed point in `s` (Brouwer 1912).
* `Econ.kakutani_fixedPoint`: a correspondence from such an `s` to nonempty
  convex subsets of `s` with closed graph has a fixed point `x ∈ φ x`
  (Kakutani 1941). This is the form used for Nash existence and for
  equilibrium existence with demand correspondences.
-/
module

public import EconLean.Foundations.FixedPoint.Brouwer.KKM
public import EconLean.Foundations.FixedPoint.Kakutani.Convex

@[expose] public section

namespace Econ

open Set

/-- **Brouwer's fixed-point theorem.** In a finite-dimensional real normed
space, a map that is continuous on a nonempty compact convex set `s` and maps
`s` into itself has a fixed point in `s`. -/
theorem brouwer_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x :=
  Brouwer.KKM.exists_fixedPoint hconv hcomp hne hmaps hf

/-- **Brouwer's fixed-point theorem**, bundled form: a continuous self-map of a
nonempty compact convex set of a finite-dimensional real normed space has a
fixed point. -/
theorem brouwer_fixedPoint_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x :=
  Brouwer.KKM.exists_fixedPoint_continuousMap hconv hcomp hne f

/-- **Kakutani's fixed-point theorem.** In a finite-dimensional real normed
space, let `s` be nonempty, compact and convex, and let `φ` send each `x ∈ s`
to a nonempty convex subset of `s`, with closed graph
`{(x, y) | x ∈ s, y ∈ φ x}`. Then `x ∈ φ x` for some `x ∈ s`. -/
theorem kakutani_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x :=
  Kakutani.exists_fixedPoint hconv hcomp hne hmaps hφne hφconv hgraph

end Econ
