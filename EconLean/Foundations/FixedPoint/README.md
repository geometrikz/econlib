# Vendored fixed-point theorems

The files in this directory are copied from
[vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)
at commit `5f650f00b1db63837a452696331a98ca886b94a8` (2026-11-08),
by The-Anh Vu-Le, released under the Apache License 2.0 (see `LICENSE` here).

Copied with geoff's approval (2026-11-23), because Brouwer's and Kakutani's
fixed-point theorems are not in Mathlib v4.36.0.

Only the KKM (Sperner) route is copied: `Common/{ContinuousMap, EnclosingSimplex,
Euclidean, NearestPoint, Sperner, Subdivision}`, `Brouwer/KKM`,
`Kakutani/{Limit, Simplex, Convex}`. The analytic proof and Schauder are left out.

Changes from upstream: only the `public import FixedPoint.*` lines were rewritten
to `public import EconLean.Foundations.FixedPoint.*`, plus any changes listed
below that were needed to build warning-free on Lean/Mathlib v4.36.0 (upstream
uses v4.36.0-rc2). Declarations keep their upstream names and namespaces
(`Brouwer.KKM`, `Kakutani`, `Sperner`, `BarycentricSubdivision`, `NearestPoint`,
`FixedPoint`).

Headline results:
- `Brouwer.KKM.exists_fixedPoint`: a map continuous on a nonempty compact convex
  set `s` of a finite-dimensional real normed space, mapping `s` into itself,
  has a fixed point.
- `Brouwer.KKM.exists_fixedPoint_continuousMap`: the same for `f : C(s, s)`.
- `Kakutani.exists_fixedPoint`: Kakutani's theorem (closed graph, nonempty
  convex values).

## Build changes

None: the copied files build warning-free unchanged on v4.36.0.
