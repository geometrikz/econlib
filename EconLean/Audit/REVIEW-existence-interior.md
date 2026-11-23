# Review: existence with a boundary condition (MWG Prop. 17.C.1)

Files: GE/ExistenceInterior.lean; zCD boundary-condition lemmas in Bridges/Aggregation/Examples.lean;
`section BoundaryCondition` in Audit/Statements/FixedPoint.lean; blueprint `sec:existence_boundary` in
chapters/fixedpoint.tex.

Addresses the independent reviewer's finding I1 (closed-simplex existence cannot apply to strongly monotone
economies such as linEconomy / Cobb–Douglas).

Proof route: shrink the simplex by r_ε(p) = (1 − Nε)p + ε𝟙, apply the (now unconditional) Gale–Nikaido–Debreu lemma to
w(p)_l = (1 − Nε) z_l(r p) + ε Σ_k z_k(r p), bound z above uniformly using the lower bound, pass to a convergent
subsequence, rule out boundary limits by the boundary condition, and conclude with Walras' law.

## Step 1: context-isolated adversarial review
- ExcessBoundedBelow, BoundaryCondition, PositivePrices: faithful (BoundaryCondition ≡ max_l z_l(pⁿ) → ∞).
- exists_equilibrium_of_boundaryCondition: faithful with deviation: homogeneity (17.B.2(ii)) dropped, which only
  generalises the theorem. Docstring now says so.
- zCD witness: genuine; it is not continuous on the closed simplex, so the interior theorem is needed.

## Step 2
- Build warning-free; `#print axioms` standard only; leanchecker passes on GE.ExistenceInterior,
  Bridges.Aggregation.Examples, Audit.Statements.FixedPoint.

## Open
- Derive (i)–(v) from preferences (continuous, strictly convex, strongly monotone, ω ≫ 0) via Berge, so that
  exchange economies like Cobb–Douglas get existence directly (MWG 17.B.2).
