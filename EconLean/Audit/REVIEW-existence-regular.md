# Review: existence with zero endowments and Cobb–Douglas-type preferences

Module: `EconLean/GE/ExistenceRegular.lean`. Context-isolated adversarial review, 2026-11-24.

**Verdict: faithful, with caveats; no blocking issues.** The statements match MWG 17.B.2 / 17.C.1:
continuous utilities, strictly convex preferences, either strongly monotone or Cobb–Douglas type,
and `ω̄ ≫ 0`. The equilibrium notion is right (`p ≫ 0`, each bundle in demand at `p·ωₐ`, exact
clearing). Zero-endowment consumers are handled correctly.

Findings and resolution:
1. `improve` hides its meaning. Under continuity it is equivalent to "demand is empty at boundary
   prices with positive wealth". Fixed: documented in the module header, and the direction used is
   proved as `RegularUtility.demand_eq_empty_of_boundary`.
2. The witness equilibrium was trivial (Cobb–Douglas consumer in autarky). Fixed: `cdEconomy` now
   has three consumers (CD owning `(1,0)`, √ owning nothing, √ owning `(0,1)`), and
   `cdEconomy_trade` proves the CD consumer trades in every equilibrium.
3. Only `x₀x₁` (α = 1/2) is formalized, not general Cobb–Douglas. Documented; general α left open.
4. `InteriorRegular` is a sufficient condition, not MWG's exact statement. Docstring fixed.
5. Continuity is required on all of `ℝ^ι`. Documented (compose with positive part).
6. Zero-endowment consumers still need `RegularUtility`. Harmless; noted.
7. Loose MWG citations fixed; `PositivePrices x` on bundles commented.
8. Quantifiers: no issue.

Proof checks: `#print axioms` standard for all headline theorems; `leanchecker` exit 0; nanoda
checked 30550 declarations with no typechecker errors. Frozen statements in
`Audit/Statements/FixedPoint.lean`, section `Regular`.
