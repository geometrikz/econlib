# Review: existence of Walrasian equilibrium from preferences (MWG 17.B.2 + 17.C.1)

Files: GE/ExistenceInterior.lean (economy corollary `exists_walrasianEquilibrium_of_boundaryCondition`),
GE/ExistencePreferences.lean (`boundaryCondition_excessDemand`, `wealth_pos`,
`exists_walrasianEquilibrium_of_preferences`, square-root economy witness), `section FromPreferences` in
Audit/Statements/FixedPoint.lean, blueprint sections in chapters/fixedpoint.tex.

Closes the independent reviewer's remaining gap: "MWG 17.B.2 from preferences plus the economy-level corollary".

## Step 1: context-isolated adversarial review
- Economy corollary: faithful (Walras' law derived from local nonsatiation).
- Boundary condition from strong monotonicity: faithful, slightly stronger than MWG (needs neither strict convexity nor
  nonzero individual endowments).
- Existence from preferences: faithful with deviation: each endowment assumed nonzero (`hωa`), i.e. positive wealth at
  p ≫ 0, as in MWG's text; not mathematically necessary. Documented in the docstring.
- Witness `sqrtEconomy` (u = √x₀ + √x₁, endowments (1,2), (2,1)): genuine; closed-simplex theorem cannot apply.

## Step 2
- Build warning-free; `#print axioms` on `exists_walrasianEquilibrium_of_preferences` and
  `sqrtEconomy_exists_equilibrium`: propext, Classical.choice, Quot.sound only (Brouwer is proved, not assumed).
- leanchecker passes on GE.ExistenceInterior, GE.ExistencePreferences, Audit.Statements.FixedPoint.
