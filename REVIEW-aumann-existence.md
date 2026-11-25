# Review note: Aumann (1966) existence without convexity (batch 6)

Files: EconLean/GE/AumannExistence.lean (new); Audit/Statements/Lyapunov.lean (section AumannExistence);
blueprint lyapunov.tex (sec:aumann_existence).

## Step 1: context-isolated adversarial review (Aumann 1966, Hildenbrand 1974, Starr 1969, MWG 17)
No blockers. Reviewer confirmed: conclusions use true (untruncated) demand at wealth p·ω, prices ≫ 0, exact
mass-weighted clearing; the continuum conclusion is the standard Aumann equilibrium notion; the witness
instantiates the theorem with proved (not assumed) mass hypothesis; frozen copies match verbatim.
Should-fix items, all applied:
- Froze the universal "no a.e.-constant equilibrium at positive prices" claim for sqContinuum, and
  `exists_pos_le_of_notMem`.
- Reworded the docstring of `sqContinuum_exists_asymmetric_equilibrium` (it is existential).
- Scope paragraph expanded: finitely many types; utility representation vs. Aumann's preference relations
  (no loss for complete/transitive/continuous, excludes Schmeidler 1969); strong monotonicity is Aumann's
  desirability; individual ω ≫ 0 vs Aumann's aggregate ∫e ≫ 0 (confirmed by reviewer); every-trader type map;
  any finite measure.
- Blueprint scope remark added; witness proof wording clarified; header rhetoric replaced by what is proved.
Not done (nit): the witness's "at positive prices" hedge could be removed (every price with nonempty demand is ≫ 0).

## Step 2: mechanical checks
- `#print axioms`: propext, Classical.choice, Quot.sound only for all headline theorems.
- `lake env leanchecker EconLean.GE.AumannExistence`: exit 0.
- nanoda: 38345 declarations, no typechecker errors.
- Audit/Statements/Lyapunov.lean builds; full `lake build` clean.
