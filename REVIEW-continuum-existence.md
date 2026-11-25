# Review note: continuum existence (batch 5)

Files: EconLean/GE/ContinuumExistence.lean, EconLean/Foundations/ConvexifiedCorrespondence.lean,
Audit/Statements/Lyapunov.lean (section ContinuumExistence), blueprint lyapunov.tex (sec:continuum_existence).

## Step 1: context-isolated adversarial review (against Aumann 1966, Hildenbrand 1974, MWG)

Review 1 (blocker found, fixed):
- BLOCKER: `exists_isWalrasianEquilibrium_of_types` carried a nonatomicity hypothesis that the proof never used
  (with type-constant allocations no splitting is needed). Dropped `hμ`; docstring and blueprint reworded as a
  reduction of the finitely-many-types convex case to the finite economy.
- Partition lemma at `n = 0` was false for nonempty null sets: restated with `[Nonempty κ]` / `Fin (n+1)`.
- Witness masses clarified (1/3, 2/3).

Review 2 (no blockers). Should-fix items, all applied:
- `maxContinuum_no_symmetric_equilibrium` generalized from the literal constant `fun _ => c` to any
  `x =ᵐ[μ] fun _ => c` (frozen statement updated).
- Witness docstring: "demand is {(2,0),(0,2)}" -> "demand contains (2,0) and (0,2) but not (1,1)"; removed the
  unproved claim about a representative consumer.
- Module docstring: the witness now claims only what is proved (no type-constant allocation is an equilibrium,
  splitting gives one), not "identical traders must consume different bundles in every equilibrium".
- Bridge docstring: "the splitting step of Aumann's 1966 proof" (not the full theorem).
- `one2` used in `maxContinuum_const_not_demanded`.
- Not done (optional, deferred): a `kakutani_fixedPoint_convexHull` corollary.

Scope disclosed: Aumann's (1966) existence theorem for general non-convex nonatomic economies (Kakutani on the
convexified truncated demand) is NOT formalized here; this batch gives the splitting bridge, the closed-graph
lemma for convexified correspondences it needs, and existence for finitely many strictly convex types.

## Step 2: mechanical checks
- `#print axioms`: propext, Classical.choice, Quot.sound only (all headline theorems).
- `lake env leanchecker EconLean.GE.ContinuumExistence` and `...ConvexifiedCorrespondence`: exit 0.
- nanoda: 37405 (ContinuumExistence) / 23066 (ConvexifiedCorrespondence) declarations, no typechecker errors.
- Audit/Statements/Lyapunov.lean builds against the frozen statements.
- Non-vacuity: sqrtContinuum (two strictly convex types), maxContinuum (non-convex, equilibrium exists only by splitting).
