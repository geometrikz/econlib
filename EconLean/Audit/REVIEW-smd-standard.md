# Review: SMD with continuous, strongly monotone consumers (`Bridges/Aggregation/SMDStandard.lean`), 2026-11-24

## Step 1: context-isolated adversarial statement review
Verdict: **faithful, with caveats**. No blocking findings.

The reviewer confirmed:
- Quantifier order: utilities and endowments are fixed before `∀ p ∈ K`.
- `demand (prefOf U) p (cost p ω) = {x}` is single-valued Walrasian demand on ℝ^L₊.
- `StronglyMonotone` is MWG's strong monotonicity. That is stronger than the "monotone" in the canonical theorem.
- Endowments are strictly positive, and there are exactly L consumers.
- A compact `K ⊆` open simplex generalizes `S_ε`.
- `PieceData` is satisfiable, and the `zBad` example is non-vacuous.

Findings and resolution:
1. *should-fix:* without strict convexity, demand is guaranteed single-valued only on `K`, not at every positive price.
   **Fixed:** this is now stated in the module Scope, in the theorem caveat, and in the blueprint.
2. *note:* prices off the simplex. **Documented:** homogeneity via `demand_smul`.
3. *note:* `stdUtility` is meaningful only under `PieceData`. **Fixed** in its docstring.
4. *note:* the module docstring said "Lipschitz" but only continuity is exported. **Fixed:** it now reads "continuous (proved
   via a Lipschitz bound)".
5. *note:* a loose constant in the construction sketch. **Annotated.**
6. *note:* why `priceBox` has upper bound 2. **Explained** in its docstring.

## Step 2: machine checks
- `lake build` is warning-free.
- `#print axioms` for `sonnenschein_mantel_debreu_monotone` and `zBad_standard_consumers`: `propext`, `Classical.choice`,
  `Quot.sound`.
- `lake env leanchecker EconLean.Bridges.Aggregation.SMDStandard`: exit 0.
- nanoda on the headline theorems: 16081 declarations, no typechecker errors. Its single pretty-printer message appears on
  every batch.
- Frozen statements: `Audit/Statements/Aggregation.lean`, `section SMDStandard`.
