# Review: Debreu–Scarf core convergence

Module: `EconLean/GE/DebreuScarf.lean`. Context-isolated adversarial review, 2026-11-25.

**Verdict: sound; no blocking findings.** Faithful to MWG §18.B / Debreu–Scarf (1963) for allocations treating
copies of a type alike. Hypotheses are all genuinely used; the witness is non-vacuous.

Findings and resolution:
1. Conclusion `p ≥ 0, p ≠ 0` weaker than available. Fixed: both theorems now conclude `PositivePrices p`
   (new lemma `positivePrices_of_mem_demand`).
2. Strict quasiconcavity is needed only for equal treatment. Documented in the module header (kept as hypothesis).
3. "Core convergence theorem" claimed but not packaged. Fixed: `mem_core_replicas_iff_walrasian` (both directions).
4. Stale cross-reference in `Replica.lean`. Fixed.
5. Continuity on all of ℝ^ι for convenience. Documented.
6. Witness only shows satisfiability of the core hypothesis. Docstring reworded; an example showing "every r"
   cannot be dropped to r = 1 is left open.
7–8. Notes, no change.

Proof checks: `#print axioms` standard; leanchecker 0; nanoda clean. Frozen: `Audit/Statements/GE.lean`, section
DebreuScarf. Full build warning-free.
