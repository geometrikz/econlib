# Review: replica economies and equal treatment in the core

Module: `EconLean/GE/Replica.lean`. Context-isolated adversarial review, 2026-11-25.

**Verdict: sound and faithful; no blocking issues.** The replica definition matches MWG's N-replica; core,
blocking and feasibility come from `GE/Exchange.lean`; the hypotheses (continuity, strict convexity via
`StrictlyQuasiconcave`, strong monotonicity) are exactly MWG's for the equal-treatment proposition.

Findings and resolution:
1. Citation: equal treatment may be numbered 18.B.2 in MWG, with 18.B.3 the Debreu–Scarf limit. Fixed: cite
   "MWG §18.B, equal-treatment proposition" and Debreu–Scarf (1963).
2. Witness weak (Walrasian allocations already have equal treatment). Fixed: added
   `linear_replica_unequal_core`, a core allocation with unequal treatment under linear utility, showing strict
   convexity is needed.
3. Continuity on all of ℝ^ι is more than needed. Documented.
4. r ≤ 1 trivial; documented.
5. Coalition feasibility with equality: equivalent under strong monotonicity. Note only.
6. Proof sketch wording of the transfer fixed; x̄ᵢ₀ ≠ 0 explained.
7. Scope honest (limit theorem not formalized).

Proof checks: `#print axioms` standard; leanchecker 0; nanoda 30597 declarations clean. Frozen:
`Audit/Statements/GE.lean`, section Replica. Full build warning-free.
