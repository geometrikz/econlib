# Re-review: consumer fixes (2026-11-23)

Step 1 of the verification protocol, re-run on the consumer review fixes by a
context-isolated adversarial reviewer, checked against MWG ch. 2–3.

Items reviewed: `ConvexPref`, `convex_demand`, `StrictlyQuasiconcave`,
`demand_subsingleton`, `exists_continuous_demand_function`,
`isGreatest_indirectUtility`, `isLeast_expenditure`, `indirectUtility_strictMono`,
`budgetSet_anti`, `indirectUtility_antitone_price`, `slutsky`, `slutsky_demand`.

Verdict: no blockers. All items match the textbook on what they state.

- `ConvexPref` now matches MWG Def. 3.B.4, with the quantifier and the contour
  set both restricted to ℝⁿ₊. This resolves F3.
- `StrictlyQuasiconcave` is now restricted to ℝⁿ₊. This resolves F7.
- The junk value (sSup ∅ = 0) cannot leak into the new duality lemmas: each one
  assumes p ≫ 0 plus w ≥ 0 or a reachable ū.
- `slutsky_demand` derives the duality identity and Shephard's lemma, which
  resolves F4. Its singleton hypotheses are satisfiable, for example by
  Cobb–Douglas extended by max(·, 0), so the theorem is not vacuous.

Findings carried forward:
1. Should-fix (OPEN, recorded as F8 in EconLean/Audit/ConsumerFindings.lean):
   Cobb–Douglas is not strictly quasiconcave on the closed orthant, because it
   is flat along the axes. As a result `exists_continuous_demand_function`
   misses the canonical consumer. MWG has the same gap.
2. Note: `slutsky_demand` asks for single-valued demand globally, where MWG
   only needs it near (p, w). When ū = u 0, differentiability of X is asked at
   w = 0.
3. Note: quasiconvexity of v (MWG 3.D.3) is not formalized yet.
4. Note: the converse of the compensated law of demand (CLD ⇒ WARP) is not
   formalized yet.
