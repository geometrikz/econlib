# Review note: approximate equilibria of replica economies without convexity (batch 7)

Files: EconLean/GE/ApproximateEquilibrium.lean (new); Audit/Statements/Lyapunov.lean (section ApproxEquilibrium);
blueprint lyapunov.tex (sec:approx_equilibrium).

## Step 1: context-isolated adversarial review (Starr 1969, Shapley–Folkman, Arrow–Hahn ch. 7, Aumann 1966)
No blockers. Reviewer confirmed quantifier order (p and C before n), that the conclusion has content for n ≥ 1
(a naive choice of demanded bundles gives error growing like n), the hypotheses are standard, the rounding lemmas
are correct, and frozen copies match.
Should-fix items, all applied:
- Witness strengthened from n = 1 to every odd n and to all prices: `positivePrices_of_mem_demand_uSq`
  (demand exists only at p ≫ 0), `mem_demand_uSq` (every demanded bundle is a corner),
  `sqReplica_odd_no_equilibrium`. All frozen.
- Scope: Starr's bound is independent of the number of types as well as agents; here C grows with |T|; per-agent
  error is C/(n|T|); the allocation optimizes exactly but need not be feasible (Starr's form is feasible with ≤ L
  agents off demand).
- Header no longer claims a limit/convergence result ("mirrored by").
- Attribution: replica analogue of Starr, proved by Carathéodory + rounding, no Shapley–Folkman.
- Blueprint rounding proof clarified; scope remark expanded.
Not done (nit): tightening the rounding bound from M+1 to M; even-n exact equilibrium of the witness.

## Step 2: mechanical checks
- `#print axioms`: propext, Classical.choice, Quot.sound only.
- `lake env leanchecker EconLean.GE.ApproximateEquilibrium`: exit 0.
- nanoda: 31751 declarations, no typechecker errors.
- Audit/Statements/Lyapunov.lean builds; full `lake build` clean.
