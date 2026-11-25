# Review record: batch 15 (group strategy-proofness of DA, reputation, lemons with gains)

Modules: `Matching/GroupStrategyProof`, `Games/Reputation`, `Information/LemonsGains`.
Frozen statements: `EconLean/Audit/Statements/Batch15.lean`.
Header-only edits: `Matching/StrategyProof.lean` (points to the group version),
`Information/Lemons.lean` (points to LemonsGains).

## Step 1: context-isolated adversarial review (proofs stripped)

Round 1:
- **Major (fixed)**: `reputation_limit` chose `δ₀` after the normal type's strategy `q` and the
  payoff stream `u`. Fudenberg–Levine's point is uniformity, because equilibria change with `δ`.
  The statement now picks `δ₀` from `μ₀, π, v, m, ε` only, then quantifies over all `δ ≥ δ₀`, `q`, `u`, `Mx`.
- Minor (fixed): the `lemonsEqR_withheld` docstring overclaimed MWG Prop. 13.B.1. It is now
  "Good cars are withheld (cf.)", and the header says the condition is sufficient, not necessary.
- Minor (fixed): the reputation docstrings now say how `π` is chosen (beliefs above `π` give best
  responses to `a*`), and that equilibrium optimality is assumed, not modelled.
- Minor (fixed): stale scope notes in StrategyProof.lean and Lemons.lean now cross-reference the new files.
- Minor (fixed): the GroupStrategyProof docstring now says women report truthfully, misreports
  need not be strict, and only men's coalitions are covered.

Round 2 (fresh reviewer, after the fixes): no Critical or Major findings. It confirmed the
quantifier order of `reputation_limit` and the non-vacuity of `hC`. Its remaining Minor
docstring points were applied.

Witnesses: one-man coalition = individual strategy-proofness. Reputation: `μ₀ = 1/2`, `q = 0`.
Lemons: qualities 1, 2 (prob 1/2), `r θ = 0.9θ`, `p = 1`, the good car is withheld although 2 > 1.8.

## Step 2: mechanical checks

- Full build of the shared tree: 8000 jobs, green and warning-free.
- `#print axioms`: every headline theorem and frozen statement uses only `propext`, `Classical.choice` and `Quot.sound`.
- leanchecker: GroupStrategyProof, Reputation, LemonsGains and Audit.Statements.Batch15 all exit 0.
- nanoda: no typechecker errors (17,889 declarations). It also reports one pretty-printer error ("Unable to print axioms"), which is cosmetic and not a typechecker error.
- `leanblueprint pdf` builds (entries in matching.tex, games.tex and asyminfo.tex).
