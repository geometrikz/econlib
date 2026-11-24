# Review: uniqueness of the stationary distribution (Macro/DP/MonotoneMixing.lean, Macro/HA/StationaryUnique.lean)

Frozen statements: `EconLean/Audit/Statements/StationaryUnique.lean` (11 theorems).

## Reverifiers
- `#print axioms`: all 11 frozen theorems use only propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on Macro.DP.MonotoneMixing, Macro.HA.StationaryUnique, Audit.Statements.StationaryUnique.
- nanoda: no typechecker errors (39,898 declarations).
- Files compile warning-free; blueprint PDF builds with 0 undefined references.

## Adversarial statement review (context-isolated)
No MISMATCH, no VACUOUS-RISK. Checked OK: layer cake and FOSD over upper sets;
`IsMonotoneKernel` matches Hopenhayn–Prescott / SLP 12.4; `unique_invariant_of_splitting` is
faithful to HP Theorem 2 / Bhattacharya–Lee (uniqueness half), valid on any preorder, `hgen`
discharged by `generateFrom_upperSets_prod`; policy monotonicity via cash on hand under i.i.d.
shocks; example numbers (value iteration: min employed saving 0.45–0.69 across the bracket vs floor
0.0025; (19/20)^320·k̄ ≈ 2.7e-6 ≤ k_h/100 ≈ 2.5e-3; δ = 0.9^321 > 0).

WEAK finding and response:
1. `slack_equilibrium_unique` title could be read as "unique equilibrium". Response: docstring now
   says "at its interest rate ... unique stationary distribution (uniqueness of the equilibrium rate
   is not claimed)"; the module Scope already says so.
Not formalized (disclosed): existence/convergence halves of HP, Markov (non-i.i.d.) income.
