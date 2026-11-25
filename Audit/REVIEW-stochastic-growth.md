# Review: stochastic growth, invariant distribution of capital (Macro/DP/StochasticGrowth.lean)

Frozen statements: `EconLean/Audit/Statements/StochasticGrowth.lean` (7 theorems).

## Reverifiers
- `#print axioms`: all 7 frozen theorems use only propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on Macro.DP.StochasticGrowth and Audit.Statements.StochasticGrowth.
- nanoda: no typechecker errors (38,950 declarations).
- Warning-free; blueprint PDF builds with 0 undefined references.

## Adversarial statement review (context-isolated)
No MISMATCH, no VACUOUS-RISK. Checked OK: ergodic interval (fixed points of worst/best shock maps);
existence (Krylov–Bogoliubov) and uniqueness of the joint law of (x, z); z-marginal = q;
E[x] = (q0 μ0 + q1 μ1)/(1−α) (also confirmed by 10^6-period simulation for α = 0, 0.3, 0.7);
`brockMirman_policy` and the standard formula E[log k] = (log αβ + E log A)/(1−α); chain lemma;
degenerate cases α = 0 and A(0) = A(1) remain correct.

WEAK findings and responses:
1. `brockMirman` has no β > 0 field (log(αβ) is a junk value otherwise). Disclosed in the docstring;
   `brockMirman_policy` assumes β > 0; the mean formula holds regardless.
2. Uniqueness is among distributions on the ergodic interval. Docstring now notes that every
   stationary distribution on ℝ lives there (not formalized).
Optimality of k' = αβ A(z) k^α in the stochastic model is cited, not proved (module Scope).
