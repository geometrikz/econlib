# Review: Hopenhayn (1992) stationary equilibrium (EconLean/Macro/Firms/Hopenhayn.lean)

Frozen statements: EconLean/Audit/Statements/Hopenhayn.lean (frozen_hop_*).

## Step 1: context-isolated adversarial econ review — PASS (no WRONG findings)
OK: incumbent Bellman equation and exit timing (exit decided after production, before the draw of x');
entrants timed consistently in free entry and the law of motion (Hopenhayn 1992: entrants produce once);
equilibrium definition equivalent to the canonical one (M = 0 is impossible since D > 0 and δ > 0;
μ ≥ 0 is implied); cutoff/upper-set hypotheses (profits increasing, Q stochastically monotone);
boundary conditions satisfiable; uniqueness over the whole triple (p, M, μ); frozen statements match.
Numerics on example₁: p* ≈ 0.7933, M ≈ 0.0409, μ ≈ (0.2046, 0.2046).

WEAK findings and responses:
- Assumptions at all real prices excluded standard models (zero output / choke price at low p).
  FIXED: π strictly increasing, s > 0 and D > 0 are now assumed only for p > 0; equilibrium requires
  p > 0; boundary prices must be positive.
- Docstring credited exogenous exit to Hopenhayn–Rogerson. FIXED: δ is described as the textbook device.
- Header said the stationary theorem gives nonnegativity. FIXED: points to `stationary_nonneg`.
- Ties broken toward staying; uniqueness is for that rule. DOCUMENTED in the module and the blueprint.
- π and s are unrelated reduced-form primitives. Acknowledged in Scope.
- example₁ has no endogenous exit at the equilibrium price (shows non-vacuity, not selection). Open.

## Step 2: mechanical checks — PASS (re-run after the fixes)
- #print axioms on all 8 frozen theorems: propext, Classical.choice, Quot.sound.
- lake env leanchecker on module and frozen file: exit 0.
- nanoda on the exported frozen theorems: 21,392 declarations, no typechecker errors.
