# Review: Aiyagari equilibrium with a non-binding cap (Macro/HA/AiyagariSlack.lean)

Frozen statements: `EconLean/Audit/Statements/AiyagariSlack.lean` (7 theorems):
wage_eq_mul_kOfR, wage_anti, aiyagari_policy_le_max, aiyagari_supply_ge_of_save,
aiyagari_exists_equilibrium_slack, slack_saving, slack_equilibrium.

## Reverifiers
- `#print axioms`: all 7 frozen theorems use only propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on Macro.HA.AiyagariSlack and Audit.Statements.AiyagariSlack.
- nanoda: no typechecker errors (37,972 declarations; "Unable to print axioms" is benign).
- File compiles warning-free; blueprint PDF builds with 0 undefined references.

## Adversarial statement review (context-isolated)
No MISMATCH, no VACUOUS-RISK. Checked OK: Cobb–Douglas wage identity and monotonicity;
algebra of A = w(r_lo) ē/(-r_hi); supply bound via the invariant z-marginal; the seven
equilibrium conjuncts (goods market re-derived); joint satisfiability via the example;
example numbers (L = 0.1, k(r_hi) = 0.2486, w(r_hi) = 3.15 k, k(r_lo) = 360.3, k̄ = 36.03,
A = 32.43 = 0.9 k̄). `slack_saving` confirmed by value iteration at r = -0.05 (min employed
saving 0.544 vs floor 0.249). Numerical equilibrium rate ≈ -0.25.

WEAK findings and responses:
1. r < 0 (hence β(1+r) < 1) comes from the bracket r_hi < 0, not derived. Response:
   docstrings now say so explicitly.
2. Example is unrealistic (90% unemployment, r_lo = -0.3995, r ≈ -0.25). Response:
   disclosed in the module header.
3. `0 < ∫a` in `slack_equilibrium` is redundant (follows from ∫a = L k(r)). Kept as a
   convenience conjunct.
4. `policy_le_max` holds for every feasible choice; the bound on the cap is stronger
   than "never binds" (the equilibrium is also one of the uncapped economy) — not
   formalized; noted as open.
