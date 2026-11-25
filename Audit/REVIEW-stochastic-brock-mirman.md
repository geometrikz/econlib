# Review: stochastic Brock–Mirman optimality (EconLean/Macro/DP/StochasticBrockMirman.lean)

Frozen statements: Audit/Statements/StochasticBrockMirman.lean
(frozen_sbm_bellman_eq, frozen_sbm_bellman_le, frozen_stochastic_brockMirman).

## Step 1: context-isolated adversarial econ review — PASS
- Plans are history-contingent (choice depends on past shocks; current z is in the state); FeasN requires
  0 < k' < A(z)k^α at every node; J is E[Σ_{t<n} β^t log c_t] under i.i.d. q (J_succ confirms no off-by-one).
- Closed form checked by hand and numerically (Bellman RHS max = V within 2e-15, argmax = αβy within 2e-8;
  deterministic case A≡1 recovers K/(1-β)).
- Optimality notion (policy payoffs → V; every feasible plan eventually ≤ V+ε) is the right one with log
  utility unbounded below; non-vacuous (policy plan feasible; example₁ instantiates Params).
- Null-probability shocks harmless. Minor WEAK: bounds limsup only (enough for optimality).
- Noted: strip_proofs.py truncated the statement of helper lemma abs_T_policy_le in the reviewer copy
  (tool defect, source file fine).

## Step 2: mechanical checks — PASS
- #print axioms: propext, Classical.choice, Quot.sound only.
- lake env leanchecker on module and frozen file: exit 0.
- nanoda: no typechecker errors.
