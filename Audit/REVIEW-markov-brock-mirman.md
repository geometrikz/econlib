# Review: Brock–Mirman with Markov shocks (EconLean/Macro/DP/MarkovBrockMirman.lean)

Frozen statements: EconLean/Audit/Statements/MarkovBrockMirman.lean
(frozen_mbm_a_eq, frozen_mbm_a_unique, frozen_mbm_bellman_eq, frozen_mbm_bellman_le,
frozen_mbm_a_iid, frozen_markov_brockMirman).

## Step 1: context-isolated adversarial econ review — PASS (no WRONG findings)
- Timing matches SLP ch. 9–10 / LS ch. 3: z_{t+1} ~ Q(z_t, ·), output at t+1 uses z_{t+1}; J is the
  n-period expected discounted utility conditional on today's shock.
- Intercept: a ↦ c + βQa is a β-contraction (rows sum to 1); unique fixed point; B, K, c match the
  canonical coefficients. V and g = αβA(z)k^α are the canonical value and policy.
- Numerics on example₁ (α=1/3, β=0.9, A=(1/2,2), persistence 0.9): Bellman max = V to 1e-15 with
  argmax αβy; value function iteration on a 401-point grid matches V to 1e-4; policy J_n rises to V.
- Optimality notion (policy J_n → V; limsup J_n ≤ V for every feasible plan) suits log utility.
- a_iid is a genuine consistency check against the explicit i.i.d. intercept.
- WEAK: unique argmax not stated (true by strict concavity); a_iid equates intercepts, V and policy
  follow immediately; docstrings were stripped in the reviewer copy so not reviewed there
  (module header and theorem docstrings only describe the statements above).

## Step 2: mechanical checks — PASS
- #print axioms (all six frozen theorems): propext, Classical.choice, Quot.sound.
- lake env leanchecker on module and frozen file: exit 0.
- nanoda on the exported frozen theorems: 18,436 declarations, no typechecker errors.
