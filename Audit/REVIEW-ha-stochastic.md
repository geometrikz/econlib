# Review record: Ramsey global convergence, stochastic plans, invariant distributions, stationary wealth distributions (2026-11-23)

Scope:
- `Macro/Growth/RamseyGlobal.lean`
- `Macro/DP/StochasticPlan.lean`
- `Macro/DP/InvariantMeasure.lean`
- `Macro/DP/StochasticConcavity.lean`
- `Macro/DP/StationaryDist.lean`
- `Macro/HA/StochSavings.lean`

Frozen headlines: `EconLean/Audit/Statements/HAStochastic.lean` (15 theorems).
Blueprint: `blueprint/src/chapters/stochastic_ha.tex`.

References:
- Stokey–Lucas–Prescott (SLP) ch. 6, 9, 12, 13
- Acemoglu ch. 6
- Aiyagari (1994)
- Huggett (1993)
- Chamberlain–Wilson (2000)
- Brock–Mirman (1972)

## Step 1: context-isolated adversarial review

The reviewer was a fresh agent. It saw only a statements file, with proofs and comments stripped, plus the
definitions of `RCKModel` and `StochDynProg` as context. The review ran in two rounds.

### Round 1 findings and resolutions

| Declaration | Finding | Severity | Resolution |
|---|---|---|---|
| `global_convergence` | Faithful, but missing monotone convergence and uniqueness of k* | low | Both added to the conclusion |
| `Inada` | No f'(∞) condition | low | Docstring: the cap f(k̄) ≤ k̄ gives f'(k̄) < 1/β |
| `ConcaveReturnStrictInChoice` | Deviates from SLP 9.7 (neither condition implies the other); only weak concavity of V | med | Docstring states the deviation and why (9.7 fails for the income fluctuation problem) |
| `StochDynProg.exists_stationary`, `StochSavings.exists_stationary` | Existence is satisfied by δ₀ when h(0,z) = 0 (Brock–Mirman) | high | **Claims downgraded.** The docs now say "existence only, possibly degenerate". The non-degenerate ergodic set (SLP 13.3–13.5) and uniqueness (SLP 12.12) are listed as open |
| `brockMirmanExample` | Hollow as a non-degeneracy witness | high | Relabelled as a witness that the hypotheses can be met, not that the distribution is non-degenerate |
| `aiyagariExample` | β = 1/2 is very impatient | med | β = 9/10 (βR < 1) |
| `StochSavings` | Asset cap k̄ is exogenous; the endogenous bound (βR < 1) is not derived | med | Documented deviation |
| `stateAt`, `IsFeasible`, `payoffN`, `expectedPayoff`, `isGreatest_expectedPayoff`, `policy_of_optimal`, `IsFeller`, `Kernel.Invariant`, `exists_invariant_of_feller`, `policyKernel`, `exists_continuous_policy`, envelope/Euler/`lt_policy` | Faithful | – | – |

### Round 2

The reviewer accepted all resolutions under "fix wrong statements, or downgrade claims honestly". No blockers remain.
It suggested an optional `h_le : h(k̄, z) ≤ k̄` lemma, which would make it visible where the cap is slack.

## Open items

- Non-degenerate invariant distribution for stochastic growth: needs g(k,z) > k near 0 (SLP 13.3–13.5).
- Uniqueness and stability of the stationary distribution (Hopenhayn–Prescott, SLP 12.12).
- Endogenous asset bound for βR < 1 (Schechtman–Escudero, Chamberlain–Wilson).
- SLP 9.5 at later dates: "almost surely" (here: first period only).
- Aiyagari / Huggett stationary equilibrium existence. This needs the policy to be continuous in the interest rate, upper hemicontinuity of the invariant-measure correspondence, and boundary conditions on aggregate saving.

## Step 2: comparator and reverifiers

- The frozen-statement file builds within the full `lake build` (5912 jobs), with no warnings.
- `#print axioms` on all 15 frozen theorems: each uses only `[propext, Classical.choice, Quot.sound]`.
- `leanchecker` exited 0 on every new module and on the audit file.
- `nanoda_bin` 0.4.17, run on a `leanexport` of the frozen theorems plus `aiyagariExample`, `brockMirmanExample`, `policyKernel` and `expectedPayoff`, checked 43,701 declarations with no typechecker errors. It printed one pretty-printer message, "Unable to print axioms", which is benign; earlier rounds printed the same message.
