# Review record: Ramsey–Cass–Koopmans and stochastic DP foundations (2026-11-23)

Scope: `Macro/DP/Monotone.lean`, `Macro/Growth/Ramsey.lean`, `Macro/DP/Stochastic.lean`,
`Macro/DP/MarkovChain.lean`, `Macro/DP/StochasticExamples.lean`, and the new
`euler_transversality_along` in `Macro/DP/SequenceProblem.lean`. Frozen headlines:
`EconLean/Audit/Statements/RamseyStochastic.lean` (15 theorems).

References: Stokey–Lucas–Prescott (SLP) ch. 4, 6, 9, 11; Acemoglu ch. 8; Ljungqvist–Sargent ch. 3, 11.

## Step 1: context-isolated adversarial review

The reviewer was a fresh agent that saw only a statements file, with comments and proofs stripped.
It had no thread context. There were two rounds.

### Round 1 findings and fixes

| # | Finding | Severity | Fix |
|---|---------|----------|-----|
| 1 | Ramsey examples were hollow: they quantified over an arbitrary `g` rather than the model's policy | high | Both examples now require `∀ k, policy k = {g k}` |
| 2 | `modified_golden_rule` is only a necessary condition, with hypotheses about the endogenous `g`, so nothing showed that a steady state exists | high | Added the converse `steady_state_of_modified_golden_rule`: βf′(k)=1 and c>0 imply `g k = k`, plus an example showing k* = 1/16 for √-utility/√-technology with β = ½ |
| 3 | `doeblin` gave convergence but did not state uniqueness of the invariant distribution | medium | Uniqueness is now an explicit conjunct |
| 4 | `tvDist` was the L¹ distance, which is twice total variation | medium | Renamed to `l1Dist`, with the 2×TV convention documented |
| 5 | `modified_golden_rule` had redundant hypotheses (u′>0, k<k̄) | low | Dropped; they are derived inside the proof |

The converse in #2 needed `euler_transversality_along` (SLP 4.15). It asks for the supergradient and the F_x ≥ 0 condition only along the candidate plan.

### Round 2

Round 2 found every new or changed declaration faithful and non-hollow. It checked:

- `steady_state_of_modified_golden_rule`
- `StrictConcaveOn.le_add_deriv`
- `modified_golden_rule`
- the three examples
- `doeblin` and `l1Dist`
- `euler_transversality_along`

## Documented deviations / open items

- Global convergence to the interior k* is not proved. The library proves convergence to *some* fixed point of g, and that k* is a fixed point; it does not rule out convergence to 0 (Inada conditions are not assumed).
- Strict monotonicity of g and monotone consumption are not proved.
- The stochastic Bellman equation uses finite Z with the discrete topology. The sequence-problem link, the principle of optimality (SLP 9.2–9.5), is open.
- Doeblin is assumed in its one-step, all-entries ≥ ε form, a special case of SLP 11.4. The N-step version is open.
- Invariant distributions for continuous-state stochastic growth (F12) and linear difference systems (F14) are not done.

## Step 2: comparator and reverifiers

- Frozen-statement file `Audit/Statements/RamseyStochastic.lean`: each statement is copied verbatim and closed by the library theorem. It builds in the full `lake build` (5332 jobs), which is warning-free.
- `#print axioms` on all 15 frozen theorems: each depends only on `[propext, Classical.choice, Quot.sound]`.
- `leanchecker` (exit 0, no output) on each of Monotone, Ramsey, Stochastic, MarkovChain, StochasticExamples, SequenceProblem, BrockMirman, and Audit.Statements.RamseyStochastic.
- `nanoda_bin` 0.4.17 on a `leanexport` of the 15 frozen theorems plus `RCKModel.sqrtExample`, `StochDynProg.value` and `l1Dist`. It checked 22,979 declarations with no typechecker errors. There was one pretty-printer message, "Unable to print axioms", which is not a check failure; the DP round saw the same message.
