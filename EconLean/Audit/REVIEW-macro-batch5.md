# Review record: macro batch 5 (consumption, AD vs Radner, Lucas tree, PIH, NK) and fixes to batches 3–4

Date: 2026-11-23. Files:
`Macro/Consumption/Precautionary.lean`, `Macro/Consumption/PIH.lean`,
`Finance/SequentialMarkets.lean`, `Finance/LucasTree.lean`,
`Macro/NK/ThreeEquation.lean`; fixes in `Macro/Labor/HosiosDiscounted.lean`,
`Macro/Labor/DMP.lean` (doc), `Macro/Growth/Romer.lean`,
`Macro/Banking/DiamondDybvig.lean`, `Macro/Misallocation.lean`,
`Macro/Hulten.lean` (title). Frozen statements: `Audit/Statements/MacroBatch5.lean`
(23 theorems); `Audit/Statements/GrowthFinance.lean` updated for the Hosios caps;
`Audit/IndependentFindings.lean` I5 now shows the bad path is infeasible.

## Step 0: findings from the independent review (Audit/REVIEW-independent.md, reviewer F)

| Finding | Action |
|---|---|
| I5: discrete Hosios `Feasible`/`IsSearchEqm` allow `q(θ) > 1`, `f(θ) ≫ 1` | Fixed: both now require `f(θ) ≤ 1` and `q(θ) ≤ 1`; `isSearchEqm_iff` carries the bounds; `hosios`, `isOptimal_stationary`, `welfare_lt` take `q(θp) ≤ 1`; example proves `q(θp) ≤ 1` (θp ≥ 1/16 from the JC equation). |
| Continuous DMP `hosios` only at r = 0 | Docstring now says so and points to `DMP.Discrete.hosios`. |
| DD suspension only a payoff inequality | Added `SuspensionGoodEquilibrium`, `SuspensionRunEquilibrium`, `suspension_unique`. |
| HK TFP formula absent | Added `tfprAvg`, `tfp_eq_hk` (HK eq. (16)); log-normal formula still open. |
| Romer equilibrium growth defined, not derived | Added `household_optimal` (log household with asset income at the free-entry return grows at `eulerGrowth`); full decentralized equilibrium still open. |
| Hulten only two CD examples | Title and header say so; general network theorem still open. |

## Step 1: context-isolated adversarial statement review

One fresh agent saw only statement extracts (proofs elided, no thread context) and
the canonical references. Verdict: **nothing false**. Findings and responses:

1. Romer `household_optimal` has no wage income; growth conjunct is `cstar_succ`.
   Response: docstring now states it derives the wealth-only household's Euler
   growth, not the equilibrium path. Open item.
2. DMP rates are constrained, not capped by `min(1,·)`; at θ = 0 `q(0) = 0` is junk.
   Response: documented; θ = 0 means no vacancies, so the cap is vacuous there as
   it should be. Capped-rate variant open.
3. `existsUnique_searchEqm` assumes existence. Response: by design (an economy whose
   JC root breaks a bound has no equilibrium); documented.
4. `tfp_eq_hk` holds for any positive labour vector. Response: documented that
   `tfp`/`tfprAvg` are TFP / HK's average only for `IsAlloc`; labour-only.
5. `seqBudget_adBudget` needs `m ≥ 0`. Response: `IsStatePrice` requires `m ≫ 0`
   (reviewer could not see it). No change.
6. HJ only for the tree's return. Response: added general `hj_bound` for any
   return with `E[m r] = 1`.
7. DD "unique" only rules out the full run. Response: partial runs are ruled out
   by `suspension_waiting_strictly_better` (all `f ≥ λ`); documented.
8. Precautionary: optima assumed; only risk vs certain mean. Response: documented.
9. PIH: `u` differentiable on ℝ (no log/CRRA); no consumption function.
   Response: documented (LQ setting).
10. NK deterministic. Response: documented; `forward`, `det`, `trace` and
    `taylor_principle` confirmed against a hand derivation (Bullard–Mitra).

## Step 2: machine checks

- `#print axioms` on all 23 frozen theorems: `[propext, Classical.choice, Quot.sound]` only.
- `leanchecker`: exit 0 for the ten touched modules and the frozen file.
- `nanoda` on the export of the frozen theorems: 27,571 declarations, no
  typechecker errors (one pretty-printer message "Unable to print axioms", as in
  earlier batches).
- Full `lake build EconLean`: warning-free.
- Comparator / `verify/check.sh`: to be run by the integrator after regenerating
  the challenge (`python3 verify/make_challenge.py`); not available in this sandbox.
