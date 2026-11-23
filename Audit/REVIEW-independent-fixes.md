# Fixes for independent reviews J/K/L (info, mechanism, matching, partial, social choice)

Date: 2026-11-23. All changes build warning-free; full shared build passes (7240 jobs).

| Finding | Fix |
|---|---|
| MoralHazard: φ convex/monotone on all of ℝ | `fullInsurance_optimal`, `implementsHigh_cost_gt` take `ConvexOn/StrictConvexOn ℝ U φ`, `MonotoneOn φ U` on a set `U` of utility levels containing the contract's utilities and `ū+g`. Frozen statement updated. |
| Assortative: increasing differences on ℝ² | `HasIncreasingDifferences f X Y` on type sets; `becker_pam` uses `range x × range y`; log·log witness on `[1,∞)²`. Frozen statement updated. |
| Repeated: SPE trivial at δ=1 | `IsRepeatedSPE` now includes `0 ≤ δ ∧ δ < 1`. |
| `gs_blocking_lemma` dropped `w ∈ μ'(M')` | Now concluded (Roth–Sotomayor Lemma 3.5): `∃ m', Improves … m' ∧ μ' m' = some w`. |
| Myerson–Satterthwaite shared support | Already documented (full-support scope, counterexample in docstring). Unchanged. |
| `postedPrice_optimal` assumes threshold pattern | New `IsRegularDiscrete` (nondecreasing virtual values) and `postedPrice_isOptimal_of_regular`: regularity ⇒ single crossing ⇒ some posted price optimal. Regularity witness for the 3-type example. |
| `median_not_defeated` counted ties | Second conjunct now `#{y ≻ m} ≤ #{m ≻ y}`. Frozen statement updated. |
| `voluntary_underprovision` ℝ-wide hypotheses | Derivative, positivity, strict antitonicity only on `G > 0`, plus `0 < Gstar`; witness `φ = 2 log(1+G)` with equilibrium `(1,0)` and `G* = 3`. Frozen statement updated. |

Verification:
- Isolated adversarial reviewer (statement-only files): all seven revised items OK, none WEAK/WRONG. Notes: regularity is stronger than needed for one buyer (posted price optimal anyway, already `postedPrice_isOptimal`); `hGpos` redundant; harmless.
- `#print axioms`: only propext, Classical.choice, Quot.sound for all changed theorems and frozen statements.
- leanchecker: exit 0 on all 9 changed modules.
- nanoda: 18,595 declarations, no typechecker errors (one pretty-printer message, not a check failure).
- Blueprint: `leanblueprint pdf` builds (132 pages); new `\lean` names resolve.

Changed files: Information/MoralHazard, Matching/{Assortative,StrategyProof}, Games/Repeated, SocialChoice/MedianVoter, Partial/PublicGoods, Mechanism/OptimalMechanism, Audit/Statements/{InfoMechanism,PartialSocial}; blueprint chapters asyminfo, games, matching, mechanism, partial, socialchoice.
