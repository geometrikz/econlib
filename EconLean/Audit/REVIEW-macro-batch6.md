# Review record: macro batch 6 (2026-11-23)

Files: Macro/NK/Shocks.lean, Macro/NK/BlanchardKahn.lean, Macro/ProductionNetworks.lean,
Macro/BaqaeeFarhi.lean, Macro/Fiscal/ChamleyJudd.lean,
Macro/NK/StickyInformation.lean, Macro/Climate/SocialCostCarbon.lean.
Frozen statements: Audit/Statements/MacroBatch6.lean (16).

## Step 1: context-isolated adversarial statement review
The referee saw statements and docstrings only. They re-derived the closed forms
(discretion, star Domar weights, sticky-information output, CES reduced form,
GHKT kernel) and found no false statement.

| # | Finding | Severity | Resolution |
|---|---------|----------|------------|
| 1 | `scc` converted welfare at 1/Y₀ although C = (1−s)Y and there is no capital feedback, so the GHKT γY₀ form came from a convention | MISLEADING | `scc` is now in consumption units (−C₀·ΔW′(0)) and `scc_eq` gives γC₀·kernel. The docstring explains that GHKT's capital feedback (s = αβ) turns γC₀ into γY₀, and that Ỹ is exogenous here. |
| 2 | `divine_coincidence` would be false if `Model` allowed σ = 0 | check | `Model` carries σ, κ > 0 and 0 < β < 1 as fields; the docstring now says so. |
| 3 | `no_firstBest_of_costPush` is immediate | note | The docstring now says so. |
| 4 | Discretion targeting rule is imposed, not derived | note | The docstring now says so. |
| 5 | BK orientation z_{t+1} = Mz_t | note | No link to `IsEquilibrium` yet; any future link must invert. |
| 6 | `hulten` lacked z > 0; star bound vacuous at a = 0; `aggVar` is a definition | MINOR | Added z, z′ > 0 and a > 0. The `aggVar` docstring now gives the i.i.d. interpretation. |
| 7 | Baqaee–Farhi θ = 1 is a junk value | MINOR | Documented; every theorem assumes θ ≠ 1. |
| 8 | Chamley–Judd convergence assumption is what Straub–Werning violate | note | Stated in the docstring. |
| 9 | Sticky info uses level paths; inflation-inertia results are not captured | note | Stated in the docstring. |

## Step 2: proof checks
- `#print axioms`: all 56 theorems use only [propext, Classical.choice, Quot.sound].
- leanchecker: all 7 modules and the frozen-statements module return rc = 0.
- nanoda: 49,781 declarations, no typechecker errors (the "Unable to print axioms" message is the known, harmless one).
- Comparator: the frozen statements compile against the library theorems.
