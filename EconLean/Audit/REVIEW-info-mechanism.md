# Review: information economics, mechanism design, repeated games, matching (2026-11-23)

Files: `Information/{Lemons,Signaling,Screening,MoralHazard}`, `Mechanism/{Revelation,VCG,Myerson,OptimalMechanism,BilateralTrade}`,
`Games/Repeated`, `Matching/GaleShapley`. Frozen statements: `Audit/Statements/InfoMechanism.lean`.

## Step 1: context-isolated adversarial review
A fresh agent saw only statement files (proofs replaced by `sorry`) and the imported definitions.
Full report: `REVIEW-info-mechanism-isolated.md`. Verdict: **no WRONG statements**.

| Finding | Class | Disposition |
|---|---|---|
| Lemons docstring claims an efficiency loss, but `r(θ) = θ` means no gains from trade | OVERCLAIM | Fixed: docstring now says no surplus is lost here; the `r(θ) < θ` welfare version is listed as not formalized. |
| `postedPrice_optimal` called "optimal" without proving the posted price is IC/IR (needs monotone `θ`) | OVERCLAIM | Fixed: renamed claim to a revenue bound; added `postedPrice_isOptimal` (monotone `θ` ⇒ IC ∧ IR ∧ bound), frozen. |
| `postedPrice_rent_eq` docstring mentions monotonicity it does not need | NIT | Fixed. |
| Signaling docstring bounds missing `− c 0 θ`; pooling "iff" | NIT | Fixed. |
| VCG cites MWG 23.C.5 (Green–Laffont converse, not formalized) | NIT | Fixed citation. |
| `revenue_equivalence` is the single-agent interim form | WEAK | Documented in module and blueprint. |
| Folk theorem covers pure profiles only, not the convex hull; `IsRepeatedSPE` meaningful only for bounded payoffs | WEAK | Documented; all theorems assume bounded payoffs. |
| Screening omits downward distortion `qL ≤ qL^FB` | WEAK | Open. |
| `sellTheFirm` does not prove first-best optimality; full insurance uniqueness under strict convexity | WEAK | Open. |
| Bilateral trade: add an efficient + DSIC (VCG) witness to show BB is what fails | WEAK | Open. |
| Gale–Shapley: all partners acceptable; `huw` not needed for existence | WEAK | Open (IR/unacceptable partners is a natural extension). |

## Step 2: machine checks
* `#print axioms` on all 68 theorems: only `propext`, `Classical.choice`, `Quot.sound`.
* `lake env leanchecker` on all 11 modules: pass.
* `leanexport` of the 68 theorems and dependencies + `nanoda`: 36,571 declarations, no typechecker errors.
* `lake comparator` / challenge regeneration: left to the integrator (`verify/check.sh`).
