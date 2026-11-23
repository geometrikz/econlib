# Review: production economies and bridge B0 (aggregation)

Files: GE/Production.lean, Bridges/Aggregation/{GrossSubstitutes,LawOfDemand,Gorman,Examples}.lean,
Audit/Statements/Aggregation.lean. Blueprint: chapters/ge_production.tex, chapters/aggregation.tex.

## Step 1: context-isolated adversarial review (statements only, proofs stripped)

| Item | Verdict | Action |
|---|---|---|
| ProductionEconomy, ProfitMax, wealth with shares, Feasible, Walrasian eq. | Faithful (MWG 16.B) | none |
| Production First Welfare (MWG 16.C.1) | Faithful | none |
| Production Second Welfare (MWG 16.D.1) with convex Y_j, quasi-eq. ⇒ eq. | Faithful | none |
| GrossSubstitutes, .sum (needs nonempty s), uniqueness (MWG 17.F.3) | Faithful | none |
| LawOfDemand.sum (MWG 4.C.1) | Faithful | none |
| LawOfDemand.excessWARP | Correct but vacuous on a homogeneous cone (forces z ≡ 0) | Caution docstring; non-vacuous WARP witness `zCD_warp` added |
| ExcessWARP.convex_equilibria (MWG 17.F.1) | Faithful | none |
| Gorman (all real wealth) | Faithful with deviation: MWG quantifies over w ≥ 0 | Added `AggregatesThroughWealthNonneg` + `gorman_of_aggregatesThroughWealthNonneg` |
| Examples | Production example had y = 0 only; Gorman example not budget-balanced | Added `prodEconomy2` (y = (-2,2)) and budget-balanced `xG` |

## Step 2: comparator stand-in and reverifiers

- Full build warning-free (5214 jobs, local).
- Frozen statements in Audit/Statements/Aggregation.lean closed by the library theorems; definitions pinned by `Iff.rfl`.
- `#print axioms`: only propext, Classical.choice, Quot.sound on all frozen theorems and examples.
- leanchecker: pass on Production, GrossSubstitutes, LawOfDemand, Gorman, Aggregation.Examples, Audit.Statements.Aggregation.
- nanoda: 26,417 declarations, no errors.

## Open
- SMD theorem (Debreu 1974 / Mantel) not started.
- Tâtonnement stability under gross substitutes not started.
- Brouwer hypothesis: pending geoff's decision on vendoring lean4-fixed-point.
