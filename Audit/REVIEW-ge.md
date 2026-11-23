# Review record: exchange economies, welfare theorems, core, existence (2026-11-23)

Files: `EconLean/GE/Exchange.lean`, `EconLean/GE/SecondWelfare.lean`,
`EconLean/GE/Existence.lean`, `EconLean/GE/Examples.lean`,
`EconLean/Foundations/SupportingHyperplane.lean`.
Frozen statements: `EconLean/Audit/Statements/GE.lean` (theorems, plus every
definition pinned by an `Iff.rfl` unfolding).

## Step 1: context-isolated adversarial review
The reviewer saw only statements and definitions (proofs and comments stripped,
consumer definitions included). References: MWG 15.B, 16.B–16.D, 17.B–17.C,
18.B, M.G; Debreu, *Theory of Value* §5.6.

| Declaration | Verdict |
|---|---|
| `cost_sum`, `ParetoOptimal`, `WeaklyParetoOptimal`, `IsWalrasianEquilibrium`, `Blocks`, `InCore`, `IndividuallyRational` | faithful |
| `Feasible` | faithful with documented deviation (exact clearing `∑x = ω̄`, as in MWG 15.B / 16.B; no free disposal) |
| `first_welfare_theorem` (MWG 16.C.1), `IsWalrasianEquilibrium.inCore` (18.B.2, no assumptions needed), `InCore.individuallyRational`, `InCore.weaklyParetoOptimal`, `IsWalrasianEquilibrium.individuallyRational`, Lemma 16.C.1 (`cost_ge/gt_of_mem_demand`) | faithful |
| `exists_price_support` (MWG M.G) | faithful |
| `IsPriceEquilibriumWithTransfers` (16.B.4) | faithful with documented deviation (MWG's `p·xₐ ≤ wₐ` omitted; equivalent under LNS, now proved as `IsPriceEquilibriumWithTransfers.cost_eq`) |
| `IsPriceQuasiEquilibriumWithTransfers` (16.D.1), `paretoOptimal` (16.C.1 with transfers), `second_welfare_theorem` (16.D.1), quasi ⇒ equilibrium (16.D.2), `mem_demand`, `price_nonneg`, `second_welfare_theorem_demand` | faithful (the inherited `ConvexPref` asks convexity on all of ℝ^L, stronger than MWG's ℝ^L₊: correct, slightly less general) |
| `ContinuousPref` | faithful (fixed: now quantifies only over `x ≥ 0`) |
| `priceSimplex`, `BrouwerSimplex`, `gale_nikaido_debreu`, `price_eq_zero_of_excess_supply`, `cost_excessDemand`, `IsFreeDisposalEquilibrium` | faithful (fixed: free-disposal equilibrium now requires `p ≥ 0`); general existence is conditional on `BrouwerSimplex ι`, unconditional for 2 goods |
| `exists_freeDisposalEquilibrium(_two_goods)` | faithful with documented deviation: needs demand defined and continuous on the closed simplex, so it does **not** cover strongly monotone economies (MWG 17.C.1, Cobb–Douglas). Limitation stated in the docstring and file header. |

No statement rated wrong.

Fixes made after review: `ContinuousPref` restricted to `x ≥ 0`; `0 ≤ p` added
to `IsFreeDisposalEquilibrium`; `cost_eq` lemma reconciling with MWG 16.B.4;
existence limitation documented; new non-degenerate example `asymEconomy`
(different linear tastes) where the WE `((3,0),(0,3))` is Pareto optimal by the
First Welfare Theorem and the endowment is provably *not* Pareto optimal.

Open (next steps, from the review):
1. MWG Prop. 17.C.1: existence with excess demand on `p ≫ 0` and the boundary
   condition (or Debreu's truncation), so strongly monotone economies are covered.
2. Discharge `BrouwerSimplex ι` for all nonempty `ι` by importing Brouwer (Lyu–Li / EconCSLib).
3. Derive continuity of the demand selection from preferences via Berge.
4. Existence example with a unique equilibrium that exercises the fixed point
   (the Leontief witness has every price as an equilibrium).

## Step 2: proof checks
- `#print axioms` on all headline and frozen theorems: `propext, Classical.choice, Quot.sound` only. No sorry, no custom axioms (Brouwer is a hypothesis, not an axiom).
- `leanchecker` (toolchain v4.36.0): passes on all six modules (one module per call).
- `nanoda_bin` 0.4.17 on a `leanexport` of the frozen and example theorems: 26,232 declarations, no typechecker errors (one pretty-printer message, not a check failure).
- Comparator stand-in: `Audit/Statements/GE.lean`.
- Full `lake build`: warning-free.
