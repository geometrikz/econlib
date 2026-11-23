# Review record: game theory (MWG Ch. 7–9), SOSD converse, risk aversion on intervals (2026-11-23)

Files: `EconLean/Games/{Strategic,Mixed,ZeroSum,Correlated,Rationalizability,Bayesian,Extensive}.lean`;
additions to `EconLean/Uncertainty/{StochasticDominance,RiskAversion}.lean`.
Frozen statements: `EconLean/Audit/Statements/Games.lean` (22 theorems) and three
new entries in `EconLean/Audit/Statements/ProducerUncertainty.lean`.

Reuse: Nash existence uses the shared Brouwer theorem (`Foundations/FixedPoint.lean`,
`brouwer_fixedPoint_continuousMap`); the minimax theorem uses Mathlib's Sion theorem
(`Sion.exists_isSaddlePointOn`); mixed strategies are the vN–M `lotteries`. EconCSLib
(Apache-2.0, Lean v4.30) was checked: its game theory covers applied/preference games, not
the MWG canon, so nothing was ported.

## Step 1: context-isolated adversarial review
The reviewer saw only statements (proofs and comments stripped by `verify/strip_proofs.py`)
and MWG / Fudenberg–Tirole / Aumann as references. Full report: `REVIEW-games-isolated.md`.

**No statement wrong.** Findings and resolution:

| # | Finding | Resolution |
|---|---|---|
| 1 | `IsBNE` allowed any prior (p = 0 makes everything a BNE) | `IsBNE` now requires `p ∈ lotteries`; `isBNE_iff_interim` takes `hp` |
| 2 | Iterated deletion used pure dominators only (MWG §8.D uses mixed) | Added `StrictlyDominatedMixed`, `isdMixed`, `IsBRSet.subset_isdMixed`, `Rationalizable.mem_isdMixed` |
| 3 | `IsDominant` lacked MWG 8.B.5's strict clause | `IsDominant` is now MWG 8.B.5; added `IsStrictlyDominant` (8.B.4) and `IsStrictlyDominant.isDominant` |
| 4 | `zermelo` excluded draws | Added `zermelo_draw` (win / draw / loss) |
| 5 | SOSD ⟹ mean-preserving spread not stated | Open (below) |
| 6 | Extensive form: perfect information, no chance nodes | Documented in the module header |
| 7 | `StrictlyDominated` vacuous when an opponent's surviving set is empty | Only reachable with infinite or empty strategy sets; theorems that matter assume finite nonempty sets. Left as is |
| 8 | Mixed BNE mixes over whole plans | Documented (Kuhn equivalence not formalized) |
| 9 | Independent beliefs (MWG) vs correlated beliefs (OR/FT) | Documented in `Rationalizability.lean` |
| 10 | No `IsSaddle` ⟺ mixed Nash of (A, −A) link; SOSD needs concavity on all of ℝ | Open |

Also from the independent reviewer thread (`Audit/REVIEW-independent.md`): risk-aversion
results were stated on all of ℝ, excluding log, √ and CRRA. Added
`riskAverseOn_iff_certaintyEquivalent_le_mean` (convex `I`) and
`riskAverseOn_iff_arrowPratt_nonneg` (open convex `I`), with a log-utility witness on (0, ∞).
"Integrated CDF ⟹ SOSD" is now `sosd_iff_integral_cdf`.

## Step 2: proof checks
- `#print axioms` on all frozen theorems in `Games.lean` and `ProducerUncertainty.lean` (22 + 31):
  `propext, Classical.choice, Quot.sound` only. No `sorry`.
- `leanchecker`: exit 0 on every Games module, `StochasticDominance`, `RiskAversion` and both audit files.
- `nanoda_bin` on a `leanexport` of all frozen theorems: 39,782 declarations, no typechecker errors.
- Full `lake build` (5856 jobs) warning-free; `leanblueprint pdf` builds with no LaTeX errors.

## Open
- SOSD ⟹ mean-preserving spread (Rothschild–Stiglitz construction).
- Pratt's theorem (comparison of two utilities) on an interval; DARA, relative risk aversion.
- Rationalizable = survives mixed ISD for two players (needs minimax/separation).
- Imperfect information: behavioural strategies, Kuhn's theorem, sequential equilibrium, PBE.
- Repeated games, folk theorems, supermodular games.
- `IsSaddle` ⟺ mixed Nash of the zero-sum game (A, −A).
