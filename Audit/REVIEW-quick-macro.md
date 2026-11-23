# Review record: McCall, Hsieh–Klenow, Diamond–Dybvig, DMP, Hulten (2026-11-23)

Files: `EconLean/Macro/Labor/McCall.lean`, `EconLean/Macro/Misallocation.lean`,
`EconLean/Macro/Banking/DiamondDybvig.lean`, `EconLean/Macro/Labor/DMP.lean`,
`EconLean/Macro/Hulten.lean`.
Frozen statements: `EconLean/Audit/Statements/QuickMacro.lean` (33 theorems).

## Step 1: context-isolated adversarial review
Each round used a fresh agent that saw only the statements (proofs and comments
stripped). References: Ljungqvist–Sargent ch. 6, Hsieh–Klenow (2009) §I,
Diamond–Dybvig (1983) and Freixas–Rochet, Pissarides (2000) ch. 1 and §8.1,
Hosios (1990), Hulten (1978), Baqaee–Farhi (2019).

**Round 1:** no false or vacuous headline. Fixed:
1. *Blocking (junk value):* Diamond–Dybvig `RunIsBest` used `1 ≤ f r₁`, so at
   `r₁ = 1`, `f = 1` (where Lean's `latePay 1 = 0/0 = 0`) a run was counted as an
   equilibrium. Now `1 < f r₁`, with the boundary convention documented (the
   waiting payoff at `f = 1` is the limit `R > 1`); `runEquilibrium_iff` is now
   `↔ 1 < r₁`, matching Diamond–Dybvig. `WaitIsBest` uses `f r₁ ≤ 1`.
2. *Blocking (review tooling):* the statement extractor truncated
   `Vertical.hulten`; fixed, and round 2 reviewed it in full.
3. Added the downward-sloping Beveridge curve in `(u, v)` space: `vac`,
   `vac_strictMonoOn`, `beveridge`. `unemp` is no longer called "the Beveridge
   curve".
4. Added `isReservationWage_iff_textbook` (`w̄ − c = β/(1−β) E(w − w̄)⁺`).
5. Added Hulten for competitive equilibria of the shocked economy (now
   `Horizontal.hulten`; the planner version is `hulten_planner`).

**Round 2:** nothing blocking. Applied: removed the unused interest-rate field
from `DMP.Economy` (the rate is an argument of `jc`/`IsEquilibrium`, and
`hosios` fixes it at 0); documented that `WaitIsBest`/`RunIsBest` are not
complements; swapped the Hulten names as above.

| Area | Verdict |
|---|---|
| McCall: existence/uniqueness of `w̄`, Bellman solution and uniqueness, acceptance rule, textbook equation, `w̄` strictly rises in `c`, weakly rises under a mean-preserving spread (convex order) | faithful (finite offer distributions; negative `c` or wages allowed) |
| Hsieh–Klenow: `tfp ≤ tfpEfficient`, equality iff efficient allocation iff TFPR equalized, dispersion strictly lowers TFP, wedge allocation, TFPR ∝ 1/(1−τ), efficient iff equal wedges | faithful with documented deviation (one industry, labour only, output wedge only) |
| Diamond–Dybvig: CRRA optimum (budget, `1 < c₁* < c₂*`, optimality over positive consumption), good equilibrium iff `r₁(1−λ+λR) ≤ R`, run iff `r₁ > 1`, multiple equilibria at the optimum, suspension makes waiting strictly better | faithful with documented deviation (liquidation value 1; suspension shows deviation is unprofitable, no full suspension game) |
| DMP: unemployment flows and convergence, job creation vs Pissarides' wage curve, unique equilibrium, tightness falls in `β`, Beveridge curve, welfare, efficiency iff equilibrium at `β = η`, Hosios | faithful with documented deviation (efficiency and Hosios with the steady-state, `r = 0` planner; Pissarides §8.1 has the discounted planner) |
| Hulten: horizontal and vertical Cobb–Douglas economies; CE efficient, Domar weights (`aᵢ`; `ω` and `1`, sum `1 + ω`), `d log Y/d log Aᵢ` = Domar weight | faithful (final good is the implicit numeraire) |

Open follow-ups: Hosios with a discounted planner (`r > 0`); a full
suspension-of-convertibility game with uniqueness of the good equilibrium;
Hsieh–Klenow with capital wedges and many industries; McCall unemployment
duration and hazard comparative statics; Hulten for general production networks.

## Step 2: proof checks
- `#print axioms` on all 33 frozen headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker`: passes on all five modules and on `Audit.Statements.QuickMacro`.
- `nanoda_bin` 0.4.17 on a `leanexport` of the frozen theorems: 29,162 declarations, no typechecker errors (one pretty-printer message, "Unable to print axioms", which is not a check failure).
- Comparator: not reachable from the cloud container; stand-in is `Audit/Statements/QuickMacro.lean`.
- Build: every module builds with no warnings.
