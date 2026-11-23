# Review record: discounted Hosios, AK, Lucas, Romer, finite-state FTAP (2026-11-23)

Files: `EconLean/Macro/Labor/HosiosDiscounted.lean`, `EconLean/Macro/Growth/AK.lean`,
`EconLean/Macro/Growth/Lucas.lean`, `EconLean/Macro/Growth/Romer.lean`,
`EconLean/Finance/AssetPricing.lean` (plus a docstring pointer in `Macro/Labor/DMP.lean`).
Frozen statements: `EconLean/Audit/Statements/GrowthFinance.lean` (17 theorems).
Blueprint: `blueprint/src/chapters/{hosios_discounted,growth_endogenous,finance}.tex`.

## Step 1: context-isolated adversarial review
Each round used a fresh agent that saw only the statements (proofs and comments
stripped), plus the already-reviewed DMP statements as context. References:
Pissarides (2000) §8.1, Hosios (1990), Ljungqvist–Sargent ch. 28; Acemoglu
ch. 11 and §13.1, Rebelo (1991), Lucas (1988), Romer (1990); Duffie ch. 1,
LeRoy–Werner, Cochrane ch. 4.

**Round 1:** nothing false or junk-dependent. Fixed:
1. *Blocking (Romer, definitional headline):* the equilibrium growth factor is
   the Euler-implied `β(1 + r)` at the free-entry rate; no decentralized dynamic
   equilibrium is constructed. Renamed `gEq` → `eulerGrowth`, `growth_lt` →
   `eulerGrowth_lt_optimal`, and documented. The planner side is derived
   (reduction to AK).
2. Romer: documented that `PlannerPlan` allows negative R&D (a relaxation, so
   the bound is valid for the true problem); added `plannerPlan_rd_nonneg`
   (R&D ≥ 0 iff `β R_S ≥ 1`); `scale_effect` now compares the same economy
   with a larger `L`.
3. Hosios: relaxed planner feasibility from `s + f ≤ 1` to `f ≤ 1` (added
   `s ≤ 1` to `Discrete`); documented that `IsSearchEqm` does not require
   `f, q ≤ 1`, the `θ > 0` guard against `q(0)` junk, and that strictness is for
   first-period deviations.
4. Lucas: restated the headline `lucas` as a comparison of the unique
   equilibrium and efficient paths (under the interiority condition) via the
   iff theorems; the formula comparison is `uStar_comparison`.
5. AK, Lucas, Romer: documented why optimality among `HasSum` plans is harmless
   (positive part always converges; non-summable plans have utility −∞).
6. FTAP: documented that `ftap_sdf` allows any positive weights π.

**Round 2:** nothing false or vacuous. Applied: renamed `scale_effect` →
`eulerGrowth_strictMono_L` with a docstring saying it is a property of the
Euler formula; strengthened the `eulerGrowth_lt_optimal` docstring; documented
symmetric machine use, possible negative growth, and the Lucas corner case.

| Area | Verdict |
|---|---|
| Discounted Hosios: Bellman equilibrium ⇔ job creation at `r = 1/δ − 1`, existence/uniqueness, planner optimum over all feasible paths (verification with `V(u) = α − λu`), strict for first-period deviations, Hosios iff `β = η` for every `r > 0` | faithful with documented deviation (discrete time; `f(θp) ≤ 1` assumed; stationary equilibrium) |
| AK: constant growth `sA − δ`, no convergence, optimal log saving `c = (1−β)Rk`, growth `βR` | faithful |
| Lucas: equilibrium = constant `(1−β)(1+B)/B`, efficient = `u*((1+γ)β/(1−β))`, equilibrium growth strictly too low iff `γ > 0` | faithful with documented deviation (human capital only, log utility, interior case) |
| Romer: demand, monopoly markup `p = 1`, `π = aL`, free entry `r = ηaL`, planner `x_S > L`, planner = AK with `R_S`, Euler growth < optimal, scale effect of the formula | faithful with documented deviation (equilibrium growth is Euler-implied, not a constructed dynamic equilibrium) |
| FTAP: no arbitrage ⇔ strictly positive state prices (Stiemke, via Hahn–Banach), SDF form, complete ⇔ unique state prices | faithful |

Open follow-ups: construct the decentralized Romer equilibrium (household with
wage and asset income); CRRA utility in AK/Lucas/Romer; Lucas with physical
capital; risk-neutral measure form of FTAP with a risk-free asset; uniqueness
of the AK optimum; strict inferiority of later-period deviations in Hosios.

## Step 2: proof checks
- `#print axioms` on all 17 frozen headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker`: passes on all five new modules, on `Macro.Labor.DMP` and on `Audit.Statements.GrowthFinance`.
- `nanoda_bin` 0.4.17 on a `leanexport` of the frozen theorems: 28,703 declarations, no typechecker errors (one pretty-printer message, not a check failure).
- Comparator: not reachable from the cloud container; stand-in is `Audit/Statements/GrowthFinance.lean`.
- Build: every module builds with no warnings.
- Blueprint: all 126 `\lean{}` names resolve (`#check`), labels unique, every `\uses` resolves; `plastex` web build of the full blueprint with the new chapters produces no LaTeX errors.
