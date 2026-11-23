# Review record: golden rule, technical progress, Diamond and Samuelson OLG (2026-11-23)

Files: `EconLean/Macro/Growth/GoldenRule.lean`, `EconLean/Macro/Growth/TechProgress.lean`,
`EconLean/Macro/OLG/LogHousehold.lean`, `EconLean/Macro/OLG/Diamond.lean`,
`EconLean/Macro/OLG/Samuelson.lean`.
Frozen statements: `EconLean/Audit/Statements/GrowthOLG.lean`.

## Step 1: context-isolated adversarial review
Each round used a fresh agent that saw only the statements (proofs and comments
stripped) plus the already-reviewed Solow statements; references Phelps,
Acemoglu ch. 2 and 9, Romer ch. 1–2, Barro–Sala-i-Martin ch. 1, Samuelson
(1958), Shell (1971), Ljungqvist–Sargent ch. 9.

**Round 1:** no false, vacuous or junk-value statements. Fixed:
1. *Blocking (misleading headline):* `firstWelfareTheorem_fails` was a
   conjunction of "an equilibrium exists" and "something dominates autarky".
   Added `IsCompetitiveEquilibrium R x` (prices, optimal savings, loan-market
   clearing, budget constraints, initial old), proved
   `isCompetitiveEquilibrium_iff` (equilibrium = autarky at the autarky rate),
   and restated the failure as "∃ equilibrium (R, x), ∃ feasible y strictly
   dominating x"; added `competitiveEquilibrium_dominated`.
2. Added the Diamond efficiency converse: `no_dominating_path` (R* ≥ 1+n ⇒ no
   feasible path from k* weakly improves consumption every period with a strict
   gain somewhere) and the iff `dynamicallyInefficient_iff_exists_improvement`.
3. Documented that Diamond "dominance" is aggregate consumption per worker.
4. Added the usual (weak) `ParetoDominates` and `StrictlyDominates.paretoDominates`.

**Round 2:** all declarations faithful or faithful with documented deviation;
nothing blocking. Applied: renamed `monetaryEquilibrium_paretoDominates` →
`monetaryEquilibrium_eq_golden_and_dominates` (it does not claim optimality);
generalized and renamed the Solow golden-rule comparison to
`consumption_lt_withGoldenSaving` (any `k* ≠ k_gold`); documented
stationary-only money and the missing Balasko–Shell results.

| Area | Verdict |
|---|---|
| Golden rule: `lt_tangent`, `goldenRule_lt/le`, `consumption_le/lt_goldenRule`, `goldenSavingRate_mem`, `isSteadyState_goldenRule`, Cobb–Douglas `k_gold`, `s_gold = α` | faithful (differentiability only at `k_gold`) |
| Technical progress: `TechEconomy`, `effective_eq_path`, `tendsto_effective`, `tendsto_detrended_output`, `balanced_growth` | faithful (intensive form primitive; `g > −1` allowed) |
| Log household: `logU_le_opt`, `logU_lt_opt`, `IsOptimalSaving`, `saving_isOptimal_iff` | faithful |
| Diamond: equilibrium iff law of motion, existence/uniqueness, stability (Prop 9.3), `R*` formula, dynamic inefficiency both directions (Prop 9.4) | faithful with documented deviation (canonical log/Cobb–Douglas/δ=1 case; aggregate-consumption dominance; paths from k*) |
| Samuelson: equilibrium = autarky, FWT failure, monetary equilibrium iff, money = golden rule and dominates autarky | faithful with documented deviation (log utility, constant population, stationary money, bond clearing via identical agents) |

Open follow-ups: Pareto optimality of the golden/monetary allocation and of
autarky when ω₂ ≥ βω₁ (Balasko–Shell); non-stationary monetary equilibria;
growth rate of Y/L → g from any start; generation-by-generation Pareto split in
Diamond; Diamond paths from any k₀ > k_gold.

## Step 2: proof checks
- `#print axioms` on all 16 frozen headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker`: passes on all five modules and on `Audit.Statements.GrowthOLG`.
- `nanoda_bin` 0.4.17 on a `leanexport` of the frozen theorems: 34,904 declarations, no typechecker errors.
- Comparator: not reachable from the cloud container; stand-in is `Audit/Statements/GrowthOLG.lean`.
- Build: every module builds with no warnings.
