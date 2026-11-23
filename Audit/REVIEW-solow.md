# Review record: the Solow growth model (2026-11-23)

File: `EconLean/Macro/Growth/Solow.lean`.
Frozen statements: `EconLean/Audit/Statements/Solow.lean`.

## Step 1: context-isolated adversarial review
Reviewer saw only the statements (proofs and comments stripped); reference
Acemoglu ch. 2 (Assumptions 1–2, Props 2.2, 2.3, 2.5), Barro–Sala-i-Martin ch. 1,
Romer ch. 1. Two rounds, each by a fresh agent.

**Round 1:** no wrong statements. Findings applied:
1. A concave `f` can jump at 0 (e.g. `f 0 = 0`, `f k = 1 + √k`), so the class
   was wider than Acemoglu's. Added field `continuousWithinAt_zero`, and the
   matching hypothesis to `of_deriv`.
2. Prop. 2.5 is strict: added `path_strictMono_of_lt`, `path_strictAnti_of_gt`
   (strictly monotone and never reaching `k*`).
3. Added the trivial steady state: `next_zero`, `fixedPoint_iff`.
4. Added comparative statics (Prop. 2.3) in `s`, `n`, `δ`.
5. Widened parameter ranges to `s ∈ (0,1]`, `δ ∈ [0,1]`, `n > −1`, `n + δ > 0`.

**Round 2 (on the revised file):** all declarations faithful, or faithful with
documented deviation; no blocking fixes. Applied: deviations written into the
file header; added `tendsto_output` and conditional convergence
(`growthRate_strictAntiOn`).

| Declaration | Verdict |
|---|---|
| `NeoclassicalProduction` | faithful with documented deviation (average-product Inada, no differentiability; equivalent for differentiable concave f) |
| `continuousOn`, `avg_strictAntiOn`, `avg_pos`, `pos`, `strictMonoOn` | faithful |
| `of_deriv` | faithful (bridge from Acemoglu's assumptions; `hpos` redundant but kept) |
| `Economy`, `next`, `path`, `IsSteadyState` | faithful with documented deviation (wider parameter ranges; Acemoglu is n = 0) |
| `isSteadyState_iff`, `existsUnique_steadyState` (Prop. 2.2) | faithful |
| `tendsto_path`, `path_strictMono_of_lt`, `path_strictAnti_of_gt`, `exists_globally_stable_steadyState` (Prop. 2.5) | faithful |
| `fixedPoint_iff`, `next_zero` | faithful |
| `steadyState_strictMono_s`, `steadyState_strictAnti_n`, `steadyState_strictAnti_δ` (Prop. 2.3) | faithful (strict monotonicity instead of signs of derivatives) |
| `cobbDouglas_neoclassical`, `cobbDouglas_steadyState`, `cobbDouglas_tendsto`, calibrated `example` | faithful; witness shows hypotheses are satisfiable |

Junk values: none relied on (all `f k / k` sit behind `0 < k`; rpow base is positive).
Open (optional): technology comparative statics (`A f`), golden rule,
labour-augmenting progress, converse of `of_deriv`, speed of convergence,
continuous time.

## Step 2: proof checks
- `#print axioms` on all headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker` (toolchain `bin/`): passes on `EconLean.Macro.Growth.Solow` and `EconLean.Audit.Statements.Solow`.
- `nanoda_bin` 0.4.17 on a `leanexport` of all headline and frozen theorems: 29,697 declarations, no typechecker errors.
- Comparator: not reachable from the cloud container; stand-in is `Audit/Statements/Solow.lean`.
- Build: `lake build` of both modules finishes with no warnings.
