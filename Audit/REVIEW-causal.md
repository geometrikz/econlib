# Review: OLS algebra and causal identification (Econometrics/)

Files: `EconLean/Econometrics/OLS.lean`, `EconLean/Econometrics/Causal/{Basic,
PotentialOutcomes, Unconfoundedness, LATE, DiD, TWFE, RD, Bounds, Witnesses}.lean`.
Blueprint: `blueprint/src/chapters/econometrics.tex`. Date: 2026-11-23.

## Step 1: context-isolated adversarial review

Two fresh agents, each given only a statement-only extract (comments stripped,
proofs replaced) plus the canonical sources: Hayashi ch. 1, Davidson–MacKinnon
Thm 2.1, Angrist–Pischke §2–5, Imbens–Rubin, Rosenbaum–Rubin 1983, Imbens 2004,
Imbens–Angrist 1994, Roth et al. 2023, de Chaisemartin–D'Haultfœuille 2020,
Hahn–Todd–van der Klaauw 2001, Imbens–Lemieux 2008, Manski 1989/1990.

**Round 1.** No statement wrong. Fixed:
1. `MeanUnconfounded` was guarded by stratum positivity only, so on a null cell
   the junk `condMean = 0` forced `E[Y_d | X = x] = 0`, and the adjustment
   theorems silently relied on that. Now guarded by cell positivity, and
   `integral_potential_eq_adjustment` / `ate_eq_adjustment` assume `Overlap`.
2. `ols_inr_eq` had a redundant rank hypothesis on `M₁X₂`; now derived
   (`isUnit_det_gram_annihilator_mul`).
3. IPW generalised to both arms (`ipw`) with the ATE form (`ate_eq_ipw`).
4. Witnesses added for unconfoundedness, DiD and fuzzy RD; `late_witness` now
   states integrability and `late = 2`.
5. Statement-extraction bug (`let` inside statements) fixed; both truncated
   statements re-reviewed in round 2.

**Round 2** (on the revised files). No statement wrong. Applied: dropped the
redundant `X₁` rank hypothesis from `ols_inr_eq` (`isUnit_det_gram_left`);
strengthened `sharp_rd_not_identified_without_continuity` to state continuity of
the other three functions and the jump of `m₀'`; `FuzzyRD.example₁_witness` now
states the limits, the raw outcome jump `3/2` and Wald ratio `3`.

| Declaration(s) | Verdict |
|---|---|
| `isLeastSquares_iff_normalEquations`, `isUnit_det_gram_iff`, `isLeastSquares_iff_eq_ols`, projection lemmas | faithful |
| `fwl`, `ols_inr_eq` | faithful (more general: any least-squares `b`) |
| `ols_omitted` | faithful with documented deviation (in-sample algebraic OVB) |
| `integral_ols` | faithful with documented deviation (fixed design) |
| `diffInMeans_eq_att_add_selectionBias`, `diffInMeans_eq_ate`, `att_eq_ate` | faithful |
| `ate_eq_adjustment`, `ipw`, `ate_eq_ipw` | faithful with documented deviation (discrete X, mean independence: weaker hypothesis) |
| `firstStage_eq`, `reducedForm_eq`, `wald_eq_late` | faithful (exclusion built into the encoding) |
| `did_eq`, `did_eq_att` | faithful (no-anticipation in mean: weaker hypothesis) |
| `twfe_eq_weighted_sum`, TWFE `Example.*` | faithful with documented deviation (balanced, equal cell sizes, cell means; exact additive `Y(0)`) |
| `sharp_rd`, `sharp_rd_identified`, `fuzzy_rd`, `fuzzy_rd_ratio` | faithful with documented deviation (conditional-mean primitives) |
| `manski_bounds`, `manski_sharp`, `manski_ate_bounds` | faithful |
| witnesses | faithful; see open items |

**Open (optional, not blocking):** unconfoundedness witness has no
within-stratum variation; DiD witness is homogeneous; sharpness of the ATE
Manski interval and separate outcome supports; TWFE with an error term
(dCDH's common trends in expectation); Rosenbaum–Rubin Thm 3 (propensity-score
sufficiency); Goodman-Bacon decomposition; Gauss–Markov and OLS variance.

## Step 2: machine checks
- `#print axioms` on 24 headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker`: passes on all ten modules.
- `nanoda_bin` 0.4.17 on a `leanexport` of all 187 blueprinted declarations: 36,983 declarations, no typechecker errors.
- `lake build` of the whole library: no warnings.
- Comparator (`verify/check.sh`): to be run by the integrator after regenerating `challenge/`.
