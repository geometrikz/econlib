# Review: IV, GMM, synthetic control, shift-share, asymptotics, VARs (Econometrics/)

Files: `EconLean/Econometrics/{IV,GMM}.lean`, `Causal/{SyntheticControl,ShiftShare}.lean`,
`Asymptotics/{DeltaMethod,OLSConsistency}.lean`, `TimeSeries/{VAR,SVAR}.lean`, and the changed
`Causal/RD.lean` (`sharp_rd_identified`). Blueprint: `blueprint/src/chapters/econometrics2.tex`
(and the RD entry in `econometrics.tex`). Date: 2026-11-23.

## Step 1: context-isolated adversarial review

One fresh agent, given only a statement-only extract (`verify/strip_proofs.py`: comments stripped,
proofs replaced by `sorry`) plus Mathlib sources to check definitions, against Hayashi ch. 2–3,
Hansen 1982, Newey–McFadden 1994, Wooldridge ch. 4–5, van der Vaart Thm 2.7/3.1, ADH 2010,
BHJ 2022, GPSS 2020, HTvdK 2001, Hamilton ch. 10–11, Lütkepohl §2.1, Sims 1980, Kilian–Lütkepohl
ch. 8. Full table: `independent-econometrics2-statement_review.md`.

**Result: no false statement, no vacuous hypothesis set.** Applied:
1. `SyntheticControl.FactorModel.estimator_eq_effect_observed`: pre-period fit on *observed*
   outcomes plus no anticipation (the reviewer noted `hfit` was on latent `Y(0)`).
2. `RD.sharp_rd_identified`: agreement only on a punctured neighbourhood (`∀ᶠ x in 𝓝[≠] c`), and
   the conclusion now identifies `m₁ c` and `m₀ c` separately (this also answers the earlier
   independent review: continuity is now genuinely needed).
3. `Asymptotics.tendstoInDistribution_const_iff`: both directions of van der Vaart Thm 2.7(iii).
4. `SVAR.sign_normalization_needed`: `diag(−1, 1)` shows triangularity alone does not identify.

Documented, not changed (open items):
- VAR results assume bounded shock paths; i.i.d. Gaussian shocks are a.s. unbounded. Extending
  to a growth class (e.g. `‖u_t‖ ≤ M(1+|t|)^p`) or an L² version is open. Stability is
  `∑‖A^j‖ < ∞`; the bridge to the eigenvalue condition (spectral radius < 1) and VAR(p)
  companion form are open.
- GMM: `avar` is the algebraic sandwich; asymptotic normality, two-step GMM and the J-test are open.
- Shift-share: numerator mean only; BHJ consistency (∑ s_n² → 0) is open.
- Delta method is scalar; the multivariate (`HasFDerivAt`) version is open.
- `ols_consistent_witness` is degenerate (point mass); a nondegenerate witness is open.
- Redundant hypotheses: `hZ` in `IV.tsls_eq_ols_fitted` (junk inverse makes both sides 0 when
  singular) and in `IV.tsls_eq_iv` (follows from `hZX`); the first conjunct of
  `GMM.identified_iff` is always true. Harmless.

| Declaration(s) | Verdict |
|---|---|
| `IV.momentSolutions_eq_singleton_iff`, `tsls_eq_ols_fitted`, `tsls_eq_iv` | faithful |
| `GMM.identified_iff`, `estimator_isMin`, `estimator_of_exact`, `tsls_eq_estimator` | faithful |
| `GMM.avar_inv`, `avar_sub_posSemidef` | faithful (algebraic part of Hayashi Prop. 3.5) |
| `SyntheticControl.*` | faithful with documented deviation (noiseless model) |
| `ShiftShare.ssiv_eq_shockIV`, `bartik_eq_sum_rotemberg` | faithful |
| `ShiftShare.integral_sum_bartik_mul(_eq_zero)` | faithful, weak (mean of numerator) |
| `Asymptotics.delta_method`, `delta_method_clt`, `tendstoInDistribution_const_iff` | faithful (scalar) |
| `Asymptotics.ols_consistent` | faithful (i.i.d. special case of Hayashi Prop. 2.1) |
| `VAR.*` | faithful with documented deviation (bounded shocks, summability form of stability) |
| `SVAR.recursive_existsUnique`, `not_identified`, `sign_normalization_needed` | faithful |

## Step 2: machine checks
- `#print axioms` on 31 headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker`: passes on all nine modules (eight new plus RD).
- `nanoda_bin` 0.4.17 on a `leanexport` of all 287 blueprinted econometrics declarations (both chapters):
  57,399 declarations, no typechecker errors (one cosmetic pretty-printer message, "Unable to print axioms").
- `lake build` of the whole library: no warnings.
- Comparator (`verify/check.sh`): to be run by the integrator after regenerating `challenge/`.
