# Review: Gauss–Markov, Goodman-Bacon, extremum estimators, GMM asymptotics, SVAR restrictions, BLP

Files: `EconLean/Econometrics/GaussMarkov.lean`, `Causal/GoodmanBacon.lean`,
`Asymptotics/{Extremum,GMMAsymptotics}.lean`, `TimeSeries/SVARRestrictions.lean`,
`Structural/BLP.lean`. Blueprint: `blueprint/src/chapters/econometrics3.tex`. Date: 2026-11-23.

## Step 1: context-isolated adversarial review

One fresh agent, given only a statement-only extract (`verify/strip_proofs.py`) plus Mathlib
sources, against Hayashi ch. 1, 3, 7; Newey–McFadden 1994; Hansen 1982; Goodman-Bacon 2021;
Blanchard–Quah 1989; Uhlig 2005; RWZ 2010; Kilian–Lütkepohl ch. 10, 13; Berry 1994; BLP 1995;
Berry–Gandhi–Haile 2013. Full table: `independent-econometrics3-statement_review.md`.

**Result: no false statement, no vacuous hypothesis set; junk-value guards (`hX`, `hA`, `hfin`,
`hden`, `hrank`) judged correct.** Applied:
1. `TWFE.pairCoef_split` (new): the pair coefficient as `s·(ΔȲ_P − ΔȲ_A) + (1−s)·(ΔȲ_P − ΔȲ_B)`,
   separating the not-yet-treated comparison from the "forbidden" already-treated one.
2. `Asymptotics.z_estimator_asymptotic`: the mean-value expansion now only needs to hold with
   probability tending to one (new tool `tendstoInMeasure_sub_of_eq_near_off`).
3. `OLS.cov_linear`: dropped the unneeded hypothesis `C X = I`.
4. Docstrings: `mle_consistent` states that the likelihood enters only via `hgap`; SVAR sign
   restrictions are on impact only and only RWZ's rotation characterisation is used.

Documented, not changed (open items):
- Limit covariances are not computed: `z_estimator_gaussian` / `gmm_limit_gaussian` only say the
  limit is Gaussian (a linear image); linking to `multivariateGaussian 0 (H⁻¹ΣH⁻ᵀ)` and to
  `GMM.avar` (beyond the algebraic `avar_eq_sandwich`) is open.
- MLE: deriving `hgap` from densities (`E log f_θ₀ − E log f_θ = KL`) is open; ULLN (F25) and the
  multivariate CLT (F27) are hypotheses by design (Coretto 2026).
- BLP: existence (surjectivity) for the mixed logit and the BLP contraction are open; consumer
  types are a finite mixture.
- Goodman-Bacon: decomposition is over unit pairs (equal cell weights); the timing-group version
  with `n_k n_l` weights is open.
- SVAR: horizon-K sign restrictions, RWZ rank condition and Haar draws are open.
- Gauss–Markov: fixed design; `Cov(b, e) = 0` and `E[s²] = σ²` are open; witness has `n = Unit`.
- GMM: variance estimation, J-test, two-step and nonlinear GMM are open.

## Step 2: machine checks
- `#print axioms` on all 84 declarations: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker`: passes on all six modules.
- `nanoda_bin` 0.4.17 on a `leanexport` of the 84 declarations: 52,514 declarations, no
  typechecker errors (one cosmetic pretty-printer message).
- `lake build` of the whole library: no warnings.
- `leanblueprint pdf`: builds (119 pages), no undefined references.
- Comparator (`verify/check.sh`): to be run by the integrator after regenerating `challenge/`.
