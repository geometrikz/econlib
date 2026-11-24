# Audit: econometrics batch 8 (χ², J test, Wald test)

Files: EconLean/Econometrics/Asymptotics/ChiSquared.lean, ChiSquaredTests.lean (new);
TwoStepGMM.lean (docstring only). Blueprint: chapters/econometrics8.tex (+ one sentence in econometrics6.tex).

## Machine checks (Lean 4.36.0)
- `lake build`: success, no warnings (autoImplicit=false).
- `#print axioms`: 26/26 declarations depend only on [propext, Classical.choice, Quot.sound].
- leanchecker on both modules: exit 0.
- nanoda (59,981 declarations incl. dependencies): no typechecker errors (the usual "unable to print axioms" pretty-printer note only).
- `leanblueprint pdf`: success, no undefined references from this chapter (pre-existing `thm:beh-rw-iff` warning is unrelated).

## Adversarial statement review (context-isolated agent)
Full text: independent-econometrics8-statement_review.md. No statement found false or vacuous;
chiSq and waldStat are the standard objects; R full row rank is implied by `IsUnit (R V Rᵀ).det`.

Responses:
1. Feasible-J witness with l > k missing — OPEN (next batch): needs an overidentified data-level construction.
2. Degenerate witnesses — `wald_witness` restated: it now asserts every hypothesis of `wald_chiSq` (including a
   non-constant consistent V̂ₙ = (1 + 1/(n+1)) I₂) together with the conclusion. `two_step_jtest_chiSq_witness`
   reuses `two_step_witness`, whose statement lists all hypotheses (constant Ĝ, Ŝ: caveat kept).
3. Singular-matrix convention — documented in the ChiSquaredTests module docstring.
4. "Asymptotic size" wording — module docstring now says pointwise rejection probability under a fixed null DGP;
   uniformity, local alternatives and power are out of scope.
- Nit: `map_quadForm_gaussian` docstring no longer says "Cochran"; notes A S A = A is sufficient, not necessary.
- Nit: the `k < l` guard is needed for c = 0 (χ²(0) is a point mass at 0), so kept.
- Missing results logged as open: χ² = Gamma(r/2, 1/2), variance 2r, additivity, Cochran's theorem proper,
  power/noncentral χ², end-to-end GMM Wald test with V̂ = (ĜᵀŜ⁻¹Ĝ)⁻¹, t-test, nonlinear Wald, LM/distance tests.
