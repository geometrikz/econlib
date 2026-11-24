# Audit: econometrics batch 9 (Wald test after efficient GMM, χ² additivity)

Files: EconLean/Econometrics/Asymptotics/GMMWald.lean (new); ChiSquared.lean (`chiSq_add` added).
Blueprint: chapters/econometrics8.tex (new section sec:gmm-wald, chiSq_add in lem:chi-squared-props).

## Machine checks (Lean 4.36.0)
- `lake build`: success, no warnings (autoImplicit=false).
- `#print axioms`: 7/7 new declarations use only [propext, Classical.choice, Quot.sound].
- leanchecker on ChiSquared and GMMWald: exit 0.
- nanoda (59,858 declarations incl. dependencies): no typechecker errors.
- `leanblueprint pdf`: success, no undefined references from these chapters.

## Adversarial statement review (context-isolated agent)
Full text: independent-econometrics9-statement_review.md. No defects; avarHat is (ĜᵀŜ⁻¹Ĝ)⁻¹ (Hayashi 3.5.13);
the Ĝθ₀ + ĝ parametrisation of linear GMM is legitimate; injectivity of Rᵀ is exactly full row rank.

Responses:
- `two_step_wald` now states the explicit limit (RAL)ᵀ(RVRᵀ)⁻¹(RAL) instead of ∃ Z; docstring says Ŝₙ is any
  consistent estimate (FirstStepGMM builds one).
- Witness caveats — OPEN: `two_step_wald_witness` states only the conclusion (it is derived from `two_step_wald`
  using the hypotheses bundled in `two_step_witness`), and R = 1 with k = 1 is square; a k = 2, l = 3,
  R = (1, −1) example is planned together with the overidentified feasible-J data witness.
- The `0 < card q` guard is needed for a = 0 when q = 0 (χ²(0) is a point mass at 0): kept.
- Missing results logged: power under fixed/local alternatives, distance-metric and C tests, joint W/J limit,
  stand-alone consistency of avarHat.
