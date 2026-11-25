# Audit: econometrics batch 11 (test consistency, t-test)

Files: EconLean/Econometrics/Asymptotics/TestPower.lean (new). Blueprint: chapters/econometrics9.tex (new),
`\input` after econometrics8 in content.tex.

## Machine checks (Lean 4.36.0)
- `lake build`: success, no warnings (autoImplicit=false).
- `#print axioms`: 15/15 declarations use only [propext, Classical.choice, Quot.sound].
- leanchecker on TestPower: exit 0.
- nanoda (58,742 declarations incl. dependencies): no typechecker errors.
- `leanblueprint pdf`: success, no undefined references.

## Adversarial statement review (context-isolated agent)
Full text: independent-econometrics11-statement_review.md. No defects: tStat is the standard t statistic,
consistency results use the right notion under minimal assumptions, hVpsd/hVm genuinely needed.

Responses:
- Witness now also lists the null-case hypotheses of `t_normal` (convergence of √n(θ̂−0), Measurable L, law N(0,I),
  V ⪰ 0, measurability of V̂). V̂ remains deterministic (caveat kept).
- Edge-case conventions (sqrt of negatives, 0⁻¹ = 0, n = 0, singular RV̂Rᵀ) documented in the module docstring.
- Nit kept: `wald_consistent` assumes RVRᵀ positive definite (V ⪰ 0 with RVRᵀ invertible would suffice).
- Missing results logged: t² = W for one restriction, local (Pitman) alternatives and noncentral χ², one-sided t-test.
