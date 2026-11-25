# Audit: econometrics batch 12 (t² = W, one-sided t-test)

Files: EconLean/Econometrics/Asymptotics/OneSidedT.lean (new). Blueprint: new section
"The t-test as a Wald test, and one-sided tests" appended to chapters/econometrics9.tex.

## Machine checks (Lean 4.36.0)
- `lake build EconLean`: success, no warnings (autoImplicit=false).
- `#print axioms`: 12/12 declarations use only [propext, Classical.choice, Quot.sound].
- leanchecker on OneSidedT: exit 0.
- nanoda (58,767 declarations incl. dependencies): no typechecker errors.
- `leanblueprint pdf`: success, no undefined references (only pre-existing duplicate labels def:bgg/thm:bgg
  from another chapter).

## Adversarial statement review (context-isolated agent)
Full text: independent-econometrics12-statement_review.md. No defects; the witness instantiates every hypothesis and
t² = W holds there with rᵀV̂r > 0 (not a 0 = 0 artefact).

Responses:
- Docstrings for `t_one_sided_wrong_side` and the module header reworded: `rᵀθ₀ < c` is an interior point of the
  composite null `rᵀθ ≤ c` (or a wrong-side alternative to `rᵀθ = c`); size over the composite null is pointwise.
- Degenerate `rᵀV̂r = 0` case of t² = W is 0 = 0 by convention (documented).
- Missing results logged: uniform size over a composite null, local power, named critical value z₁₋α,
  random V̂ in witnesses.
