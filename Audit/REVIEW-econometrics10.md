# Audit: econometrics batch 10 (overidentified data-level witnesses)

Files: EconLean/Econometrics/Asymptotics/FeasibleJWitness.lean (new, namespace Econ.Asymptotics.FeasibleJ);
GMMWald.lean (`two_step_wald_rect_witness` added). Blueprint: econometrics8.tex, section sec:chi-squared-witnesses.

## Machine checks (Lean 4.36.0)
- `lake build`: success, no warnings (autoImplicit=false).
- `#print axioms`: 35/35 declarations use only [propext, Classical.choice, Quot.sound].
- leanchecker on FeasibleJWitness and GMMWald: exit 0.
- nanoda (60,095 declarations incl. dependencies): no typechecker errors.
- `leanblueprint pdf`: success, no undefined references.

## Adversarial statement review (context-isolated agent)
Full text: independent-econometrics10-statement_review.md. No false or vacuous statements; all helper lemmas
checked by hand; the n ≥ 4 conditions are necessary. The feasible-J design is linear, overidentified (l = 2 > k = 1),
with a random first step and genuinely estimated Ŝ(θ̃); J_n → ω₁² ∼ χ²(1).

Responses:
1. Trivially-true hypotheses not listed as conjuncts — documented in both docstrings (discharged in proofs).
2./3. Spike device and triangular-array deterministic design — documented as caveats in the module docstring
   (same device as the existing `two_step_feasible_witness`). An i.i.d. sampling witness (needs an LLN/CLT
   instantiation) remains OPEN.
4./5. Minimal overidentification (zero first-stage strength of the second instrument; S = W₁ = I) and light
   use of estimated inputs in the rect Wald witness — OPEN, optional strengthening.
