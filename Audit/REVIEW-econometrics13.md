# Audit: econometrics batch 13 (local power, noncentral χ²)

Files: EconLean/Econometrics/Asymptotics/LocalPower.lean (new). Blueprint: chapters/econometrics10.tex (new),
`\input` after econometrics9 in content.tex.

## Machine checks (Lean 4.36.0)
- `lake build EconLean`: success, no warnings (autoImplicit=false).
- `#print axioms`: 15/15 declarations use only [propext, Classical.choice, Quot.sound].
- leanchecker on LocalPower: exit 0.
- nanoda (58,890 declarations incl. dependencies): no typechecker errors.
- `leanblueprint pdf`: success, no undefined or duplicate references.

## Adversarial statement review (context-isolated agent)
Full text: independent-econometrics13-statement_review.md. No defects. Limits and noncentrality
(‖M^{-1/2}h‖² = hᵀM⁻¹h, Davidson–MacKinnon λ) match the canon; the witness uses a genuine drift (h = 1,
noncentrality 1/2, consistent with t² = W) and a non-constant V̂.

Responses:
- Docstrings fixed: `ncChiSq` (dependence only on ‖μ‖² is classical, not formalized), header (no atoms needs a
  nonempty index), `t_local_power_mono` (statement is monotonicity in h), helper lemma (sequence need not be constant).
- Kept as documented caveats: one fixed probability space with drifting θₙ (not the P_{θₙ}/Le Cam formulation);
  √n(θ̂ₙ − θₙ) →d L under the drift is assumed, not derived from contiguity; witness only has q = 1.
- Missing results logged: ncChiSq depends only on (q, λ); mean q + λ; Wald local power ≥ size and increasing in λ;
  strict monotonicity and power → 1 as h → ∞; two-sided monotonicity in |h|; primitive conditions (e.g. OLS).
