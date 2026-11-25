# Review: behavioral round 27 (RDUNecessity)

Date: 2026-11-25. Files: `Behavioral/RDUNecessity.lean` (new), header-only edits to
`Behavioral/RDUConcaveConvex.lean` and `Behavioral/RDUStrongRiskAversion.lean`; frozen `Audit/Statements/BehavioralXXVII.lean`.

## Adversarial statement review (context-isolated agent)
Checked against Chew–Karni–Safra (1987).
- No MAJOR findings. Both necessity theorems are true as stated (local limit arguments; no monotonicity of
  U needed). `baseLot`/`spreadLot` G-values and `isMPS_spread` verified by hand. `cks_iff` hypotheses fit
  (monotonicity for sufficiency, one regular point each for necessity); non-vacuous (w = t², U = id).
- MINOR (fixed): docstring/header note that `StronglyRiskAverse` is RDU proper only for increasing U.
- MINOR (fixed): stale scope lines in RDUConcaveConvex and RDUStrongRiskAversion now point to `cks_iff`.
- MINOR (fixed): wording "differentiable with positive derivative at some point"; convention note
  (CKS's g concave on the cumulative ⇔ w convex on the decumulative, w(t) = 1 − g(1 − t)); regularity
  conditions described as ours, not CKS's.
- Not adopted (optional generality): replacing U's derivative point by "U nonconstant"; right derivative at s = 0.

## Mechanical checks
- Full `lake build EconLean` on the shared tree: success (7950 jobs), no warnings.
- `#print axioms` (12 library + 12 frozen): only propext, Classical.choice, Quot.sound.
- `leanchecker` on RDUNecessity, RDUConcaveConvex, RDUStrongRiskAversion, BehavioralXXVII: exit 0.
- `leanexport` + nanoda: 19713 declarations, no typechecker errors.
- Frozen file: two closers use explicit arguments (`concave_of_…`, `cks_iff`) since `@f ..` cannot infer the
  regular points; statements are verbatim.
- Blueprint: thm:beh-cks-iff after thm:beh-cks; pdf and web build; no new undefined refs.
