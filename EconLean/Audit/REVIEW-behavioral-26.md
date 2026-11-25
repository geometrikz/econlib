# Review: behavioral round 26 (RISymmetric)

Date: 2026-11-25. Files: `Behavioral/RISymmetric.lean` (new), header-only edits to
`Behavioral/RationalInattention.lean` and `Behavioral/Logit.lean`; frozen `Audit/Statements/BehavioralXXVI.lean`.
Addresses independent review O's flag: uniform marginals are now derived from a symmetric problem.

## Adversarial statement review (context-isolated agent)
Checked against Matějka–McKay (2015) Lemma 2 and the a-priori-symmetric-options result; Caplin–Dean.
- No MAJOR findings. `valueF` is MM's objective in unconditional probabilities; the bounds
  `riObjective_le_valueF`, `valueF_le_riObjective_gl` (P may have zeros) and `isOptimalRule_gl_of_isMax`
  are true and correctly quantified. `softmax_optimal_of_symmetric` is true; it generalizes MM's fully
  symmetric case to any transitive symmetry set; conclusion is "an optimal rule" (uniqueness can fail).
- MINOR (fixed): `hmul` redundant → added `isSymmetry_mul` and `softmax_optimal_of_transitive`
  (only transitivity by symmetries assumed).
- MINOR (fixed): "F is concave" reworded to equal-weight Jensen; header notation π → ρ; citation of
  the symmetric result corrected; scope says Caplin–Dean support conditions are not formalized.
- MINOR (fixed): stale "left for a follow-up" in Logit.lean header now points to RationalInattention/RISymmetric.

## Mechanical checks
- Full `lake build EconLean` on the shared tree: success (7946 jobs), no warnings.
- `#print axioms` (13 library + 13 frozen): only propext, Classical.choice, Quot.sound.
- `leanchecker` on RISymmetric, RationalInattention, Logit, BehavioralXXVI: exit 0.
- `leanexport` + nanoda: 17269 declarations, no typechecker errors.
- Blueprint: thm:beh-ri-sym before "Ambiguity"; pdf and web build; no new undefined refs.
