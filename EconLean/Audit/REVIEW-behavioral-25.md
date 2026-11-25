# Review: behavioral round 25 (RDUConcaveConvex)

Date: 2026-11-25. Files: `Behavioral/RDUConcaveConvex.lean`, frozen `Audit/Statements/BehavioralXXV.lean`.

## Adversarial statement review (context-isolated agent)
Checked against Chew–Karni–Safra (1987), Rothschild–Stiglitz (1970), increasing concave order, Tomić–Weyl.
- No MAJOR findings. `fuchs_mono` is true with arbitrary-sign weights (slopes ≥ 0 remove the zero-total
  condition). `SSD x q p` is p ≥_icv q on weakly increasing grids, direction correct. `cks_ssd`/`cks_mps` true.
- Reviewer showed monotone w is genuinely needed even in the MPS version once U is nonlinear
  (w = 2t² − t, U = −e^{−v}, numerical counterexample); `hUm` needed since rdu ranks by grid index.
- MINOR (fixed): header now says IsMPS unfolds to equal means ∧ SSD; notes weakly increasing grids;
  notes `hwm` is a standing CKS assumption that cannot be dropped for nonlinear U.
- MINOR (fixed): stronger non-vacuity witness added, `sq_tri_strict` (equal means, RDU 1/4 vs 1/2).
- Scope: only CKS sufficiency; necessity only for linear U (`yaari_strongRiskAverse_iff`).

## Mechanical checks
- Full `lake build EconLean` on the shared tree: success (7942 jobs), no warnings in new files.
- `#print axioms` (12 library + 12 frozen): only propext, Classical.choice, Quot.sound.
- `leanchecker` on both modules: exit 0.
- `leanexport` + nanoda: 18323 declarations, no typechecker errors.
- Blueprint: thm:beh-cks after thm:beh-rdu-strong; pdf and web build; no new undefined refs.

## Note
Round 24's handoff had appended its two imports after `@[expose] public section` in the shared
EconLean.lean; fixed in place (imports moved above that line) on 2026-11-25.
