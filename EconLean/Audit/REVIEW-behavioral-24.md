# Review: behavioral round 24 (RDUStrongRiskAversion)

Date: 2026-11-25. Files: `Behavioral/RDUStrongRiskAversion.lean`, frozen `Audit/Statements/BehavioralXXIV.lean`.

## Adversarial statement review (context-isolated agent)
Checked against Fuchs (1947), Rothschild–Stiglitz (1970), Yaari (1987), Chew–Karni–Safra (1987).
- No MAJOR findings. `fuchs` with arbitrary-sign weights is correct (Fuchs allows it); `IsMPS` matches the
  RS integral condition for weakly increasing grids; convex-w convention matches Yaari's decumulative weighting;
  converse yields full (not just midpoint) convexity since the grid's middle point is chosen per λ.
- MINOR (fixed): header now says `IsMPS` is an MPS only for weakly increasing grids and an algebraic
  condition otherwise; "increasing" → "weakly increasing" in header and docstring.
- MINOR (resolved): stripped `isMPS_tri` was truncated at `let`; the real statement is
  `IsMPS (0,l,1) (triLot r r) (triLot t s)` with r = l t + (1−l) s, as the reviewer asked; frozen file states it in full.

## Mechanical checks
- Full `lake build EconLean` on the shared tree: success (7938 jobs), no warnings in new files.
- `#print axioms` (10 library + 10 frozen): only propext, Classical.choice, Quot.sound.
- `leanchecker` on both modules: exit 0.
- `leanexport` + nanoda: 13823 declarations, no typechecker errors.
- Blueprint: thm:beh-rdu-strong added after thm:beh-rdu-risk; pdf and web build; no new undefined refs.
