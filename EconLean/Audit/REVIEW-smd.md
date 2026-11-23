# Review: Sonnenschein–Mantel–Debreu, Debreu's decomposition step

Files: Bridges/Aggregation/SMD.lean, `section SMD` in Audit/Statements/Aggregation.lean, blueprint `sec:smd` in
chapters/aggregation.tex.

What is proved: any z with Walras' law on D ⊆ open simplex, with z_l(p) + c p_l > 0 (e.g. z bounded below and prices
≥ ε), equals Σ_l z^l with z^l(p) = (z_l(p) + c p_l)(e_l − (p_l/‖p‖²) p), each z^l satisfying Walras' law and WARP, and
continuous wherever z is. Witness `zBad`: violates WARP (non-convex equilibrium set) yet decomposes.

Not proved: Debreu's second step (each piece is the excess demand of a rational consumer). WARP is necessary for that,
and sufficient for L = 2, but not for L ≥ 3.

## Step 1: context-isolated adversarial review
All statements faithful. Fixes applied:
- Docstring: background paragraph marked as background; added the WARP-vs-rationalizability caveat for L ≥ 3.
- Exposed the explicit pieces (`frozen_debreu_pieces`, `frozen_debreuPiece_def`) and added continuity transfer
  (`continuousOn_debreuPiece`).
- Froze the witness (`frozen_zBad_def`, `frozen_DBad_def`, `frozen_zBad_smd`).

## Step 2
- Build warning-free; `#print axioms` standard only; leanchecker passes on Bridges.Aggregation.SMD and
  Audit.Statements.Aggregation.
