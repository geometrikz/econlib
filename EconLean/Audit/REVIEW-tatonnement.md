# Review: tâtonnement (Lyapunov step) and GS ⇒ p*·z(p) > 0 for two goods

Files: Bridges/Aggregation/Tatonnement.lean, additions to Bridges/Aggregation/Examples.lean (zCD_cost_pos,
zCD_tatonnement_antitone, φArc/zArc/pArc witness), `section Tatonnement` in Audit/Statements/Aggregation.lean,
blueprint section `sec:tatonnement` in chapters/aggregation.tex.

## Step 1: context-isolated adversarial review (two rounds)

Round 1 findings, all fixed:
- Paths were required on all of ℝ (with positivity for all t). For zCD this forces constant paths: running time
  backwards hits the boundary in finite time. **Fixed**: paths start at t = 0 (`HasDerivWithinAt` on `Ici 0`), all
  hypotheses and conclusions only for t ≥ 0 (`AntitoneOn`/`StrictAntiOn` on `Ici 0`).
- "Stability" overstated: only the Lyapunov step is proved. **Fixed**: docstrings and blueprint say convergence is not
  claimed.
- Only a constant-path witness. **Fixed**: nonconstant witness `pArc` (rotation on the unit circle toward (1,1)),
  `pArc_strictAnti`.

Round 2: all statements faithful; `cost_pos_two_goods` faithful with deviation (L = 2 only, named as such). Caveat
recorded in the docstring: `zArc` is not an economic excess demand (degree-1 homogeneous, not GS); it only witnesses
joint satisfiability.

## Step 2

- Full local build warning-free (5380+ jobs).
- `#print axioms`: propext, Classical.choice, Quot.sound only.
- leanchecker: pass on Tatonnement, Aggregation.Examples, Audit.Statements.Aggregation.

## Open
- Convergence (LaSalle-type) for global stability, MWG 17.H.1 in full.
- p*·z(p) > 0 under gross substitutes for L > 2 goods (Arrow–Block–Hurwicz).
- `leanblueprint pdf` could not be run here: no TeX Live in this container (apt mirror unavailable). Needs to be run
  by the integrator.
