# Review: Brouwer/Kakutani (vendored) and unconditional existence

Vendored: Foundations/FixedPoint/** from vltanh/lean4-fixed-point @ 5f650f0 (Apache 2.0, The-Anh Vu-Le),
copied with geoff's approval (decision card, 2026-11-23). KKM route only; only import paths rewritten.
New: Foundations/FixedPoint.lean (Econ-facing statements), GE/ExistenceGeneral.lean, Audit/Statements/FixedPoint.lean,
blueprint chapters/fixedpoint.tex.

## Step 1: context-isolated adversarial review (statements only)

| Frozen statement | Verdict |
|---|---|
| frozen_brouwer | Faithful |
| frozen_brouwer_continuousMap | Faithful |
| frozen_kakutani (closed graph on s, nonempty convex values in s) | Faithful (closed graph with values in a compact set = uhc + closed values) |
| frozen_brouwerSimplex ([Nonempty ι] necessary) | Faithful |
| frozen_gale_nikaido_debreu' | Faithful (Debreu 1959 §5.6 version, not MWG 17.C's z = 0 version) |
| frozen_exists_freeDisposalEquilibrium' | Faithful with documented deviation: needs demand continuous on the closed simplex, so not MWG 17.C.1 / Cobb–Douglas |

No fixes required. Non-vacuity: `BrouwerSimplex (Fin 3)` and a 3-good GND instance with z(p) = -p in GE/ExistenceGeneral.lean.

## Step 2: comparator stand-in and reverifiers

- Full local build warning-free (5304 jobs); vendored files build unchanged on v4.36.0.
- `#print axioms`: propext, Classical.choice, Quot.sound only, on all frozen theorems.
- leanchecker: pass on Common.Sperner, Common.Subdivision, Brouwer.KKM, Kakutani.Simplex, Kakutani.Convex,
  Foundations.FixedPoint, GE.ExistenceGeneral, Audit.Statements.FixedPoint.
- nanoda: 30,852 declarations, no typechecker errors (one pretty-printer message "Unable to print axioms",
  which is output formatting, not a kernel failure; axioms independently confirmed by `#print axioms`).
