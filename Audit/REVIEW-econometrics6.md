# Review: econometrics batch 6

Files: `EconLean/Econometrics/Causal/PropensityScore.lean`, `TimeSeries/YuleWalker.lean`,
`Asymptotics/TwoStepGMM.lean`. Blueprint: `chapters/econometrics6.tex`.

## Step 1: context-isolated adversarial statement review

A fresh agent saw only the proof-stripped statements (`verify/strip_proofs.py`) and checked them against
Rosenbaum–Rubin (1983), Imbens–Rubin §12.3, Hamilton §3.4, Brockwell–Davis, Hansen (1982), Hayashi §3.5 and
Newey–McFadden §5. Full table: `Audit/independent-econometrics6-statement_review.md`.

Verdict: no false or contradictory statement. `cell`, `stratum`, `armProb`, `propensity`, `MeanUnconfounded`, `gram`,
`gmmA`, `jStat`, `jForm` match the textbook objects. Findings and handling:

| # | Finding | Action |
|---|---------|--------|
| D1 | J limit: mean l − k stated, χ²(l − k) law not | Documented (Mathlib has no χ² distribution); open |
| D2 | "Two-step" oversells: first step and construction of Ŝ not modelled | Docstrings reworded to "efficient GMM with a consistently estimated weight" (Hayashi Prop. 3.5); scope note added |
| C1 | Witness used S = I, so efficient weight equals identity | Witness now uses heteroskedastic S = diag(1, 2) |
| C2 | `hgm`, `Measurable L` partly redundant with `hg` | Kept (harmless, matches the reused GMM theorems) |
| C3 | Overlap not carried to e(X) | Added `overlap_coarsen` |
| C4 | Only "if" direction of RR Thm 2 | Documented in module docstring and blueprint |
| C5 | Uncentred moments; zero mean not assumed | Documented (identities hold either way) |
| C6 | `IsAR (p := p)` is AR(p+1) | Documented |
| C7 | Γ invertibility assumed, not derived from σ² > 0 | Open |
| C8 | Yule–Walker witnesses only degenerate on finite Ω | Documented; added `ar1_stationary_bound` (σ² > 0 ⇒ |φ| < 1) |

## Step 2: proof reverifiers

- `#print axioms` on all 33 declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- `lake env leanchecker` on the 3 modules: pass.
- nanoda on the export closure: 58,818 declarations, no typechecker errors.
- Full `lake build`: warning-free (also checked with `autoImplicit=false`). `leanblueprint pdf`: builds once an
  unrelated `$` typo in `chapters/asyminfo.tex:339` is fixed (not in this batch's files).

Comparator (`verify/check.sh`) runs at integration after `make_challenge.py`.
