# Review: Cobb–Douglas existence for all exponents; max-ratio tâtonnement

Modules: `EconLean/GE/CobbDouglas.lean`, `EconLean/Bridges/Aggregation/TatonnementSup.lean`.
Context-isolated adversarial review, 2026-11-24.

**Verdict: faithful with caveats; no blocking issues.**

- rpow on negative bases is irrelevant: demand only looks at `x ≥ 0`; `cont` holds globally for α > 0.
- The Arrow–Hurwicz max-ratio result is stated faithfully (GS, degree-0 homogeneity, `p* ≫ 0`, no Walras' law needed).
- `antitoneOn_sup'_of_hasDerivWithinAt` is the standard Danskin-type envelope monotonicity; non-vacuous.

Findings and resolution:
1. Module doc claimed a strict static step that was unproved. Fixed: added `GrossSubstitutes.excess_neg_of_max_ratio`.
2. "Lyapunov stability" overstated (box invariance is proved; ε–δ stability is not stated). Fixed: wording.
3. "Right derivatives" imprecise. Fixed: "within [0, ∞), one-sided at 0".
4. Path positivity assumed; unit adjustment speeds. Documented in module header.
5. `zEx` breaks Walras' law (`p·z ≤ 0`). Disclosed in docstring, including that it is not from an economy.
   A Walras-compliant witness would need Picard–Lindelöf; left open.
6. `cd2Economy` only re-applies the general theorem; explicit hand-computed equilibrium left open.
7–8. No change needed.

Proof checks: `#print axioms` standard; `leanchecker` exit 0 on both modules; nanoda checked 30578 and 20248
declarations with no typechecker errors. Frozen: `Audit/Statements/FixedPoint.lean` (section CobbDouglas) and
`Audit/Statements/Aggregation.lean` (section TatonnementSup).

## Addendum: Cobb–Douglas demand formula (second review, 2026-11-24)

`cdDemand`, `demand_cobbDouglas`, `cd2Economy_equilibrium`. Verdict: correct and faithful; the reviewer
re-derived the equilibrium (1, 8/9), (1/3, 3/4), (2/3, 1/4) by hand. Notes applied: docstring explains the
unnormalized exponents vs MWG 3.D.1, and states uniqueness up to scaling (not formalized). Optional
generalizations (w = 0, weaker hypotheses for `cost_cdDemand`) left. This resolves finding 6 above.
Checks: axioms standard, leanchecker 0, nanoda 30601 declarations clean. Frozen: FixedPoint.lean section CobbDouglas.
