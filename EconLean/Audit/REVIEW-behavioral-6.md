# Review record: behavioral round 6 (2026-11-23)

Modules: `Behavioral/ForwardGuidanceGE`, `Behavioral/CreditCycles`,
`Behavioral/Satisficing`, `Behavioral/ChoiceWelfare`,
`Behavioral/SmoothAmbiguity`, `Behavioral/LimitedAttention`. Frozen
statements: `Audit/Statements/BehavioralVI.lean` (41 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements against Gabaix (2020),
McKay–Nakamura–Steinsson (2016), Bordalo–Gennaioli–Shleifer (2018),
López-Salido–Stein–Zakrajšek (2017), Simon (1955) / Rubinstein (Lecture 3),
Bernheim–Rangel (2009), Klibanoff–Marinacci–Mukerji (2005) and
Masatlioglu–Nakajima–Ozbay (2012). It recomputed the backward matrix
`B = [[M, 1/σ], [κM, βM^f + κ/σ]]`, checked that `ρ(B) < 1` iff
`κ < σ(1 − M)(1 − βM^f)` (Gabaix's peg-determinacy condition), the RE bound
`1/σ + Tκ/σ²`, the credit-cycle IRFs and the WARP(LA) definition.

No major issues. Minor issues and resolutions:

1. MNO Theorem 1 only in the necessity direction. **Documented** as such
   (sufficiency left open).
2. `IsCLA` uses an injective `X → ℕ`, so vacuous on uncountable `X`.
   **Documented** (MNO assume finite `X`).
3. GE forward-guidance vanishing stated only as sufficiency. **Fixed:** added
   `fgGE_not_vanishes` (left functional `ℓ = (1, (1 − M)/(κM))` with `ℓB ≥ ℓ`),
   `fgGE_vanishes_iff`, `fgGE_vanishes_iff_determinate`.
4. RE puzzle is under the return-to-steady-state selection. **Documented.**
5. `invest_bust` had a vacuous `α ≠ 1`; bust is relative. **Fixed:** `α < 1`,
   added `invest_bust_lt`, documented as a relative reversal.
6. `expSpreadNext` hard-coded the θ-independence. **Fixed:** next period's
   spread is now built from the diagnostic rule (`fcNext`, `spreadNext`), the
   conditional expectation `condExp` drops the `ε_{t+1}` loading, and
   `condExp_spreadNext` derives θ-independence; added `cov_expected_change`.
7. `concaveOn_of_averse` is belief-free. **Documented.**
8. Mixing acts in utility presumes Anscombe–Aumann. **Documented.**
9. Names promising negations. **Fixed:** `example_violates_warp : ¬ WARP cex`;
   `satisfice_not_utility` renamed `satisfice_ne_argmax`.
10. Satisficing search order fixed to `Fin n`. **Documented** (WLOG by relabeling).

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-23
  ~19:30 UTC (7,276 jobs): success, no warnings.
- `#print axioms` on 87 theorems (46 library + 41 frozen): only `propext`,
  `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 6 modules and `Audit.Statements.BehavioralVI` pass.
- `leanexport` + `nanoda`: 17,256 declarations, no typechecker errors (usual
  single "Unable to print axioms" pretty-printer message).
- `leanblueprint pdf` and `web` build; every `\lean{}` name resolves.
