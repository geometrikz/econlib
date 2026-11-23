# Review record: behavioral round 11 (2026-11-23)

Modules: `BoundedRationality/KMRChain` (new), `BoundedRationality/BayesianLearning`
(new), `Behavioral/VariationalPreferences` (new), plus a header pointer in
`BoundedRationality/StochasticStability`. Frozen statements:
`Audit/Statements/BehavioralXI.lean` (25 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements and module headers against
Kandori–Mailath–Rob (1993), Binmore–Samuelson–Vaughan (1995), Sandholm (2010),
Wald/Doob (1949), Blackwell–Dubins (1962), Kalai–Lehrer (1993, 1994) and
Maccheroni–Marinacci–Rustichini (2006). It confirmed the birth–death kernel,
`IsStationaryDist` (values beyond `N` unused), the revision probabilities, the
quantifiers of `kmr_selects_riskDominant` and the exponent count (`2m < N`),
the `IsIID` definition, the one-step forecast, the KL order, and that
`le_dot_add_cost` + `exists_eq_dot_add_cost` give `I(f) = min_p (⟨p,f⟩ + c(p))`.

No major issues. Minor issues and resolutions:

1. Stripped `isIID_coord`/`coord_posterior_consistent` statements were cut at a
   `haveI :=` in the type (stripper artifact). **Checked**: the originals state
   `IsIID` for the coordinate process under `infinitePi (pmfMeasure (q θs))`
   and a.e. consistency under that measure; the full statements are in the source.
2. Payoffs include the reviser; this is the one-revision chain, not KMR's.
   **Documented** in the header and blueprint.
3. `posterior_consistent` hypotheses are sufficient, not minimal. **Documented.**
4. Berk (1966) is the misspecified case. **Fixed:** cite Wald (1949)/Doob; Berk as cf.
5. "Finite Blackwell–Dubins" overclaimed. **Fixed:** renamed to weak merging
   (Kalai–Lehrer 1994), noting identification is assumed.
6. `IsNiveloid` included normalization and concavity. **Fixed:** renamed
   `IsVariationalFunctional`.
7. `I` on all of `ℝ^S` (unbounded utility). **Documented.**
8. Convexity of `c` and "domain ⊆ Δ" were missing. **Fixed:** added
   `isProb_of_inDom`, `cost_convex_combo`, `convex_inDom`, `cost_convex`
   (lower semicontinuity and uniqueness documented as not formalized).
9. Only an expected-utility witness. **Fixed:** added `expected_inDom_iff`
   (the index is `+∞` off the prior, so the domain is proper).
10. Birth–death existence/uniqueness do not assume `up + down ≤ 1`.
    **Documented** (algebraic statements; `P_nonneg` gives stochasticity).
11. In the stag hunt, `A` is the safe (hare) action. **Documented.**
12. Ties to `A` is a modelling choice. Already documented.

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-23
  (7,454 jobs): success, no warnings.
- `#print axioms` on 80 declarations (55 library + 25 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 4 modules and `Audit.Statements.BehavioralXI` pass.
- `leanexport` + `nanoda` on the 25 frozen theorems: 36,829 declarations, no
  typechecker errors (usual single "Unable to print axioms" pretty-printer
  message).
- `leanblueprint pdf` and `web` build; every `\lean{}` name in
  `behavioral.tex` resolves (677).
