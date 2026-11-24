# Review record: behavioral round 12 (2026-11-24)

Modules: `BoundedRationality/Robinson` (new), `BoundedRationality/PoissonCH`
(new), plus header updates in `BoundedRationality/FictitiousPlay` (pointer to
Robinson) and line wrapping in `Behavioral/VariationalPreferences`. Frozen
statements: `Audit/Statements/BehavioralXII.lean` (24 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements and module headers against
Robinson (1951), Brown (1951) and Camerer–Ho–Chong (2004). It confirmed that
`IsFPPath` is simultaneous fictitious play (row maximizes, column minimizes,
date 0 unconstrained), that `exploit` is the duality gap and nonnegative, that
`IsSystem` matches Robinson's vector systems (her proof needs only
`max U(0) ≤ min V(0)`), that `Good`/`eventually_good` have the uniform
quantifier order of her lemma, that `isFPPath_fp` constructs a genuine path,
and that `poissonFreq` and `chBelief` are CHC's objects.

Findings and resolutions:

1. MAJOR: the header claimed Robinson's own statement (max and min average
   payoffs converge to the value) but only the empirical payoff was proved.
   **Fixed:** added `tendsto_max_min_value` (with `payoff_le_max`,
   `min_le_payoff`).
2. MAJOR: "total-variation distance" for `Σ|g_k − f|`, which is the ℓ¹
   distance (twice TV). **Fixed:** renamed to ℓ¹ throughout.
3. The limit theorem did not mention `chBelief`. **Fixed:**
   `tendsto_l1_chBelief` states `∑' h, |chBelief f k h − f h| → 0`; Poisson
   corollaries split (`poisson_hasSum_l1`, `poisson_tendsto_l1`).
4. "Higher levels are more accurate" only as a limit. **Fixed:** added
   `l1_strictAnti`.
5. `eventually_isEpsSaddle` lacked membership of the frequencies in the
   simplex. **Fixed:** added.
6. "Only the set of equilibria is approached" is informal. **Documented** as
   informal.
7. Brown's alternating process not formalized. **Documented.**
8. Global bound `|A k l| ≤ a` in the vector-system lemmas. **Documented**
   (holds for finite games).
9. Junk values at `t = 0`: consistent, no change.
10. Beauty-contest CH uses the large-population approximation and level 0
    guessing 50. **Documented.**

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-24
  (7,486 jobs): success, no warnings.
- `#print axioms` on 77 declarations (53 library + 24 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 4 modules and `Audit.Statements.BehavioralXII` pass.
- `leanexport` + `nanoda` on the 24 frozen theorems: 20,102 declarations, no
  typechecker errors (usual single "Unable to print axioms" message).
- `leanblueprint pdf` and `web` build; all 746 `\lean{}` names in
  `behavioral.tex` resolve.
