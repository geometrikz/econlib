# Review record: behavioral round 10 (2026-11-23)

Modules: `BoundedRationality/FictitiousPlay`,
`BoundedRationality/StochasticStability`. Frozen statements:
`Audit/Statements/BehavioralX.lean` (17 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements and module headers against
Brown (1951), Robinson (1951), Fudenberg–Levine (1998, ch. 2),
Kandori–Mailath–Rob (1993), Young (1993) and Harsanyi–Selten (1988). It
checked that `IsFP` constrains only dates `T ≥ 1` and best-responds to the
others' frequencies only, the full `IsMixedNash` conclusion, the
risk-dominance condition and `p*`, which convention each resistance refers
to, and the stag-hunt example (safe action risk dominant, stag payoff
dominant, `p* = 1/4`).

Major issues (both fixed):

1. The KMR/Young selection theorem was named and described as stochastic
   stability although it is a two-state formula. **Fixed:** renamed
   `riskDominant_selected_twoState`; the header bullet now states the
   two-state reduction and that the full chain is not formalized.
2. The header said transition probabilities are "of order `ε^r`" while the
   formal object used exactly `ε^r`. **Fixed:** added
   `tendsto_weightA_of_bounds` and `riskDominant_selected_of_bounds`, which
   allow any transition probabilities between constant multiples of `ε^r`.

Minor issues and resolutions:

3. Fudenberg–Levine proposition number uncertain. **Fixed:** cite ch. 2
   without a number.
4. No prior weights, date `0` free; independent (product) beliefs.
   **Documented.**
5. `freq_eq_zero_of_dominated` is not about dominance. **Fixed:** renamed
   `freq_eq_zero_of_worse_at_limit`.
6. Only constant paths witness convergence. **Documented** (Robinson and
   Miyasawa convergence theorems not formalized).
7. Payoffs include self-matching; KMR's thresholds differ by `O(1/N)`.
   **Documented** (does not affect the large-`N` claims).
8. Leaving at exact ties. **Documented** (weak best reply convention).

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-23
  ~23:30 UTC (7,394 jobs): success, no warnings.
- `#print axioms` on 54 declarations (37 library + 17 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: both modules and `Audit.Statements.BehavioralX` pass.
- `leanexport` + `nanoda` on the 17 frozen theorems: 14,707 declarations, no
  typechecker errors (usual single "Unable to print axioms" message).
- `leanblueprint pdf` and `web` build; every `\lean{}` name in
  `behavioral.tex` (603) resolves.
