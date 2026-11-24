# Review record: housing market (TTC), matching with contracts, Rubinstein bargaining (batch 7)

Modules: `Matching/HousingMarket`, `Matching/Contracts`, `Bargaining/Rubinstein`.
Frozen statements: `Audit/Statements/MatchingBargaining.lean` (14 headline theorems, each closed by
the library theorem with named arguments).

## Check 1: context-isolated adversarial statement review (2 rounds, proofs stripped)

The reviewer confirmed that `IsTTC` characterizes exactly the TTC outcome under strict
preferences. It also confirmed that the strict core / weak blocking, `IsStableAlloc`,
the fixed-point theorem and the Binmore–Rubinstein–Wolinsky limit are faithful.

Round 1 findings, all fixed:
- **HousingMarket citation:** uniqueness of the strict core is now credited to Roth–Postlewaite. Shapley–Scarf's weak core with indifferences is noted as not formalized.
- **HousingMarket witnesses:** the 2-agent witness now exercises `IsTTC` and `strictCore_eq_ttc`. A new 3-agent two-stage witness was added.
- **Contracts framing:** reframed as the abstract two-sided version (Fleiner 2003, Hatfield–Kominers 2017) and the unverified theorem numbers were dropped. Other changes:
  - finiteness and algorithm caveat added;
  - the converse direction and doctor-optimality listed as not formalized;
  - `ChoiceFn.top` docstring fixed, and the witness described as simple.
- **Rubinstein overclaims:**
  - the header states that the game and SPE are not formalized;
  - `shaked_sutton` was renamed to `shaked_sutton_bounds`;
  - the asymmetric-Nash identification is marked as not formalized;
  - a note was added that the limit does not depend on who proposes first;
  - the dropped `0 ≤ δ₂` hypotheses are documented.
- **Reported "major" syntax error:** this was an artifact of `verify/strip_proofs.py`, which in one run detached a docstring from `choiceFn_top_spec`. The source compiles, and the next run stripped it correctly.

Round 2: all remaining docstring items were fixed as listed above.

## Check 2: kernel and axioms
- Full shared build: green (7520 jobs), warning-free.
- `#print axioms`: run on the 15 library theorems and 14 frozen copies. Only propext, Classical.choice and Quot.sound appear.
- leanchecker: exit 0 on all 4 modules.
- nanoda: 19595 declarations, no typechecker errors.

## Blueprint
New sections:
- `matching.tex`: sec:housing-market, sec:contracts.
- `cooperative.tex`: sec:rubinstein.

The PDF builds (159 pages) with no errors.

## Batch 8 addition: TTC strategy-proofness and efficiency (2026-11-24)

New in `Matching/HousingMarket`: `strictCore_agree_below`, `ttc_strategyproof` (Roth 1982) and `ttc_pareto`. Frozen copies are appended to `Audit/Statements/MatchingBargaining.lean`.

**Isolated review:** no major issues. The reviewer confirmed that the dominant-strategy statement is exact:
- arbitrary reports by others;
- any strict misreport;
- the comparison is made under the true utility.

Minor fixes applied:
- `hu'` is weakened to strictness of `u' i` only.
- Roth (1982) is added to the references.
- Abdulkadiroğlu–Sönmez is dropped.
- The efficiency citation is attributed.
- The header now lists all theorems that assume strictness.

**Check 2:**
- The full build is green.
- Axioms are the standard trio only.
- leanchecker exits 0 on both modules.
- nanoda found no errors.

**Blueprint:** `thm:ttc-strategyproof` was added to matching.tex. The PDF builds (160 pages).
