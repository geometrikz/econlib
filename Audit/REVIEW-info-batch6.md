# Review record: informativeness, Bayes correlated equilibrium, property rights, Boston (batch 6)

Modules: `Information/Informativeness`, `Information/BayesCorrelated`, `Information/PropertyRights`,
`Matching/Boston`. Frozen statements: `Audit/Statements/InfoBatch6.lean` (11 headline theorems,
each closed by the library theorem with named arguments).

## Check 1: context-isolated adversarial statement review (2 rounds, proofs stripped)

Round 1 findings, all fixed:
- PropertyRights: `owner_optimal` was a tautology; replaced by `more_ownership_raises_surplus`
  (Hart 1995 Ch. 2: the party whose investment matters should own the assets).
- PropertyRights: the witness violated the hypotheses (monotonicity on all of R with log);
  hypotheses now `MonotoneOn ... (Set.Ici 0)`, matching the domain of investment.
- BayesCorrelated: the converse (BCE to BNE of an expansion) required a full-support prior;
  now only ψ ≥ 0, π ≥ 0, via `obedientExpansion` that handles null states.
- Informativeness: added that the conditional-expectation contract stays in the domain U.
- Boston: "strictly prefers" and "higher priority" now stated (`idxOf` comparisons), not left
  implicit in raw lists.

Round 2: all four RESOLVED. Minor items then fixed:
- Dropped redundant hypothesis `hspec` from `more_ownership_raises_surplus` (derived from
  `hspec'` + `hmore`).
- Added a witness meeting every hypothesis of `more_ownership_raises_surplus` jointly
  (V = 2 log(1+i), v = 0, v' = log(1+i); x = 0, x' = 1/2 unique, y = 1 unique).
- Citation softened to "Hart 1995, Ch. 2"; witness docstring says it does not prove uniqueness.

Not formalized (stated in docstrings): the converse half of Holmström's principle; the
mixed-strategy reduction in Bergemann–Morris.

## Check 2: kernel and axioms
- Full shared build green (7474 jobs), warning-free.
- `#print axioms` on all 11 headline theorems, `obedientExpansion` and the 11 frozen copies:
  only propext, Classical.choice, Quot.sound.
- leanchecker: exit 0 on all 5 modules.
- nanoda: 10236 declarations, no typechecker errors (the usual harmless pretty-printer note).

## Blueprint
Sections appended: asyminfo.tex (sec:informativeness, sec:bce, sec:property-rights),
matching.tex (sec:boston). `leanblueprint pdf` builds (153 pages), no errors, all \lean names exist.
