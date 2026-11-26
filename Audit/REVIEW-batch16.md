# Review record: batch 16 (rural hospitals, Nash folk theorem with minmax punishments)

Modules: `Matching/RuralHospitals`, `Games/MinmaxFolk`. Frozen statements:
`EconLean/Audit/Statements/Batch16.lean`.

## Step 1: context-isolated adversarial review (proofs stripped)

Round 1: no Critical or Major findings. The following Minor points were fixed:
- The headline of `nash_folk_pureMinmax` overclaimed slightly. It now reads "Nash folk theorem for pure stationary target profiles", and its docstring says it is the pure-minmax special case of Fudenberg–Tirole Thm. 5.1. The mixed minmax is weakly lower, so FT covers more payoffs.
- The proof stripper corrupted a header line that began with the word "theorem". The line has been reflowed.
- The rural hospitals header now says the content is about the longer side: the shorter side is always fully matched when everybody is acceptable.

Round 2 (fresh reviewer, after the fixes): no Critical or Major findings. The following Minor points were fixed:
- Attribution: the women-pessimal result is the corollary of Roth–Sotomayor Thm. 2.13, not the theorem itself.
- The citation of Mailath–Samuelson Prop. 2.5.1 was dropped, because its number and content could not be confirmed.
- The `IsRepeatedNash` docstring now carries the bounded-payoffs caveat about `tsum`.
- The `min(|M|,|W|)` remark is marked as not a theorem.
- The `rural_hospitals` docstring now states its scope: one-to-one matching, everybody acceptable.

Both reviewers confirmed the following:
- `firstDev` picks the earliest deviation.
- `minmaxTrigger` identifies the unique deviator.
- `pureMinmax` is min over b₋ᵢ of max over sᵢ.
- `IsRepeatedNash`, which checks deviations from the empty history only, is the right notion.
- Dropping `huw` from `daMatching_womenPessimal` makes the statement stronger, not vacuous.

Witnesses:
- Matching: two men and one woman. Man 1 is single in every stable matching.
- Repeated game: in the prisoners' dilemma, the minmax trigger supporting cooperation is a Nash equilibrium at δ = 1/2.

## Step 2: mechanical checks

- Full build of the shared tree: 8018 jobs, green and warning-free.
- `#print axioms`: every headline theorem and frozen statement uses only `propext`, `Classical.choice` and `Quot.sound`.
- leanchecker: RuralHospitals, MinmaxFolk and Audit.Statements.Batch16 all exit 0.
- nanoda: no typechecker errors (15,739 declarations). It also reports one cosmetic pretty-printer message ("Unable to print axioms").
- `leanblueprint pdf` builds (entries in matching.tex and games.tex).
