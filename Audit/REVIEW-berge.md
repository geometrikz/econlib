# Review record: correspondences and Berge's maximum theorem (2026-11-23)

Files: `EconLean/Foundations/Correspondence.lean`, `EconLean/Foundations/Maximum.lean`.
Frozen statements: `EconLean/Audit/Statements/Berge.lean`.

## Step 1: context-isolated adversarial review
Reviewer saw only the statements (proofs and comments stripped) and Mathlib's
hemicontinuity definitions; reference Aliprantis–Border ch. 17, Stokey–Lucas 3.6, MWG M.K.6.

| Declaration | Verdict |
|---|---|
| `upperHemicontinuousAt_iff_textbook`, `lowerHemicontinuousAt_iff_textbook`, `ContinuousCorrespondence`, `graph` | faithful (Mathlib's UHC/LHC = AB Def 17.2, incl. empty values) |
| `isClosed_of_isClosed_graph`, `isClosed_graph_of_upperHemicontinuous` (AB 17.10) | faithful |
| `UpperHemicontinuousAt.inter_of_isClosed_graph` (AB 17.25) | faithful |
| `upperHemicontinuousAt_of_isClosed_graph`, `upperHemicontinuous_of_isClosed_graph` (AB 17.11) | faithful (no Hausdorff needed) |
| `IsCompact.biUnion_of_upperHemicontinuous` (AB 17.8) | faithful |
| `isClosed_graph_iff_seq`, `UpperHemicontinuousAt.exists_tendsto_subseq` (AB 17.16/17.20) | faithful |
| `maxValue`, `argmax`, `isGreatest_maxValue`, `argmax_eq`, `argmax_nonempty`, `isCompact_argmax`, `continuous_of_argmax_eq_singleton` | faithful |
| `upperSemicontinuous_maxValue`, `lowerSemicontinuous_maxValue` | faithful with documented deviation (continuous f; compact values needed because m is a real sSup) |
| `continuous_maxValue`, `upperHemicontinuous_argmax`, `berge_maximum_theorem` | faithful with documented deviation (f continuous on X×Y as in SL/MWG; AB only needs it on the graph) |

Findings fixed: both `example`s now state and prove their premises (non-vacuity
witness checks all Berge hypotheses; the LHC-necessity counterexample proves
UHC, nonempty compact values, ¬LHC at 0, and ¬continuity of the value).
Deviations documented in the Maximum.lean header. Missing-but-in-Mathlib:
AB 17.20 converse / 17.21 are `UpperHemicontinuousAt.of_sequences`,
`LowerHemicontinuousAt.of_sequences`, `LowerHemicontinuousAt.exists_seq_tendsto`.
Open (optional): Berge with f continuous only on the graph; semicontinuous-f halves.

## Step 2: proof checks
- `#print axioms` on all 16 headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker` (ships in the v4.36.0 toolchain `bin/`): passes on both modules (run one module per call; passing two at once segfaults, a tool quirk).
- `nanoda_bin` 0.4.17 (also in toolchain `bin/`) on a `leanexport` of all headline theorems: 13,928 declarations, no typechecker errors.
- Comparator: not reachable from the cloud container; stand-in is `Audit/Statements/Berge.lean`, which restates each headline verbatim and closes it with the library theorem.
