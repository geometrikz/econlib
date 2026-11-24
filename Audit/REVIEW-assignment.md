# Review record: the Shapley–Shubik assignment game (batch 9)

Module: `Cooperative/Assignment`. Frozen statements: `Audit/Statements/Assignment.lean` (6 headline theorems).

## Check 1: context-isolated adversarial review (proofs stripped)

No major issues. The reviewer confirmed:
- the characteristic function is right (best internal matching; negative-surplus pairs are left out);
- the core characterization is right;
- balancedness and nonemptiness are correctly stated and not vacuous.

Minor items, all fixed:
- **Overclaim:** "core = optimal dual solutions" needed strong duality. Added `assignment_weak_duality` and `assignment_strong_duality`, and the docstrings now say how the pieces combine.
- **Unneeded hypothesis:** `[Nonempty (B ⊕ S)]` is dropped from `assignment_core_nonempty` and `shapley_shubik`. The case with no players is handled directly.
- **Citation:** the vague Osborne–Rubinstein citation is removed.
- **Not-formalized list:** expanded to the core lattice and optimal points, competitive prices, complementary slackness, stand-alone LP integrality, and the Demange–Gale–Sotomayor auction.

Integration fix: `IsMatching` was renamed `IsPairMatching` because of a clash with `Matching/GaleShapley`.

## Check 2: kernel and axioms
- **Full shared build:** green (7762 jobs) with no warnings.
- **Axioms:** checked on the 6 theorems and their frozen copies. Only propext, Classical.choice and Quot.sound appear.
- **leanchecker:** exit 0 on both modules.
- **nanoda:** no typechecker errors.

## Blueprint
`cooperative.tex` gets sec:assignment-game (def:assignment-game, thm:assignment-core), and the PDF builds.
