# Review record: batch 14 (Green–Laffont, intuitive criterion, Rogerson)

## Modules
New:
- `Mechanism/GreenLaffont`
- `Information/IntuitiveCriterion`
- `Contracts/FirstOrderApproach`

Header-only updates (stale "not formalized" text removed):
- `Mechanism/VCG`
- `Information/Signaling`

Frozen statements: `Audit/Statements/Batch14.lean`, 10 theorems.

## What is proved
- **Green–Laffont (unrestricted domain; MWG Prop. 23.C.5).**
  - Every efficient, strategy-proof mechanism pays Groves transfers.
  - Together with `groves_isStrategyProof`, this is a full characterization.
  - Witness: 2 agents and 2 outcomes; the hypotheses hold jointly.
- **Cho–Kreps intuitive criterion in the two-type Spence model.**
  - A separating PBE that passes the criterion is the Riley outcome.
  - Every pooling PBE fails the criterion.
  - The Riley PBE passes.
  - Witness: c = e/θ.
- **Rogerson (1985).**
  - Summation by parts.
  - CDFC plus a nondecreasing utility schedule gives expected utility that is concave in effort.
  - So the first-order condition implies the global optimum.
  - A Mirrlees–Holmström-form schedule with μ ≥ 0 and nondecreasing L is monotone, which gives the combined theorem.
  - μ ≥ 0, g = 1/u′ and L = likelihood ratio are abstract hypotheses; this is disclosed.

## Check 1: isolated adversarial review (2 rounds, proofs stripped)
- **Round 1:** 3 independent reviewers, no Major findings. Minor items fixed:
  - Green–Laffont:
    - The header now says the result has content only with an efficient rule on the whole domain (essentially finite X).
    - Added a joint witness.
    - Fixed the stale VCG header.
  - Intuitive criterion:
    - Named the omitted symmetric case.
    - Stated that each theorem uses a subset of the assumptions.
    - Stated that eR is a hypothesis.
    - Fixed the stale Signaling header.
  - Rogerson:
    - Stated that g and L are abstract stand-ins for 1/u′ and the MLRP likelihood ratio.
    - Reworded "the wage schedule solving the relaxed program".
    - Noted that p ≥ 0 is unused.
    - Added a witness for `mirrlees_monotone`.
- **Round 2:** all items resolved, no Major findings. Minor items fixed:
  - Corrected the hypotheses in the pooling docstring.
  - Noted that `hbig` is only a sufficient condition.
  - Re-attributed smoothly connected domains to Holmström (1979).
  - Noted the probability range in the witness.

## Check 2: kernel and axioms
- Full shared build is green (7890 jobs) and warning-free.
- Axioms: only propext, Classical.choice and Quot.sound, across 10 theorems plus their 10 frozen copies.
- leanchecker exits 0 on the 3 new modules, the 2 updated modules and the frozen file.
- nanoda: no typechecker errors (16,156 declarations).
- Comparator stand-in: the frozen-statements file.
- `leanblueprint pdf` builds.
- Blueprint entries:
  - mechanism.tex: `thm:green-laffont`
  - asyminfo.tex: `thm:intuitive`
  - asyminfo.tex: `thm:rogerson`
