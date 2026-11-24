# Review record: the Rubinstein alternating-offers game (batch 10)

Module: `Bargaining/RubinsteinGame`, which also updates the header of `Bargaining/Rubinstein`. Frozen statements: six theorems appended to `Audit/Statements/MatchingBargaining.lean`.

## What is proved
- **The game.** The alternating-offers game is defined on histories of rejected offers, with pure strategies and discounting measured from each node.
- **SPE definition.** Subgame perfection requires no profitable unilateral deviation at every proposal node and at every response node (after any feasible offer).
- **Existence.** `stationary_isBargSPE`: the stationary profile is an SPE.
- **Shaked–Sutton.** `spePay_eq`: the Shaked–Sutton inequalities are derived from the game itself. Every SPE gives each proposer her Rubinstein share after every history.
- **Uniqueness.** `bargSPE_eq_stationary`: every pure-strategy SPE equals the stationary profile at every history.
- **Outcome.** `bargSPE_unique`: immediate agreement on x*.

## Check 1: isolated adversarial review (2 rounds, proofs stripped)
**Round 1.** The model, payoffs and SPE definition were judged correct: neither too weak nor too strong, and not vacuous. Findings and fixes:
- **Major:** the header claimed "the unique SPE", but only the root outcome had been proved. Fixed by adding `bargSPE_eq_stationary`, which proves strategy-level uniqueness at every history.
- **Minor:** fixed as follows:
  - the docstrings now disclose that strategies are pure;
  - the citation is now O–R *Course* §7.2–7.3, Prop. 122.1, specialized to exponential discounting;
  - added a note on δ = 0;
  - corrected the stale "not formalized" sentence in Rubinstein.lean;
  - pointed to the stationary payoff lemmas.

**Round 2.** All items resolved. The remaining minor point (the mixed-strategy remark) was reworded to: "extension to behavioral strategies not formalized".

## Check 2: kernel and axioms
- **Full shared build:** green, 7764 jobs.
- **Axioms:** checked on 6 theorems plus 6 frozen copies. Only propext, Classical.choice and Quot.sound appear.
- **leanchecker:** exit 0 on RubinsteinGame, Rubinstein and MatchingBargaining.
- **nanoda:** no errors.

## Blueprint
`cooperative.tex` gains `sec:rubinstein-game` (`def:barg-game`, `thm:rubinstein-game`). The PDF builds.
