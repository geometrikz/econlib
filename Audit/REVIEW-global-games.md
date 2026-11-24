# Review record: global games (batch 11)

Module: `Information/GlobalGames`. Frozen statements: `Audit/Statements/GlobalGames.lean` (5 theorems).

## What is proved
- **Model.** Two-player investment game (invest pays θ − 1, plus 1 if the other invests; not investing pays 0)
  with a diffuse prior, so E[θ | x] = x, and beliefs μ_x about the other's signal with
  μ_x((−∞, t]) = G((t − x)/ε), G nondecreasing, G(0) = 1/2 (`GlobalBeliefs`).
- **Iterated dominance.** `survives μ n`: strategies (measurable sets of signals at which to invest) whose action at
  every signal is a best reply to some round-(n−1) survivor.
- `threshold_survives`: the Laplacian threshold strategy "invest iff x > 1/2" survives every round.
- `globalGame_invest` / `globalGame_noInvest`: each signal x ≠ 1/2 is decided after finitely many rounds.
- `globalGame_unique`: every strategy surviving all rounds invests above 1/2 and not below, for every ε > 0
  (Morris–Shin 2003, §2; Carlsson–van Damme 1993 credited as the origin).
- `uniformNoise_spec`: non-vacuity witness, beliefs uniform on [x − 1, x + 1] (from anti-correlated noise), ε = 1.

## Check 1: isolated adversarial review (2 rounds, proofs stripped)
- **Round 1:** no Major issues. Minor issues fixed:
  - Citation re-attributed to Morris–Shin 2003 §2, with Carlsson–van Damme credited as the origin.
  - Added the wording "for every ε > 0 (diffuse prior)".
  - Added a not-formalized list: posterior derivation, common-prior consistency, proper priors and the limit,
    general payoffs, many players.
  - Added a note on the redundant fields.
  - Added the note that the witness comes from anti-correlated noise.
  - Added the E[θ|x] docstring for `investGain`.
- **Round 2:** all six items confirmed fixed, no Major issues. Three Minor issues, all fixed:
  - The redundancy note is corrected: `0 ≤ G` is needed.
  - Added a note that μ is a free primitive, not tied to a posterior over θ.
  - Removed a duplicate import.

## Check 2: kernel and axioms
- **Full shared build:** green, 7768 jobs, warning-free.
- **Axioms:** only propext, Classical.choice and Quot.sound, on all 5 theorems and their frozen copies.
- **leanchecker:** exit 0 on `Information.GlobalGames` and `Audit.Statements.GlobalGames`.
- **nanoda:** 10 headline and frozen declarations plus their closure, 34,080 declarations, no typechecker errors.
- **Comparator:** stand-in is the frozen-statements file.
