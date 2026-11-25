# Review: behavioral round 19 (menu preferences from axioms)

Files: `Behavioral/TemptationAxioms.lean` (new), `Behavioral/Temptation.lean` (header only).
Frozen statements: `Audit/Statements/BehavioralXIX.lean` (11 statements).

## Step 1: adversarial statement review (context-isolated agent, 2026-11-25)
No MAJOR findings; the reviewer verified the counterexample by hand. MINOR fixes applied:
- Header now says the pair reduction is an alternative finite-menu route, not a step of GP's proof.
- Dropped the overclaim that GP pair values "need lotteries"; now: set betweenness places no
  restriction across pairs, GP get it from independence over lotteries.
- `sbExample_not_GP` strengthened to menus of size at most two.
- Header notes: W represents a preference (ordinal axioms; non-representable preferences not covered);
  `W ∅` is unconstrained; `StrategicRational` is Kreps' special case, preference for flexibility not treated;
  admissible pair data are not characterized.
- Renamed `GP_eq_maxmin` to `W_eq_maxmin_pairs`.
- Not done: reordering the conjuncts of `SetBetweenness` to match `setBetweenness`.

## Step 2: mechanical checks
- `#print axioms` on 12 declarations: only propext, Classical.choice, Quot.sound (the `decide` proof uses no native reduction).
- `leanchecker` on TemptationAxioms, Temptation, BehavioralXIX: exit 0.
- `leanexport` + nanoda: 8929 declarations, no typechecker errors (one benign "Unable to print axioms").
- `lake build EconLean` on the shared tree with these files: success (7874 jobs).
- Blueprint `leanblueprint pdf` and `web` succeed; new label `thm:beh-gp-pairs`.
