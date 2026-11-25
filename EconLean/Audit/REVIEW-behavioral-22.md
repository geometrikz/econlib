# Review: behavioral round 22 (choice from lists, Rubinstein–Salant 2006)

Files: `Behavioral/ChoiceFromLists.lean` (new). Frozen statements: `Audit/Statements/BehavioralXXII.lean` (13 statements).

## Step 1: adversarial statement review (context-isolated agent, 2026-11-25)
No MAJOR findings. The reviewer checked lists/PI/LIIA against RS, hand-verified that the left fold of `step` picks the
first (δ = false) or last (δ = true) maximal element, the revealed `relOf`/`deltaOf`, quantifiers of `pi_iff_rule`,
that nothing needs X finite (statements are stronger than RS), and the satisficing encoding (RS Example 2).
MINOR fixes applied:
- Added `first_eq_rule` and `first_not_rational` (first-element rule has PI but no strict preference rationalizes it).
- Header: Proposition 1 conditional on `IsChoice`, lists `liia_pi`/`pi_liia`; scope note says first/last tie-breaking is by
  construction (only maximality is a theorem), satisficing only checked to pick a satisfactory element, uniqueness of
  (R, δ) not formalized (δ unique only on classes with ≥ 2 elements).
- Not done: `rule_eq_first`/`rule_eq_last` via `find?`; exact satisficing formula.

## Step 2: mechanical checks
- `#print axioms` on all declarations: only subsets of propext, Classical.choice, Quot.sound.
- `leanchecker` on ChoiceFromLists and BehavioralXXII: exit 0.
- `leanexport` + nanoda: 1178 declarations, no typechecker errors (one benign "Unable to print axioms").
- `lake build EconLean` on the shared tree with these files: success (7926 jobs).
- Blueprint `leanblueprint pdf` and `web` succeed; new section `sec:beh-lists`, theorem `thm:beh-lists`.
