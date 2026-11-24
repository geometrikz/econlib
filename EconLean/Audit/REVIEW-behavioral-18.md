# Review: behavioral round 18 (Rabin–Weizsäcker full iff, fair coins)

Files: `Behavioral/CARACharacterization.lean` (new), `Behavioral/RabinWeizsacker.lean` (header only).
Frozen statements: `Audit/Statements/BehavioralXVIII.lean` (9 statements).

## Step 1: adversarial statement review (context-isolated agent, 2026-11-24)
No statement was vacuous, contradictory or wrongly quantified. Findings and fixes:
- MAJOR (header scope): `rabinWeizsacker`'s "⇒" holds only within the `NarrowDominated` class
  (fair-coin lottery-vs-sure pairs, second lottery a constant shift of the first, strict narrow
  choices). Header and blueprint now say so explicitly; continuity flagged as an extra assumption.
- MINOR: added `isCARAorLinear_of_ti` (composed Nagumo–de Finetti–Jessen step); added two-sided
  witnesses `cara_isCARAorLinear`, `id_isCARAorLinear`; noted that `IsCARAorLinear` builds in strict
  monotonicity and that `isCARAorLinear_of_affine_shift` does not need positive slopes; cited Aczél §3.1.
- Not done: iff version of `narrowDominated_affine`; smooth non-CARA witness (kink witness kept).

## Step 2: mechanical checks
- `#print axioms` on 12 declarations: only propext, Classical.choice, Quot.sound.
- `leanchecker` on CARACharacterization and BehavioralXVIII: exit 0.
- `leanexport` + nanoda: 17438 declarations, no typechecker errors (one benign "Unable to print axioms").
- Frozen file compiles against the library.
- `lake build EconLean` on the shared tree: every module built (7862/7864); the root file failed only on a
  clash outside this round: `Econ.Audit.frozen_policy_monotone` is declared in both
  `Audit/Statements/StationaryUnique.lean` and `Audit/Statements/RamseyStochastic.lean`.
- Blueprint `leanblueprint pdf` and `web` succeed; new label `thm:beh-rw-iff` resolves.
