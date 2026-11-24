# Review record: behavioral round 17 (2026-11-24)

Module: `Behavioral/RabinWeizsacker.lean` (narrow bracketing with wealth effects yields
state-wise dominated combined choices; CARA and linear utility never do). Header-only edit
in `NarrowBracketing.lean` (pointer). Frozen statements: `Audit/Statements/BehavioralXVII.lean`
(7 statements).

## Step 1: adversarial statement review (context-isolated agent)
No MAJOR findings. Verified: `NarrowDominated` models two decisions (lottery vs sure amount,
second lottery a shift of the first), strict narrow choices, and state-wise domination by
δ > 0 of the opposite combination; the converse for CARA checked by hand; the kink example is
right; the conclusion is not trivial (fails for CARA/linear).
MINOR, fixed: `IsProb p` added to `NarrowDominated` and to the main theorem (without it a
non-probability weight vector gave a spurious "wealth effect"); risk-loving CARA `exp(βx)`
added (`caraLove_not_narrowDominated`); header notes that the main theorem needs only
continuity and that `WealthEffect` is a strict reversal for the given `p`.
Not formalized (stated in the header): non-CARA ⇒ wealth effect (functional equation).

## Step 2: mechanical checks
* `lake build EconLean` against the shared tree: success, 7846 jobs, no warnings.
* `#print axioms` on all 23 blueprint names: only propext, Classical.choice, Quot.sound.
* `leanchecker` on RabinWeizsacker, NarrowBracketing, BehavioralXVII: pass.
* `leanexport` + `nanoda`: 15779 declarations, no typechecker errors.
* Blueprint: `leanblueprint pdf` and `web` succeed, no undefined references.
