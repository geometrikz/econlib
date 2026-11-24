# Review record: behavioral round 14 (2026-11-24)

Modules: `BoundedRationality/SwapRegret.lean` (swap regret), `BoundedRationality/CursedMixed.lean`
(behavioral-strategy BNE via the agent normal form; Eyster–Rabin cursed equilibrium and
Jehiel–Koessler ABEE in behavioral strategies, with existence). Header updates in `Cursed.lean`
and `Analogy.lean` (pointers to CursedMixed; no statement changes).
Frozen statements: `Audit/Statements/BehavioralXIV.lean` (14 statements).

## Step 1: adversarial statement review (context-isolated agent)
No MAJOR findings. The reviewer checked by hand `swapGain_eq_sum`, `isCorrelatedEq_iff_swap`,
`behavCursedInterim_eq` (term by term), the cursed belief `avgProb` against Eyster–Rabin Def. 1,
the agent-form marginalization, and `behavAnalogyInterim_eq` (needs `IsAnalogyPartition`).
MINOR, addressed in documentation:
* prior-weighted interim payoffs make these ex-ante (Harsanyi) equilibria; null types face no
  condition (same convention as `Games/Bayesian.lean`, MWG); coincides with interim when all
  types have positive probability (Eyster–Rabin's assumption);
* `χ` ranges over ℝ; only `[0,1]` gives probability beliefs; results hold for all `χ`;
* swap-regret header wording (corollary not stated separately; CE/no-swap equivalence is
  folklore);
* ABEE: no pure-ABEE nonexistence counterexample formalized; opponent bundling not covered.

## Step 2: mechanical checks
* `lake build EconLean` against the shared tree: success, 7802 jobs, no warnings.
* `#print axioms` on all 30 blueprint names: only propext, Classical.choice, Quot.sound.
* `leanchecker` on SwapRegret, CursedMixed, Cursed, Analogy, BehavioralXIV: pass.
* `leanexport` + `nanoda`: 16959 and 30213 declarations, no typechecker errors.
* Blueprint: `leanblueprint pdf` and `web` succeed, no undefined references.
