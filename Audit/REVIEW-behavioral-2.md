# Review record: rational inattention, ambiguity, bounded rationality (2026-11-23)

Files: `EconLean/Behavioral/{RationalInattention,Ambiguity}.lean`,
`EconLean/BoundedRationality/{LevelK,QRE,BerkNash}.lean`.
Frozen statements: `EconLean/Audit/Statements/BehavioralII.lean` (30 headline theorems).
Blueprint: `blueprint/src/chapters/behavioral.tex` (§ rational inattention, ambiguity) and
`blueprint/src/chapters/bounded_rationality.tex`; every theorem in these files has a `\lean` entry.

## Step 1: context-isolated adversarial review

The reviewer saw only statements and definitions (proofs and comments stripped) plus the source papers:
Sims 2003, Matějka–McKay 2015, Gilboa–Schmeidler 1989, Ellsberg 1961, Nagel 1995, Stahl–Wilson 1995,
Camerer–Ho–Chong 2004, McKelvey–Palfrey 1995, Esponda–Pouzo 2016.

First pass found four problems. All were fixed, and a second pass on the changed declarations
found no remaining problems.

| Finding | Fix |
|---|---|
| Matějka–McKay theorem assumed every action has positive marginal probability, which excludes the paper's main case (unchosen actions) | Assumption dropped. New Gibbs lemmas for a default that may vanish (`gl_*`, `objective_le0`, `eq_gl_of_optimal0`, `kl_nonneg0`). The uniform-marginal corollary no longer assumes `c > 0`. |
| QRE existence was proved only for a scalar 2×2 fixed point, not linked to the general `IsLogitQRE` | Bridge `isLogitQRE_of_qre2x2` and `exists_isLogitQRE_2x2`: every 2×2 game has a logit QRE in the general sense. Added `uniform_isLogitQRE_zero` (the λ=0 QRE exists). |
| Berk–Nash example did not use KL minimization and the model was correct on the played action | New example: true success 1/2 and 7/10; the model says the action is irrelevant with success 2/5 or 9/20 (`example1_misspecified`: no parameter is correct). Action 0 with belief on 9/20, the KL-best fit, is Berk–Nash, while action 1 is truly better (1/2 < 3/5). |
| Level-k beauty contest results read as statements about the finite game | Documented as the large-population approximation; `beauty_fixed_iff` labelled an algebraic lemma; level-0 documented as a pure anchor profile. |

## Step 2: mechanical checks

- `lake build` of all five modules and the frozen statements file: no errors, no warnings, no `sorry`.
- `#print axioms` on all 95 theorems (library + frozen): each uses only `propext`, `Classical.choice`,
  `Quot.sound`.
- `leanchecker` on each of the six modules: exit 0.
- `nanoda_bin` 0.4.17 on a `leanexport` of all 95 theorems: 18,107 declarations, no typechecker errors
  (one pretty-printer message, "Unable to print axioms", not a check failure).

## Open items (not formalized)

- Matějka–McKay: existence of an optimal rule and the fixed-point characterization of the marginal.
- Gilboa–Schmeidler representation theorem (axioms ⇒ maxmin EU); priors are a finite set, whose minimum
  equals the minimum over its convex hull.
- Poisson specialization of cognitive hierarchy; the finite-player beauty contest and uniqueness of its
  all-zero equilibrium.
- General logit QRE existence (needs Brouwer, missing from Mathlib); converse of the 2×2 bridge.
- Berk–Nash existence (needs Kakutani); weak identification ⇒ self-confirming equilibrium; uniqueness of
  the Berk–Nash strategy in the example (the reviewer notes 9/20 is the KL minimizer under every mixed
  strategy).
