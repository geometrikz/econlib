# Review record: partial equilibrium and IO, social choice, bargaining, cooperative games,
# Myerson–Satterthwaite, first-price auction, DA strategy-proofness, assortative matching

Date: 2026-11-23. Files:
`Mechanism/{MyersonSatterthwaite,FirstPrice}`, `Matching/{StrategyProof,Assortative}`,
`Partial/{Externalities,PublicGoods,Oligopoly,Monopoly,Salop,DiamondParadox}`,
`SocialChoice/{May,MedianVoter}`, `Bargaining/Nash`, `Cooperative/{Shapley,Core}`.
Frozen statements: `Audit/Statements/PartialSocial.lean`.

## Step 1: context-isolated adversarial review

A fresh agent saw only proof-stripped copies (`verify/strip_proofs.py --keep-comments`) of the
15 files plus the supporting definitions they use (Games/ZeroSum, Games/Strategic,
Uncertainty/VNM, Matching/GaleShapley, Mechanism/{BilateralTrade,Myerson}). Its full table is
`REVIEW-partial-social-isolated.md`.

Round 1: no statement false (SUSPICIOUS) or wholly vacuous. Findings and what was done:

| Finding | Verdict | Action |
|---|---|---|
| `IsMedianPeak`/`median_condorcet` use a strict median: no median exists for even `n` with distinct peaks | MISMATCH / VACUOUS-RISK | Added `IsWeakMedianPeak`, `median_not_defeated` (MWG 21.D.1, any `n`), `exists_weakMedian`, and a two-voter witness; `median_condorcet` relabelled the strict form. |
| `bertrand_isNash_iff` assumed demand positive at every price (excludes linear demand) | WEAK | Restated with continuous, nonincreasing, nonnegative demand and `x(c) > 0`; proof rewritten (`bertrand_exists_pos`). |
| `myerson_satterthwaite`: constraints at every type in `[a,b]`, distributions only supported there | WEAK, docstring MISMATCH | Statement kept; module and theorem docstrings state the scope (matches MWG under full support) and the reviewer's posted-price example. Open: support-restricted version. |
| `IsParetoExt` did not require `h ∈ H`; `coase_theorem` does not model bargaining | WEAK | Feasibility added to the definition; docstring says this is the efficiency form. |
| `discrimination_price_le` only algebra | WEAK | Added `discrimProfit` and `third_degree_discrimination` (joint two-market profit maximization). |
| `monopoly_output_lt` not tied to the optimum | WEAK (minor) | Added `monopoly_optimum_lt_competitive`. |
| `salop_free_entry` was an identity | WEAK (minor) | Now an iff characterization for `n > 0`. |
| `gs_blocking_lemma` drops `w ∈ μ(M')`; `daMatching_strategyproof` has no truncation or coalitional version | WEAK | Scope stated in docstrings. Open items. |
| `becker_pam` docstring overclaimed (Shapley–Shubik link) | WEAK | Docstring corrected; gaps listed. |
| Stackelberg comparison is bare arithmetic; Diamond search rule is reduced form | WEAK (minor) | Docstrings say so. |

Round 2 (same isolated agent, revised stripped files): all items resolved or acceptably
scoped; nothing new wrong. Remaining notes: optional full-support corollary for
Myerson–Satterthwaite; `monopoly_optimum_lt_competitive` allows an arbitrary nondecreasing `MC`
away from the monopoly output (more general, not wrong).

## Step 2: kernel checks

* `#print axioms`: all 108 theorems and lemmas in the 15 files depend only on `propext`,
  `Classical.choice`, `Quot.sound`.
* `lake env leanchecker` on every module (and the frozen file): pass.
* nanoda (independent kernel) on an export of all of them: 44,503 declarations, no
  typechecker errors.
* Full shared build with the new files and imports: pass, warning-free.
* Blueprint: chapters `partial.tex`, `socialchoice.tex`, `cooperative.tex`, sections added to
  `mechanism.tex` and `matching.tex`; every declaration has an entry; `leanblueprint pdf` builds.

## Open

Myerson–Satterthwaite with constraints only on the supports; Gale–Sotomayor `w ∈ μ(M')`;
coalitional strategy-proofness and truncation strategies; Becker uniqueness/NAM; TTC and
housing markets; matching with contracts; school choice; two-sided markets; BLP contraction.
