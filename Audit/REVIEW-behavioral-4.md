# Review record: behavioral round 4 (2026-11-23)

Scope: `Behavioral/{SocialPreferences,Salience,ShroudedAttributes,ContractDesign,Falmagne}.lean`,
`Information/PersuasionExistence.lean`, the new existence results in
`Behavioral/{ReferenceDependence,RationalInattention}.lean`, and the fixes for the independent
review's open points (`Audit/REVIEW-independent.md`, review-F).

## Step 1: isolated adversarial statement review

A context-isolated agent saw only the stripped statements (comments removed, proofs replaced by
`sorry`) and the source papers: Fehr–Schmidt 1999, Bolton–Ockenfels 2000, Bordalo–Gennaioli–Shleifer
2012, Gabaix–Laibson 2006, DellaVigna–Malmendier 2004, Falmagne 1978 / Fiorini 2004,
Kamenica–Gentzkow 2011, Kőszegi–Rabin 2006/07, Matějka–McKay 2015.

Result: **no major findings**. Every headline statement was checked by hand, including edge cases,
and found correct with jointly satisfiable hypotheses. Minor findings and how they were handled:

| Finding | Resolution |
|---|---|
| DM: optimality of `p*` is proved on `Region` (both thresholds in [0,1]), a local interior optimum; a numeric example with β̂ < β shows a better price outside `Region` | Documented as scope in the file header (DM also characterize the interior FOC). No counterexample found with 0 ≤ β ≤ β̂ ≤ 1. Global optimality left open. |
| BGS: `sigma_ordering` covers intervals of gains only | Documented (losses follow by `sigma_neg`; straddling intervals not covered). |
| GL: λ = 1 (unshrouding educates all myopes); deviator captures whole segment on ties; `pStar`/`zero_profit` presume ĉ < e < v̂ | Documented as modelling choices in the header; theorems state the hypotheses they use. |
| KR: `exists_pe`/`exists_ppe_of_convex` need convex D (randomization); KR's binary choice sets are not convex | Documented next to `exists_pe`. |
| KR: `two_PE_example` garbled in the review copy | Artifact of the stripping script (a `let … :=` inside the statement); the source is unchanged from round 1 and compiles. |

Notes acted on: `ultimatum_offer_half` was only weak optimality; added
`ultimatum_offer_half_unique` (strict for s ≠ 1/2). Notes recorded but not changed: ERC dictator
result assumes strictly increasing v and shows only that gifts > 1/2 are dominated; salience ranks
use competition ranking (documented); the persuasion bound is |Ω|+2 messages, weaker than KG's |Ω|
(documented); RI uses a full-support prior.

Independent-review open points (review-F) for these files:
- KR choice sets were not probability vectors → `IsLotterySet` added to `IsPE`/`IsCPE`; done.
- KR `exists_ppe` assumed a PE exists → `exists_pe` (Kakutani, convex compact lottery sets),
  `exists_ppe_of_convex`, `exists_ppe_allLotteries`; done.
- MM: existence of an optimal rule → `exists_isOptimalRule`, `exists_optimal_generalizedLogit`;
  done. MM Corollary 1 (symmetric problems) still open (needs convexity of mutual information).
- Gul–Pesendorfer converse (axioms ⇒ representation) still open.
- Falmagne converse → `falmagne`, `isRUM_iff_bm_nonneg`; done.
- KG optimal-signal existence → `exists_optimal_signal`; done.

## Step 2: mechanical checks

- Frozen statements: `EconLean/Audit/Statements/BehavioralIV.lean` (33 theorems) and the updated
  `Audit/Statements/Behavioral.lean` (KR) build.
- `#print axioms` on all 232 theorems of the touched modules and frozen files: only `propext`,
  `Classical.choice`, `Quot.sound` (4 use none).
- `leanchecker` on all ten modules: exit 0.
- `leanexport` + nanoda (45,529 declarations): no typechecker errors (one pretty-printer
  message, "Unable to print axioms", as in earlier rounds).
- No `sorry`; `lake build` warning-free; blueprint `leanblueprint pdf` and `web` build.
