# Review record: behavioral decision theory (2026-11-23)

Files: `EconLean/Behavioral/{PresentBias,RankDependent,ReferenceDependence,Temptation,Logit}.lean`.
Frozen statements: `EconLean/Audit/Statements/Behavioral.lean` (46 headline theorems).

## Step 1: context-isolated adversarial review
The reviewer saw only the statements and definitions (proofs and comments stripped) plus the source
papers: Laibson 1997, O'Donoghue–Rabin 1999, Strotz 1956, Quiggin 1982, Kahneman–Tversky 1979,
Tversky–Kahneman 1992, MWG 6.D, Kőszegi–Rabin 2006/2007, Gul–Pesendorfer 2001, Matějka–McKay 2015,
Anderson–de Palma–Thisse 1988.

First pass: no statement was wrong or vacuous. All worked examples were re-computed and matched the paper
(report: τ_tc=1, τ_s=2, τ_n=4; movie: τ_tc=4, τ_s=1, τ_n=3). Two results overclaimed, and several
definitions carried junk values or unstated conventions. Fixes:

| Finding | Fix |
|---|---|
| Logit file labelled as Matějka–McKay's theorem but proves only the per-state step for a fixed full-support `P` | Header now scopes it as that step and lists the missing parts (mutual information as min of average KL, endogenous `P`, `Pᵢ = 0`). Added `generalizedLogit_const_eq_softmax`. |
| KR endowment results use the status quo, not expectations, as the reference | Documented. Added the expectations-based PE results `keep_isPE_iff` (keep is a PE iff p ≤ WTA) and `sell_isPE_iff` (sell is a PE iff p ≥ v(1+η)/(1+ηλ)). |
| `Lottery` allowed mass off the grid (junk, e.g. `fairCoin` p 3 = 1/2) | Added the field `eq_zero_of_lt`; fixed `fairCoin`. |
| Ranking conventions not stated (the index order is the ranking; `cpt` normalizes v(r)=0, w±(0)=0) | Documented in docstrings. Added `cpt_zero_eq_rdu` (CPT with no losses = RDU). |
| `presentValue` truncates s − t for s < t; δ = 1 in the task model | Documented. |
| GP menus are finite deterministic sets, not lotteries | Documented. |
| Stochastic KR PE existence not shown (`exists_ppe` assumes a PE) | Documented. Riskless PE existence is `isPEDet_of_isMax`. |
| `WTP` number reused as seller's PE cutoff | Docstring clarifies. |

Second pass, on the changed declarations (`Lottery`, `fairCoin`, `cpt_zero_eq_rdu`, `keep_isPE_iff`,
`sell_isPE_iff`, `generalizedLogit_const_eq_softmax`): all faithful.

Open (suggested, not done): the full Matějka–McKay theorem; stochastic KR PE existence; PPE/CPE mug cutoffs;
`sophDate 1 = tcDate`; OR welfare bounds; the GP representation (sufficiency); TK92/Prelec weighting functions.

## Step 2: proof checks
- `#print axioms` on 42 headline theorems: `propext, Classical.choice, Quot.sound` only. No sorry.
- `leanchecker` (toolchain `bin/`, one module per call): exit 0 on all five modules and the frozen-statements module.
- `nanoda_bin` 0.4.17 on a `leanexport` of all 46 frozen theorems: 18,080 declarations, no typechecker errors
  (one pretty-printer message, "Unable to print axioms", not a check failure).
- Comparator stand-in: `Audit/Statements/Behavioral.lean` restates every headline verbatim and closes it with
  the library theorem.
- `lake build` of all six modules: no warnings.
