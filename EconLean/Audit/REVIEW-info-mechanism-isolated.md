# Adversarial review: p3 (Information, Mechanism, Games/Repeated, Matching)

Scope: every `.lean` file under `/home/user/review/p3/`. Imported definitions were checked in
`/mnt/project-files/econlean/EconLean/` (`IsNash`, `IsBNE`, `interim`, `SimpleLottery`, `lotteries`,
`pdPayoff`). Sorries are ignored. Each statement was checked by hand against the canonical result.
No statement turned out false, and no hypothesis set is contradictory.

Severity legend: WRONG / OVERCLAIM / WEAK / NIT.

---

## Information/Lemons.lean

- **OVERCLAIM: module docstring, `isLemonsEq_iff`.** The docstring says "Every car above the worst
  is withdrawn, although trading it would be efficient (buyers value it as much as sellers)." With
  `r(θ) = θ` there are **zero** gains from trade, so withdrawing a car loses no welfare. The
  inefficiency that makes Akerlof's result matter is absent. The statement itself is true but
  economically degenerate: `E[θ | θ ≤ p] = p` forces all offered mass onto `p`, which is close to a
  tautology. Canonical versions (Akerlof 1970; the MWG §13.B treatment with seller reservation value
  `r(θ)` below buyer value) have strict gains from trade, so unravelling destroys surplus.
  *Fix:* parametrise the seller's value as `r(θ) = α θ` with `α < 1`, or more generally `r(θ) < θ`.
  Define equilibrium as `p = E[θ | r(θ) ≤ p]` with mass > 0. Then prove unravelling to the bottom
  under a condition on `F` (or for a concrete witness distribution), and prove that surplus
  `∑ (θ − r θ)` from withdrawn cars is lost. Alternatively, drop the words "although trading it
  would be efficient".
- **NIT: label.** "MWG Example 13.B.1 with `r(θ) = θ`" picks the knife-edge case where the example
  has no bite. Say so explicitly.
- `IsLemonsEq.only_worst`: no findings.

## Information/MoralHazard.lean

- **WEAK: `fullInsurance_optimal`.** It shows that the constant contract is *a* cheapest contract.
  MWG Prop. 14.B.2 also gives uniqueness under strict risk aversion: with `StrictConvexOn` and a
  full-support `f`, any cheapest contract is constant. Suggest adding the strict/uniqueness version.
- **WEAK: `sellTheFirm`.** The third conjunct only computes the principal's profit as
  `E_H π − gH − ū`. It does not show that this is the first-best: it never proves the value is at
  least the profit of any IR contract with either effort level. The docstring's "first-best
  profit" holds only by the reader's arithmetic. Suggest stating that it is at least
  `max(E_Hπ − gH − ū, E_Lπ − gL − ū)`, or that no IR contract with observable effort does better.
- **NIT.** `φ : ℝ → ℝ` is assumed convex and monotone on all of `ℝ`. Inverse utilities of bounded
  utilities (for example CARA, whose inverse is defined only on `(−∞, 0)`) do not fit. This is
  acceptable, but it is a restriction.
- **NIT.** The module docstring ties `implementsHigh_nonconstant` to "if `fH` has full support",
  but the theorem (correctly) does not need that hypothesis.
- `implementsHigh_cost_gt`: correct. IC forces `E_L ν − E_H ν ≤ gL − gH < 0`, so `ν` is
  non-constant. Full support plus strict Jensen plus monotonicity then gives the strict inequality.

## Information/Screening.lean

- **WEAK: `IsOptimalMenu.noDistortionAtTop`.** It proves no distortion at the top, zero rent at the
  bottom and a binding `IC_H`. It does **not** prove the companion half of MWG Prop. 14.C.6: the
  low type's quantity is distorted downward, `qL ≤ qL^FB` (strictly below it when `pH > 0` and
  `θH > θL` with `v` strictly increasing and concave). The downward distortion appears only in the
  witness's docstring, as a comment. Suggest adding a comparative statement: if `qL` maximises
  `virtualL`, `qL^e` maximises `θL v − c q`, and `v` is increasing, then `v qL ≤ v qL^e`.
- **NIT.** The model never imposes `pL + pH = 1`, `v` increasing or concave, or `v 0 = 0`. The
  statements stay correct because the needed facts are assumed directly (`hvL`, `hmono`, and the
  maximiser hypotheses). In the canonical model the monotonicity hypothesis `v qL₀ ≤ v qH₀` is a
  consequence rather than an assumption.
- `screeningProfit_le`, `bindingMenu_feasible`, `screeningProfit_bindingMenu` and
  `isOptimalMenu_binding` were checked algebraically: correct. Witness numbers check out:
  `surplusH = 1.5q − q²` gives `3/4`, and `virtualL = q/8 − q²/4` gives `1/4`.

## Information/Signaling.lean

- **NIT: module docstring.** "`c eH θH ≤ θH − θL ≤ c eH θL`" silently assumes `c 0 θ = 0`. The
  theorems correctly use differences `c eH θ − c 0 θ`.
- **NIT: module docstring.** "a pooling level `e*` is an equilibrium **iff** the low type prefers
  it ..." is too strong. Sufficiency (`isSpencePBE_pooling`) also needs monotone costs and the
  single-crossing inequality `hsc`. The theorem statements themselves are honest.
- **NIT: `IsSpencePBE`.** It does not require `0 < pH < 1`. If `pH ∈ {0,1}`, the "on-path" Bayes
  constraints are imposed on a zero-probability message. This is harmless because it is more
  restrictive.
- **NIT.** No pooling witness is given; only a separating one is.
- `separating_eL`, `separating_bounds`, `isSpencePBE_separating`, `pooling_bound` and
  `isSpencePBE_pooling` were checked: correct. The constructions verify for all deviations
  `e ≥ 0`.

## Mechanism/Revelation.lean

No findings. `IsDominantEq` and `IsDSIC` match MWG Defs. 23.B.5 and 23.B.6. The prior-weighted
`IsBIC` is the standard equivalent of the conditional definition for positive-probability types,
and the docstring discloses this. `IsBNE` (ex-ante Nash with `p` a lottery) implies the
prior-weighted interim condition.

## Mechanism/VCG.lean

- **NIT: attribution.** The header cites "MWG Props. 23.C.4–23.C.5". As I recall, 23.C.5 is the
  Green–Laffont converse (only Groves mechanisms are truthful and efficient on rich domains), which
  the file explicitly does not formalise. Cite 23.C.4 only, and check the numbering.
- **NIT.** The witness covers one case of the second-price auction (`θ1 ≤ θ0`).
- `groves_truthful`, `clarke_transfer_nonpos` and `clarke_individuallyRational` were checked:
  correct, with the hypotheses they need and no more.

## Mechanism/Myerson.lean

- **WEAK / NIT: `revenue_equivalence`, `expected_revenue_eq`.** This is the one-agent
  reduced-form (interim) version. MWG Prop. 23.D.3 is a multi-bidder auction statement: BIC
  mechanisms with independent private values, the same interim allocation probabilities and the
  same lowest-type utility yield equal expected revenue. The multi-agent version follows per bidder
  only after linking interim `q_i` and `p_i` to an ex-post mechanism and BIC. That link is not
  formalised. The docstring does not overclaim, but the MWG citation suggests more than is proved.
- `myerson_ic_iff` and `sub_eq_integral_of_sandwich` were checked: correct, including the empty
  case `a > b`. The integral only uses `q` on `[a, θ] ⊆ [a,b]`.

## Mechanism/OptimalMechanism.lean

- **OVERCLAIM (minor): `postedPrice_optimal`.** The docstring says the posted price `θ m`
  "maximises expected revenue among all IC and IR mechanisms". The theorem has no monotonicity
  hypothesis on `θ`, so it only proves an upper bound by the posted-price revenue. Without
  `MonotoneOn θ (Iio n)` the posted price need not itself be IC or IR. For example, with
  `θ = (2, 1)` and `m = 1`, type 0 buys at price 1 while type 1 does not, which violates IC. So
  "optimal mechanism" does not follow from the statement alone. *Fix:* add `hθ` and conclude
  `IsICDiscrete … (postedQ m) (postedP θ m) ∧ IsIRDiscrete … ∧ bound`.
- **NIT: `postedPrice_rent_eq`.** The docstring says "With nondecreasing types", but the identity
  holds with no hypothesis (the sum telescopes). Update the docstring.
- **WEAK.** The witness only evaluates virtual weights. It never instantiates
  `postedPrice_optimal` or `postedPrice_IC_IR`. Ironing for non-single-crossing weights is not
  covered, which is acknowledged implicitly.
- `revenue_eq_virtual_sub`, `rentFloor_le` and `revenue_le_virtual` were checked: correct.

## Mechanism/BilateralTrade.lean

- **WEAK: witness.** The posted-price witness shows that DSIC and budget balance are jointly
  satisfiable. It does not show that efficiency and DSIC are jointly satisfiable (for example the
  Groves/VCG mechanism `tB = c·x`, `tS = v·x`). That witness would show budget balance is the
  binding constraint. Suggest adding it.
- The label is honest. It is explicitly the dominant-strategy (Hurwicz / Green–Laffont)
  impossibility, and the file says Bayesian Myerson–Satterthwaite is not formalised. Ex-post budget
  balance `tB = tS`, both-sided DSIC on `[a,b]`, and efficiency on strict inequalities are all
  canonical. The statement is true: payments are pinned as `tB = c·x + hB(c)` and
  `tS = v·x + hS(v)` at interior points, and BB contradicts this on the no-trade region. No other
  findings.

## Games/Repeated.lean

- **WEAK: `nashReversion_folk`.** Only pure stage profiles `a` are supported. Friedman's theorem
  covers any feasible payoff vector, including convex combinations (via public randomisation or
  time-averaging), that strictly dominates a stage-NE payoff. The docstring is accurate about what
  is proved, but the label "folk theorem" is broader than the statement.
- **NIT: `discPayoff` / `IsRepeatedSPE`.** These use `tsum`, which returns `0` on non-summable
  streams. `IsRepeatedSPE` is meaningful only for bounded stage payoffs. All theorems assume
  boundedness, but the definition does not. Consider bundling boundedness, or note it in the
  docstring.
- `IsRepeatedSPE` (all histories, all repeated-game deviations), `grimTrigger_isSPE` (correct
  one-shot condition `(1−δ)u_i(s, a_{−i}) + δ u_i(e) ≤ u_i(a)`) and the PD witness (`δ ≥ 1/5`)
  were checked: correct.

## Matching/GaleShapley.lean

- **WEAK.** All partners are acceptable: there is no outside option, and stability omits individual
  rationality. Gale–Shapley and Roth–Sotomayor allow unacceptable partners, with stability
  requiring IR. Suggest adding acceptability thresholds `um m none`, `uw w none`.
- **NIT.** `exists_stable_matching` assumes `hum` and `huw`. Strictness is not needed for existence
  (ties can be broken arbitrarily). `huw` is also unnecessary for men-optimality.
- `IsMatching`, `IsBlocking`, `IsStableMatching` and the men-optimality conclusion (including "is
  matched under `μ` whenever matched in some stable `ν`") match the canonical definitions.
  `optInv_daStep` and `exists_best_proposer` are true as stated.
