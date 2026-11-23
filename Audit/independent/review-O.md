# Statement review: Behavioral/* (15 files) + BoundedRationality/BerkNash.lean

Reviewer stance: adversarial. All files were read in full. Lean was not run. Mathlib junk-value semantics were checked by hand. Overall result: **no MISMATCH or VACUOUS statement was found among the headline theorems.** The problems are (i) key economic steps that are still assumed rather than derived (Matějka–McKay uniform marginals; Kőszegi–Rabin PE existence in the finite case), and (ii) coverage gaps: the canonical theorem a file's name suggests is not stated (Rabin–Weizsäcker; Salience's Allais/common-ratio results; Berk–Nash existence lives in another file).

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `IsChoiceRule`, `luce`, `ChoiceAxiom`, `probSet` | StochasticChoice | Luce (1959) | faithful | Constraints apply to nonempty menus only. `P ∅ ·` is unconstrained but never used. |
| `luce_iia`, `luce_choiceAxiom`, `luce_isChoiceRule` | StochasticChoice | Luce (1959) | faithful | Strictly positive weights, so no `x/0` junk. |
| `eq_luce_of_choiceAxiom` | StochasticChoice | Luce (1959) Thm 3 | faithful | Positivity is assumed, as Luce does. Weights are `P univ ·`. |
| `softmax_eq_luce` | StochasticChoice | McFadden logit | faithful | Identity. |
| `Ranking`, `IsTop`, `IsRUM`, `rumP`, `rumP_regularity` | StochasticChoice | Block–Marschak (1960) | faithful | Strict linear orders; rank 0 = best. |
| `bm`, `bm_rumP`, `bm_rumP_nonneg` | StochasticChoice | BM polynomial K(a,A)=Σ_{B⊇A}(−1)^{|B∖A|}P(a,B) | faithful | Sums only over supersets of A, so no empty-menu junk. |
| `falmagne`, `isRUM_iff_bm_nonneg` | Falmagne | Falmagne (1978) Thm | faithful | Full iff. P is assumed to be a choice rule only, with no extra regularity. Holds for empty and singleton X, as it should. |
| Chain/flow lemmas (`G_eq_one`, `hit_eq`, `reach_eq_T`, …) | Falmagne | proof internals | faithful (quick pass) | Auxiliary lemmas. |
| (coverage) Luce ⇒ RUM | StochasticChoice | Holman–Marley; McFadden | gap | Not stated, although it follows from `isRUM_iff_bm_nonneg` (sanity test 3). |
| `kl`, `mutualInfo`, `marginal`, `riObjective` | RationalInattention | Matějka–McKay (2015) | faithful with documented deviation | `kl p q` gives a finite junk value when q_i=0<p_i (log 0 = 0). In `mutualInfo` the reference is the marginal, which dominates every p ω when the prior is positive (`rule_eq_zero_of_marginal_eq_zero`), so no harm. `IsPrior` requires full support. |
| `optimal_is_generalizedLogit` | RationalInattention | MM (2015) Thm 1 | faithful | Derived from optimality alone. Covers zero-marginal actions. |
| `optimal_is_softmax_of_uniform` | RationalInattention | MM (2015), a-priori-homogeneous corollary | **WEAK** | Uniform marginals are still **assumed** (`hunif`), not derived from a symmetric prior. |
| `exists_isOptimalRule`, `exists_optimal_generalizedLogit` | RationalInattention | existence | faithful | `continuous_riObjective` holds for arbitrary g, because MI = Σ g p log p − Σ m log m. |
| `u`, `gainLoss`, `μLin`, `U` | ReferenceDependence | Kőszegi–Rabin (2006) | faithful with documented deviation | Finite outcome support (bundles indexed by ι). μ is arbitrary; KR's A0–A4 are imposed only where needed. |
| `IsPE`, `IsPPE`, `IsCPE` | ReferenceDependence | KR (2006) Defs 1–2; KR (2007) CPE | faithful | |
| `exists_ppe` | ReferenceDependence | KR (2006) | **WEAK** | PE existence is still a **hypothesis** (`hPE`) for finite D. It is genuinely needed for general μ (sanity test 2). |
| `exists_pe`, `exists_ppe_of_convex`, `exists_ppe_allLotteries`, `exists_ppeDet` | ReferenceDependence | KR (2006) | faithful | Existence **derived** for convex compact D, for the full simplex, and for deterministic finite D with λ≥1. |
| `sell_iff`, `buy_iff`, `endowment_effect`, `keep_isPE_iff`, `sell_isPE_iff`, `two_PE_example` | ReferenceDependence | KR (2006) §V; Kahneman–Knetsch–Thaler | faithful | Checked by hand: WTA = v(1+ηλ)/(1+η) and WTP = v(1+η)/(1+ηλ). |
| `SubjectiveProblem`, `K`, `IsBerkNash` | BerkNash | Esponda–Pouzo (2016) Def 1 | faithful with documented deviation | Single agent, no private state or signal, finite Θ, full-support Qθ (so K is finite and continuous). |
| `isBerkNash_of_correct`, `optimal_of_isBerkNash` | BerkNash | EP (2016) Prop 1 | faithful with documented deviation | `Identified` is EP's *strong* identification (all x, not only those played). |
| `misspecified_example` | BerkNash | EP-style example | faithful | Checked: K is minimised at θ=1 (0.45 closer to 0.5); subjEU 0.45 > 0.35; true EU 0.5 < 0.6. |
| Berk–Nash existence (EP 2016 Thm 1) | BerkNash | EP (2016) Thm 1 | **coverage gap (in this file)** | Not in BerkNash.lean. It is `exists_isBerkNash` in BoundedRationality/Existence.lean, for finite Θ only. |
| `fs`, `fs2`, `fs_two` | SocialPreferences | Fehr–Schmidt (1999) eq. (1) | faithful | `card−1` is cast to ℝ (no ℕ truncation). For n=1, α/0 = 0 junk is harmless because the sums are 0. FS's β≤α and 0≤β<1 are not built in; theorems add what they need. |
| `accepts_iff`, `ultimatum_offer_unique`, `ultimatum_offer_half(_unique)` | SocialPreferences | FS (1999) Prop 1 | faithful | Checked: threshold α/(1+2α); βP<½ ⇒ offer threshold, βP>½ ⇒ offer ½. Complete information. |
| `dictator_selfish`, `dictator_half` | SocialPreferences | FS (1999) dictator discussion | faithful | |
| `publicGood_freeRide` | SocialPreferences | FS (1999) Prop 4(a) | faithful | Statement is stronger than "contribute 0 is dominant": every marginal increase strictly lowers utility when a+β<1. Verified. |
| `relShare`, `erc`, ERC lemmas | SocialPreferences | Bolton–Ockenfels (2000) | faithful | σ = 1/n when total payoff is 0, as in BO. |
| `payoffs`, `competitive_offer`, `loser_outbids`, `competitive_no_outbid` | MarketInequity | FS (1999) Prop 2 (proposer competition) | faithful with documented deviation | n=3 (2 proposers) only. Only the losing proposer's deviation is checked. The equilibrium is not defined as a game. |
| `sigma`, `sigma_ordering`, `sigma_dimSens` | Salience | Bordalo–Gennaioli–Shleifer (2012) eq. (2), Def 1 | faithful | Ordering and diminishing sensitivity, for nonnegative payoffs. |
| `rank`, `factor`, `weight`, `value`, `Prefers`, `prefers_iff_value` | Salience | BGS (2012) | faithful with documented deviation | Ties share the better rank (BGS assume no ties). Linear v. |
| `win_more_salient_iff`, `longShot_iff`, `longShot_small_p`, `longShot_large_G` | Salience | BGS (2012) Prop 1 (long-shot risk seeking) | faithful | Condition 2p²G < θ(1−2p) checked by hand. Also holds for δ≤0, which is harmless generality. |
| (coverage) Allais / common ratio / preference reversals | Salience | BGS (2012) Props 2–4 | gap | Not stated. |
| `BeliefRule.Linear`, `forecast` | BeliefRule | Gabaix (2020); BGS (2018) | faithful | |
| `FE`, `FR`, `cgCoeff`, `cov_FR_FR`, `cgCoeff_neg_iff`, `cgCoeff_cognitive_pos` | DiagnosticExpectations | Bordalo–Gennaioli–Ma–Shleifer (2020) | faithful | Coefficient −θ(1+θ)/((1+θ)²+θ²ρ²) matches. No x/0: the denominator is >0 under the stated hypotheses. v (variance of x_{t−2}) is free but drops out. |
| `fe_orthogonal_iff` | DiagnosticExpectations | rational-expectations orthogonality | faithful | Still correct when v = 0. |
| `priceIRF`, `price_overreaction`, `price_reversal`, `price_change_lt` | DiagnosticExpectations | BGLS-style asset pricing | faithful | `tsum` junk is avoided: `hasSum_priceIRF` gives HasSum under \|δρ\|<1. |
| `Model`, `IsEquilibrium`, `Determinate`, `index`, `determinate_iff` | CognitiveDiscounting | Gabaix (2020) Prop (determinacy) | faithful | With σ = inverse IES, index = κ(φπ−1)+(1−βM^f)φx+σ(1−M)(1−βM^f) is Gabaix's condition. The Determinate definition is not vacuous (the example checks a determinate peg). |
| `peg_determinate_iff`, `peg_indeterminate_rational`, `determinate_robust`, `isEquilibrium_rational` | CognitiveDiscounting | Gabaix (2020) | faithful | |
| `fg_response`, `fg_puzzle_rational`, `fg_vanishes` | CognitiveDiscounting | Gabaix (2020) forward-guidance puzzle | faithful with documented deviation | IS curve only, with an exogenous real-rate cut. Gabaix's FG result also runs through the Phillips curve. |
| `Gym`, `fee`, `profit`, `welfare`, `pOpt` | ContractDesign | DellaVigna–Malmendier (2004) Prop 1 (uniform cost) | faithful | Recomputed the FOC: p* = a − (1−β)δb, independent of β̂, under uniform F. This matches DM's formula with f(·)/f(·) = 1. The Region hypotheses are satisfiable (sanity test 6). |
| `pOpt_lt_cost`, `profit_lt_of_naive`, `welfare_lt`, `welfare_soph` | ContractDesign | DM (2004) | faithful | |
| `Market`, `pStar`, `profitShrouded`, `profitUnshrouded` | ShroudedAttributes | Gabaix–Laibson (2006) | faithful with documented deviation | A deviating firm captures *all* consumers in a tie, which is stronger than equal splitting, so the no-deviation results are conservative. The shrouded equilibrium itself is not defined. |
| `shrouded_no_deviation`, `curse_of_debiasing`, `profitUnshrouded_nonpos`, `unshroud_profitable` | ShroudedAttributes | GL (2006) Props 1–2 (curse of debiasing) | faithful | Verified case by case: the condition e−c_A < α(v_A−c_A) is exactly the right one. |
| `eu`, `ChoosesA`, `ChoosesD`, `vS`, `narrow_choices_exist` | NarrowBracketing | Tversky–Kahneman (1981) | faithful | A specific kinked prospect-theory v rationalises A and D, which is dominated. |
| `segregate_gains`, `integrate_losses`, `integrate_mixed` | NarrowBracketing | Thaler (1985) hedonic editing | faithful | Checked convexity/concavity arguments. |
| (coverage) Rabin–Weizsäcker (2009) Thm 1 | NarrowBracketing | RW (2009) Econometrica | **coverage gap / WEAK** | The general theorem (narrow bracketing ⇒ dominated choices for broad classes of v) is absent. Only an existence example is formalised. |
| `rational_not_optimal`, `exists_better_belief`, `example_optimism` | MotivatedBeliefs | Brunnermeier–Parker (2005) Prop 1 | faithful with documented deviation | Reduced form: the realised-utility term R is assumed to peak at the true q. In BP this follows from optimal action choice. |
| `mse`, `weight`, `overprecision`, … | Overconfidence | normal–normal updating (no single canonical theorem) | faithful | |

## Non-faithful items

### 1. `RationalInattention.optimal_is_softmax_of_uniform` (WEAK: uniform marginals are assumed)

The hypothesis `hunif : ∀ i, marginal g p i = c` asserts the conclusion's key step. Matějka–McKay obtain the plain logit from *a priori homogeneous* options (a prior invariant under permutations of actions), and then derive that the unconditional choice probabilities are uniform. No file states that derivation. Given `optimal_is_generalizedLogit`, the theorem is a one-line corollary: with a constant P_i, the generalized logit equals softmax.

Example where the theorem is silent: a single state, v = (1,0), λ = 1. Mutual information is identically 0, so the optimal rule is the point mass (1,0). Its marginal is not uniform, and softmax(v) = (e/(1+e), 1/(1+e)) is not optimal. This is sanity test 1(a). The missing canonical statement is sanity test 1(b).

The hypotheses are not vacuous: with v ≡ 0, the uniform rule is optimal and has uniform marginals (sanity test 1(c)).

### 2. `ReferenceDependence.exists_ppe` (WEAK: PE existence is a hypothesis)

`exists_ppe (hD : D.Finite) (hPE : ∃ F, IsPE …)` only selects the best element of a nonempty finite PE set. For an unrestricted μ the hypothesis cannot be dropped. Take D = {0,1,2} (one good, m = id) and μ(x) = 3 if x = −2, else 0:
- u(1|0) = 1 > 0 = u(0|0)
- u(2|1) = 2 > 1
- u(0|2) = 0 + μ(−2) = 3 > 2

So no PE exists (sanity test 2). The pure-lottery version is the same, via `U_pure`.

Mitigation already in the file: existence **is derived** by
- `exists_pe` and `exists_ppe_of_convex` (convex compact D, via a fixed point);
- `exists_ppe_allLotteries`;
- `exists_ppeDet` (deterministic finite D with KR's linear loss-averse μ, η≥0, λ≥1).

So the headline answer is: existence is derived wherever KR derive it. Only the general finite-D wrapper still assumes it. That wrapper should be renamed, or its docstring should say so.

### 3. Berk–Nash existence (coverage gap in BerkNash.lean; documented deviations)

BerkNash.lean has no existence theorem. Esponda–Pouzo (2016) Thm 1 appears as `SubjectiveProblem.exists_isBerkNash` in BoundedRationality/Existence.lean, with `[Nonempty X] [Nonempty Θ]`. That theorem is stated only for **finite Θ** with full-support Qθ, whereas EP allow compact Θ under continuity assumptions. It is also single-agent with no state or signal.

`Identified` requires Qθ = Q at *every* x. That is EP's strong identification. `optimal_of_isBerkNash` is therefore EP Prop 1 under the stronger hypothesis. It is correct, but weaker than EP's version stated with weak identification plus belief-robustness.

### 4. NarrowBracketing (coverage gap for Rabin–Weizsäcker)

The file proves only the TK (1981) example: there exists a v with A and D chosen and A∧D dominated. Rabin–Weizsäcker's main theorem (for any v outside a narrow class, e.g. not CARA-like, some pair of independent decisions makes the narrow bracketer choose an FOSD-dominated combination) is not stated. The headline "narrow bracketing (Rabin–Weizsäcker)" is not covered.

### 5. Salience (coverage gap)

Only the long-shot proposition is formalised. BGS (2012)'s Allais common-consequence and common-ratio results and their preference-reversal results are absent. Tie handling in `rank` (ties share the better rank) is a benign extension.

### 6. MarketInequity, ShroudedAttributes, CognitiveDiscounting FG (documented deviations)

- **MarketInequity:** `competitive_offer` shows that s=1 is forced when the *losing* proposer has no profitable outbid. There is no game, no responder-rejection stage, and only n=3 is covered. FS Prop 2 is for general n.
- **ShroudedAttributes:** firm deviations are checked against the candidate prices. The equilibrium notion and its existence and uniqueness are not stated. Tie-breaking gives the deviator the whole market, which is conservative.
- **CognitiveDiscounting:** the forward-guidance results use the IS curve only (`IsISPath`), with no Phillips-curve feedback, so the theorem is weaker than Gabaix's full-model statement. The determinacy results use the full model and are faithful.

### 7. MotivatedBeliefs (reduced form)

`rational_not_optimal` takes "R is maximised at q" as a hypothesis. In Brunnermeier–Parker this is the derived statement that realised expected utility is maximised by acting on true beliefs. The theorem is a correct first-order argument, but it is abstract. No action, payoff or anticipation structure is modelled.

## Things specifically checked and found OK

- **Junk values:**
  - Real.log 0 = 0 in `kl`, `mutualInfo` and Berk–Nash `K` (the reference measure dominates, or Qθ>0).
  - α/(card−1) when n=1.
  - `tsum` in `priceIRF`: HasSum is proved under |δρ|<1.
  - x/0 in `cgCoeff`: the denominator is positive under the stated hypotheses.
  - Luce with positive weights.
  - `relShare` with total 0.
  - `IsRule` with ι empty makes `IsOptimalRule` false, so the RI theorems are vacuous only in that degenerate case. `exists_isOptimalRule` carries `[Nonempty ι]`.
- **Satisfiability:**
  - ContractDesign Region: β=½, β̂=⅘, δ=b=1, a=½ gives p*=0, thr=½, thr̂=⅘.
  - Cognitive NK determinate peg (the in-file example).
  - Berk–Nash misspecified example.
  - KR two-PE example.
- **Algebra re-derived by hand:** FS acceptance threshold; KR WTA/WTP; BGS long-shot salience condition; BGMS CG coefficient; DM optimal price; GL curse-of-debiasing inequality; Gabaix determinacy index (after converting σ between IES and inverse IES).
