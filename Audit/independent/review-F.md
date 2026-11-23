# Statement review: Behavioral, Bounded Rationality and Macro targets (reviewer F)

Scope: the 19 TARGET files under `/home/user/rv/in/EconLean/`. I read only the statement files and the one dependency needed for definitions (`Behavioral/Logit.lean` and `Behavioral/RationalInattention.lean` for `IsProb` and `kl`). I checked every headline theorem by hand against the canonical statement, and worked through each worked-example theorem numerically (ODR report and movie dates, Berk–Nash example, KR mug, DD `c1star`).

**Overall:** the algebraic and economic content is mostly sound. I found **no theorem I believe is false**. The main problems are:
- **Missing headlines.** Three canonical existence or general results named in the brief are not actually stated: McKelvey–Palfrey QRE existence for general finite games, Esponda–Pouzo Berk–Nash existence, and general Hulten.
- **Theorems that assume the hard step.** KR PPE existence takes PE existence as a hypothesis.
- **Over-permissive feasibility and equilibrium notions** in discrete-time DMP.
- **Results reduced to special cases.** HK covers only the qualitative half. GP covers only one direction. Samuelson covers only stationary money. Continuous-time Hosios covers only r = 0.

## Summary table

| Declaration | File | Reference | Verdict | One-line reason |
|---|---|---|---|---|
| `discount`, `presentValue` | PresentBias | Laibson 1997; ODR 1999 | faithful with documented deviation | ℕ-subtraction makes a past date (s < t) count as "now" (weight 1); never used with s < t in theorems |
| `exponential_timeConsistent` | PresentBias | Strotz 1956 | faithful | correct |
| `exists_preferenceReversal_iff`, `not_preferenceReversal_of_beta_one` | PresentBias | Laibson 1997 | faithful | both directions; I checked β>1 also yields no reversal |
| `Task`, `U`, `NaiveDoes`, `sophFrom`, `naiveDate`, `sophDate`, `tcDate` | PresentBias | O'Donoghue–Rabin 1999 AER §II | faithful | correct payoff timing for immediate costs/rewards; tie → do now (ODR convention); `tcDate` = first argmax of w |
| `soph_le_naive` | PresentBias | ODR 1999 Prop. 2 | faithful | holds for all β (proof does not need β≤1), so generality is harmless |
| `tc_le_naive_of_immediateCosts`, `naive_le_tc_of_immediateRewards` | PresentBias | ODR 1999 Prop. 1 | faithful | I checked the side conditions (c≥0 / v≥0, β∈(0,1]) and they suffice |
| `report_dates`, `movie_dates` | PresentBias | ODR 1999 examples | faithful | I recomputed: report (1,2,4), movie (4,1,3) |
| `Lottery`, `G`, `F`, `FOSD`, `eu`, `fosd_iff_eu` | RankDependent | MWG Prop 6.D.1 | faithful | on a common finite ordered grid; both directions |
| `rdu`, `decisionWeight`, `rdu_mono`, `rdu_strictMono` | RankDependent | Quiggin 1982; Wakker 2010 Ch.7 | faithful | decumulative weighting; FOSD monotonicity weak and strict |
| `opt_violates_fosd` | RankDependent | Kahneman–Tversky 1979; Fishburn 1978 | faithful | I built a construction (a at 1, b at 2 vs a+b at 3) that witnesses it |
| `cpt`, `cpt_mono`, `cpt_id`, `cpt_zero_eq_rdu`, `cpt_statusQuo` | RankDependent | Tversky–Kahneman 1992 | faithful | standard layer form; `cpt` is invariant to the level of v r, so `hvr` in `cpt_id` is genuinely needed |
| `cpt_rejects_fair_coin`, `tkValue_lossAverse`, `tk_rejects_fair_coin` | RankDependent | TK 1992 | faithful with documented deviation | `tkValue` at x=0 is `0^α`, i.e. 1 if α=0 (rpow junk); theorems require α>0 or don't hit 0 |
| `consumptionUtility`, `gainLoss`, `u`, `U`, `IsPE`, `IsPPE`, `IsCPE` | ReferenceDependence | Kőszegi–Rabin 2006 QJE, 2007 AER | WEAK | stochastic `D : Set (ι → ℝ)` is not restricted to probability vectors |
| `exists_ppe` | ReferenceDependence | KR 2006 (PE/PPE existence) | WEAK | **assumes** `∃ F, IsPE …`; the remaining content is "a finite set has a max" |
| `exists_cpe` | ReferenceDependence | KR 2007 | faithful (finite case) | trivial max over finite D |
| `isPEDet_of_isMax`, `exists_ppeDet` | ReferenceDependence | KR 2006 | faithful | linear μ, λ≥1, deterministic finite D; existence genuinely proved |
| `two_PE_example`, `sell_iff`, `buy_iff`, `endowment_effect`, `keep_isPE_iff`, `sell_isPE_iff` | ReferenceDependence | KR 2006 §IV; Tversky–Kahneman 1991 | faithful with documented deviation | `sell_iff`/`buy_iff`/`endowment_effect` use a status-quo reference (TK 1991); the PE versions use expectations (KR). I recomputed the WTA/WTP formulas |
| `W`, `setBetweenness`, `commitment_strict`, `W_pair_succumb` | Temptation | Gul–Pesendorfer 2001 Thm 1 | WEAK (coverage) | only representation ⇒ set betweenness; the representation theorem (axioms ⇒ u,v) is absent; menus are finite sets of abstract X, not lotteries |
| `SubjectiveProblem`, `K`, `IsBerkNash` | BerkNash | Esponda–Pouzo 2016 Def. 1 | faithful | single-agent, finite, Qθ>0 |
| `isBerkNash_of_correct`, `optimal_of_isBerkNash` | BerkNash | EP 2016 Prop. 1 (strong identification) | faithful | `Identified` = strong identification under correct specification |
| Berk–Nash existence (EP 2016 Thm 1) | BerkNash | EP 2016 Thm 1 | **MISMATCH / coverage gap** | **not stated anywhere** although it is a listed headline |
| `misspecified_example` | BerkNash | EP-style example | faithful | I verified: θ=0.45 minimizes KL, x=0 subjectively optimal, x=1 truly better |
| `FiniteGame`, `IsLevelKPath`, `isPureNash_of_levelK_fixed`, `levelK_eq_of_strictNash` | LevelK | Nagel 1995; Stahl–Wilson; Crawford et al. 2013 | faithful with documented deviation | level-0 is a pure profile, not uniform randomization |
| `levelKGuess`, `levelK_guess_tendsto`, `chGuess`, `chGuess_strictAnti` | LevelK | Nagel 1995; Camerer–Ho–Chong 2004 | faithful with documented deviation | beauty contest is an ad hoc recursion (no game, own-guess effect ignored); CH weights are any positive f, not Poisson |
| `U`, `logitResponse`, `IsLogitQRE`, `IsMixedNash` | QRE | McKelvey–Palfrey 1995 | faithful | |
| `isNash_of_tendsto_qre` | QRE | MP 1995 Thm 2 | faithful | limit points as λ→∞ are Nash |
| QRE existence for general finite games | QRE | MP 1995 Thm 1 | **MISMATCH / coverage gap** | only `exists_isLogitQRE_2x2` and λ=0 are stated; no general existence |
| `qre2x2_exists`, `exists_isLogitQRE_2x2` | QRE | MP 1995 (2×2 special case) | faithful | holds for all λ including negative |
| `flow`, `steadyState_unemployment`, `tendsto_unemployment` | DMP | Pissarides 2000 Ch.1 | faithful | discrete-time flow map, 0<s+f<2 |
| `Economy`, `findRate`, `fillRate`, `jc`, `jc_iff_textbook`, `existsUnique_equilibrium`, `equilibrium_strictAnti_β`, `beveridge` | DMP | Pissarides 2000 (1.22)–(1.24) | faithful | `fillRate 0 = 0` (rpow junk) but all uses need θ>0 |
| `welfare`, `IsEfficient`, `isEfficient_iff`, `hosios` | DMP | Hosios 1990; Pissarides 2000 Ch.8 | faithful with documented deviation | planner maximizes steady-state net output, so the result is only for r = 0; the discounted case is in HosiosDiscounted |
| `Discrete`, `IsSearchEqm`, `isSearchEqm_iff`, `existsUnique_searchEqm` | HosiosDiscounted | discrete-time DMP (LS Ch.28) | WEAK | the equilibrium does not require f(θ)≤1 or q(θ)≤1; "equilibria" with job-finding probability ≫1 are admitted |
| `Feasible`, `welfare`, `IsOptimal`, `hosios` (discrete) | HosiosDiscounted | Hosios 1990 | WEAK | feasibility omits q(θ)≤1 (matches ≤ vacancies); in substance the iff is right, and the `tsum` is guarded by `summable_welfare` |
| `OfferDist`, `T`, `IsReservationWage`, `isReservationWage_iff_textbook`, `existsUnique_reservationWage` | McCall | LS 4th ed. §6.3, eq. (6.3.3) | faithful | |
| `bellman_*`, `accept_iff`, `reservationWage_strictMono_c` | McCall | LS §6.3 | faithful | |
| `Riskier`, `reservationWage_mono_riskier`, `mps_example` | McCall | LS §6.3.3; Rothschild–Stiglitz 1970 | faithful | convex order = MPS; weak inequality as in LS |
| `logU_le_opt`, `logU_lt_opt`, `IsOptimalSaving`, `saving_isOptimal_iff` | LogHousehold | standard | faithful | positivity guards avoid `log` junk |
| `Diamond`, `IsEquilibrium`, `existsUnique_equilibrium`, `tendsto_equilibrium`, `rate_steadyState` | Diamond | Acemoglu Ch.9 §9.2–9.3 (log, CD, δ=1) | faithful with documented deviation | log utility, Cobb–Douglas, full depreciation only |
| `dynamicallyInefficient_iff`, `exists_dominating_path`, `no_dominating_path`, `dynamicallyInefficient_iff_exists_improvement` | Diamond | Acemoglu Prop 9.? / Cass 1972 | faithful | both directions. I checked that `no_dominating_path` really holds: g is concave, g'(k*)≥1, c*>0 |
| `Samuelson`, `IsFeasible`, `ParetoDominates`, `IsCompetitiveEquilibrium`, `firstWelfareTheorem_fails`, `golden_dominates_autarky` | Samuelson | Samuelson 1958; LS Ch.9 | faithful | market clearing a=0 is imposed explicitly (correct for one cohort of savers) |
| `IsMonetaryEquilibrium`, `isMonetaryEquilibrium_iff`, `monetaryEquilibrium_eq_golden_and_dominates` | Samuelson | LS Ch.9; Wallace 1980 | faithful with documented deviation | only stationary monetary equilibria; the non-stationary continuum converging to autarky is not covered |
| `NeoclassicalProduction`, `of_deriv` | Solow | Acemoglu Assm 1–2 | faithful with documented deviation | Inada conditions on the average product f(k)/k (weaker, implied by the derivative versions via `of_deriv`) |
| `existsUnique_steadyState`, `tendsto_path`, `exists_globally_stable_steadyState`, comparative statics | Solow | Acemoglu Prop 2.2–2.5 | faithful | discrete time, δ∈[0,1] |
| `cobbDouglas_steadyState`, `cobbDouglas_tendsto` | Solow | Acemoglu Ex. 2.? | faithful | |
| `goldenRule_*`, `consumption_le_goldenRule`, `consumption_lt_goldenRule`, `goldenSavingRate_mem`, `cobbDouglas_goldenSavingRate` | GoldenRule | Acemoglu Prop 2.? | faithful with documented deviation | existence of k_gold (f'(k_g)=n+δ) is a hypothesis for general f; it is proved for Cobb–Douglas (s_g = α) |
| `TechEconomy`, `effective_eq_path`, `tendsto_effective`, `tendsto_detrended_output`, `balanced_growth` | TechProgress | Acemoglu §2.7 | faithful | the BGP is stated only from k₀=k*; the asymptotic growth rate → g is implied but not stated; Uzawa is absent |
| `Horizontal.*`, `hulten_planner`, `hulten` | Hulten | Hulten 1978; Baqaee–Farhi 2019 | WEAK (coverage) | only a "horizontal" CD economy with Domar weights = a_i |
| `Vertical.*`, `domar`, `hulten` | Hulten | Hulten 1978 | WEAK (coverage) | a single 2-stage CD example; the general theorem (efficient CRS network: ∂log Y/∂log A_i = sales_i/GDP) is not stated |
| `Industry`, `tfp`, `tfpEfficient`, `tfp_le_efficient`, `tfp_eq_efficient_iff`, `tfpr_equal_iff`, `wedgeAlloc_efficient_iff` | Misallocation | Hsieh–Klenow 2009 eqs (16)–(17) | WEAK (coverage) | qualitative half only; single input (no K/L wedges); the HK TFP-loss formula (log TFP = … − σ/2·Var log TFPR under joint log-normality) is absent |
| `crra`, `crra_optimum` | DiamondDybvig | DD 1983 §II | faithful | `crra 1 c = 0` junk (÷0) but all uses require γ>1 or γ≠1 |
| `Bank`, `latePay`, `WaitIsBest`, `RunIsBest`, `goodEquilibrium_iff`, `runEquilibrium_iff`, `multiple_equilibria` | DiamondDybvig | DD 1983 Thm 1–2 | faithful with documented deviation | r₁=1 is excluded from the run equilibrium (`latePay 1 = R·0/0 = 0` junk is guarded); bank failure ignores sequential-service lotteries |
| `suspension_waiting_strictly_better` | DiamondDybvig | DD 1983 §IV | WEAK | a payoff inequality only; "suspension eliminates the run equilibrium / implements the optimum" is not stated |

## Details on non-faithful items

### 1. QRE: McKelvey–Palfrey general existence is missing (MISMATCH / coverage gap)
MP (1995, Thm 1): for every finite normal-form game and every λ ≥ 0 a logit QRE exists. This is a direct Brouwer application on the product of simplices.

`QRE.lean` proves existence only for `game2x2` (`exists_isLogitQRE_2x2`) and for λ = 0 (`uniform_isLogitQRE_zero`). Nothing like `∀ (G : FiniteGame I) [Fintype I] lam, ∃ σ, IsLogitQRE G lam σ` is stated. That missing statement is in `sanity_tests.lean`.

`isNash_of_tendsto_qre` is correct, but it is vacuous for a game where no QRE sequence is known to exist. It is non-vacuous only for 2×2 games.

### 2. Berk–Nash: Esponda–Pouzo existence is missing (MISMATCH / coverage gap)
EP (2016, Thm 1) says a Berk–Nash equilibrium exists in every regular SMDP or game. The file states:
- the definition;
- the "correctly specified ⇒ Nash is BN" direction;
- the "correct + strongly identified ⇒ BN is optimal" direction;
- one example.

The headline existence result is not stated. Proving it needs Kakutani on the joint (σ, μ) correspondence with upper hemicontinuity of the KL-minimizer set, which is non-trivial. The intended statement is in `sanity_tests.lean`.

### 3. Kőszegi–Rabin `exists_ppe` assumes PE existence (WEAK)
```
theorem exists_ppe … (hD : D.Finite) (hPE : ∃ F, IsPE bundle μ m D F) : ∃ F, IsPPE …
```
With `hPE` assumed, the proof is "pick a U(F|F)-maximizer among the finitely many PEs". The economically hard step, existence of a PE, is assumed. A PE need not exist for general μ, for example a gain-seeking μ with λ<1; on why existence is subtle see KR 2006 and the recent "On the existence of personal equilibria" (arXiv 2512.08348). The deterministic linear-μ case (`exists_ppeDet`) does prove existence, but the stochastic version has no analogue.

A related definition issue: `D : Set (ι → ℝ)` is never required to consist of probability vectors, so `IsPE` and `IsCPE` apply to arbitrary real weight vectors. For example, `D = {fun _ => 5}` makes U a 25× scaled double sum. This does not falsify any theorem, but the definitions are not the KR objects. Fix: add `∀ F ∈ D, IsProb F`.

A stochastic analogue of `exists_ppeDet` holds, and I suggest stating it in its place: for μ = μLin η λ with η≥0, λ≥1, and D finite and nonempty with probability vectors, the E[m]-maximizer is a PE. The argument is the same: U(F'|F) ≤ E_{F'}m + η(E_{F'}m − E_F m).

### 4. Discrete Hosios: equilibrium and feasibility admit probabilities above 1 (WEAK)
`IsSearchEqm` has no constraint `D.findRate θ ≤ 1` or `D.fillRate θ ≤ 1`, so `existsUnique_searchEqm` counts as an equilibrium a θ with job-finding probability far above 1.

Example: A = 10, η = 1/2, s = 1/10, c = 1, y−b = 1, δ = 9/10 (rate = 1/9), β = 1/2. The JC equation 0.0211·√θ + 0.5θ = 0.5 gives θ ≈ 0.98, so f(θ) ≈ 9.9. The unemployed Bellman equation `U = b + δ(fE + (1−f)U)` then puts negative weight on U.

`Feasible` likewise omits q(θ) ≤ 1, i.e. matches ≤ vacancies. For the in-file example economy (A = 1/4, η = 1/2), θ = 1/100 is "feasible" with q = 2.5.

The `hosios` iff is still correct, because both sides use the same relaxed `IsOptimal` and θp needs `hfp`. But the welfare benchmark optimizes over a set larger than the economically feasible one, and the conclusion "θp is optimal" does not certify q(θp) ≤ 1. Fix: add `fillRate θ ≤ 1` to `Feasible` and both bounds to `IsSearchEqm`, or use a bounded matching function.

### 5. Continuous-time DMP Hosios only at r = 0 (documented deviation)
`IsEfficient` maximizes the steady-state net-output function `welfare`, and `hosios` is stated for `IsEquilibrium 0 β θ`. Pissarides Ch.8 shows the efficient θ equals the β = η equilibrium for any r>0 using a dynamic planner, but the static steady-state objective is the wrong planner problem when r > 0. This is acceptable because HosiosDiscounted covers discounting, but the continuous-time file's `hosios` must not be cited as the general Hosios theorem.

### 6. Hulten: only two closed-form examples (WEAK, coverage)
`Horizontal` is the CD economy y_i = A_i l_i, Y = ∏ y_i^{a_i}. Its Domar weights equal a_i and sum to 1, so it cannot distinguish Hulten from value-added weighting.

`Vertical` is a single two-stage example showing Domar weights sum to 1+ω > 1. Both proofs go through explicit formulas for `maxOutput`; the envelope argument is never used.

Hulten's theorem as stated in the literature is: for any efficient competitive economy with CRS technologies and arbitrary input–output network, d log Y / d log A_i = p_i y_i / GDP. That statement does not appear. Calling the file "Hulten's theorem" overstates it.

### 7. Hsieh–Klenow: no TFP-loss formula; single input (WEAK, coverage)
The file proves three qualitative results:
- TFP ≤ efficient TFP;
- equality iff TFPR is equalized;
- equality iff the output wedges are equal.

These are correct. The model is a one-input simplification (labor only, no capital wedge τ_K).

HK's quantitative result is absent: eq. (16) TFP = (Σ (A_i · TFPR̄/TFPR_i)^{σ−1})^{1/(σ−1)}, and under joint log-normality log TFP = log TFP_eff − (σ/2)·Var(log TFPR). The "TFP loss" headline is therefore not covered.

`tfpr` is revenue per input up to a constant (p_i y_i ∝ y_i^ρ). It uses x/0 = 0 when s_i = 0, but every theorem using it requires s_i > 0, so this is harmless.

### 8. Gul–Pesendorfer: only one direction (WEAK, coverage)
`setBetweenness` shows that the representation W(A) = max(u+v) − max v satisfies set betweenness. GP 2001 Thm 1 is the representation theorem: a preference over menus of lotteries satisfying weak order, continuity, independence and set betweenness has such a representation with linear u, v. That theorem is absent, and X is an abstract finite type rather than lotteries, so independence and linearity never appear. The missing converse is in `sanity_tests.lean` as a comment.

### 9. Diamond–Dybvig details (faithful with documented deviation / WEAK)
- `runEquilibrium_iff : RunEquilibrium ↔ 1 < r₁`. This matches DD's claim that runs exist for r₁ > 1. At r₁ = 1 the definitions declare no run equilibrium. At f = 1, `latePay 1 = R·0/0 = 0` by junk division, but the definition guards it with `f < 1`, so the junk value is never used.
- When the bank fails (f r₁ > 1), withdrawing is declared best without modeling the sequential-service lottery. That is fine qualitatively.
- `suspension_waiting_strictly_better` is a payoff inequality. It does not state that the run is not an equilibrium of the suspension game, nor that suspension implements (c₁*, c₂*).

### 10. Samuelson OLG: only stationary money (documented deviation)
`IsMonetaryEquilibrium M p` has a constant price, so return R = 1. The canonical analysis (LS Ch.9) also has a continuum of non-stationary monetary equilibria with inflation converging to autarky. These are not modeled. Within its scope the file is correct, including the claims that the monetary steady state equals the golden allocation and that it dominates autarky iff ω₂ < βω₁.

### 11. Minor junk-value notes (no theorem affected)
- `PresentBias.presentValue β δ t a s` with s < t truncates `s - t` to 0 and returns weight 1 (a past reward counts as immediate).
- `DMP.Economy.fillRate 0 = 0`, because Mathlib defines `0 ^ x = 0` for x ≠ 0, whereas the economic value is +∞.
- `DiamondDybvig.crra 1 c = 0`: the formula divides by zero instead of giving log c.
- `RankDependent.tkValue 0 …` at x=0 equals `0^0 = 1`.

Every theorem guards against these cases.

## Coverage gaps (canonical results implied by the names but not stated)
- QRE: MP Thm 1 general existence; the principal branch / homotopy result (MP Thm 3).
- BerkNash: EP Thm 1 existence; EP Thm 2 (learning foundation).
- ReferenceDependence: unconditional PE existence (stochastic, linear μ); KR's choice-acclimating PE.
- Temptation: GP representation theorem; self-control vs. no-self-control characterization.
- Hulten: the general network theorem.
- Misallocation: the HK TFP-gap formula and the log-normal variance formula; capital/labor wedges.
- TechProgress: Uzawa's theorem; asymptotic growth rate of output per worker → g.
- Samuelson: non-stationary monetary equilibria.
- LevelK: no actual beauty-contest `FiniteGame` linking `levelKGuess` to `IsLevelKPath`.

Sources: [KR 2006 (refdep.pdf)](https://www.wiwi.uni-bonn.de/koszegi/refdep.pdf), [On the existence of personal equilibria (arXiv 2512.08348)](https://arxiv.org/pdf/2512.08348), [Sarver notes on expectations-based reference points](https://sites.duke.edu/toddsarver/files/2024/01/4-Expectations-Based-Ref-Points.pdf)
