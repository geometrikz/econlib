# Statement review: Mechanism/* and Matching/*

Scope: `EconLean/Mechanism/{Revelation,VCG,Myerson,OptimalMechanism,FirstPrice,BilateralTrade,MyersonSatterthwaite}.lean` and `EconLean/Matching/{GaleShapley,StrategyProof,Assortative}.lean`. I only looked at the statement files (proofs are `sorry`). Lean was not run, so the semantics below come from reading the code.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `IsDominantEq`, `IsDSIC` | Revelation | MWG Def 23.B.5/23.C.3; Börgers 5.2 | faithful | Quantifies over all message profiles of the others; the deviation is in i's own report. |
| `revelation_dominant` | Revelation | MWG Prop 23.C.1 | faithful | Composition of a dominant equilibrium with `g` is DSIC. |
| `IsBIC`, `revelation_bayesian` | Revelation | MWG Prop 23.D.1 | faithful with documented deviation | Finite type spaces only. `IsBNE` is ex ante Nash with `p ∈ lotteries` (so it equals interim optimality on positive-probability types). `IsBIC` uses the unnormalised conditional, which is equivalent. |
| `IsEfficientRule`, `grovesTransfer`, `groves_truthful` | VCG | MWG Prop 23.C.4 (Groves) | faithful | General types and outcomes. `h_i` is independent of i's own report. |
| `othersMax`, `clarkeTransfer`, `clarke_truthful` | VCG | MWG 23.C (Clarke pivot) | faithful | Needs `Fintype X` and `Nonempty X`. |
| `clarke_transfer_nonpos`, `clarke_individuallyRational` | VCG | Nisan et al. AGT 9.3.3 | faithful | IR needs `v ≥ 0`, which is the standard "no negative valuations" condition. |
| (coverage) Green–Laffont / Holmström uniqueness of Groves | VCG | MWG Prop 23.C.5 | gap | Never stated. "VCG efficiency" holds only because efficiency is assumed through `hk`. |
| `IsICMech`, `myerson_ic_iff` | Myerson | Myerson 1981 Lemma 2; Börgers Prop 2.2; Krishna 5.1 | faithful | Proves both directions. A monotone `q` is integrable, so the `∫` carries no junk value. Single agent, reduced form. |
| `revenue_equivalence` | Myerson | Krishna Prop 3.1 / 5.2 | faithful with documented deviation | Stated as single-agent pointwise payment equivalence. The multi-bidder auction version (same allocation rule implies same expected revenue) is not stated. |
| `expected_revenue_eq` | Myerson | Krishna Prop 3.1 | WEAK | The type distribution `F : SimpleLottery` has **finite support**. The textbook case of continuous F (e.g. uniform) is not covered. It is a trivial corollary of the pointwise result. |
| `virtualWeight`, `revenue_le_virtual` | OptimalMechanism | Börgers §2.4 (discrete); Myerson 1981 Lemma 3 | faithful | `virtualWeight j = f_j·φ_j` with the discrete virtual value φ_j = θ_j − (θ_{j+1}−θ_j)(1−F_j)/f_j. The bound needs only IC and IR, with no assumption on the order of θ. |
| `postedPrice_optimal`, `postedPrice_isOptimal` | OptimalMechanism | Myerson 1981 Thm; Riley–Zeckhauser 1983; Krishna 5.2 | **WEAK (coverage)** | One buyer with discrete types only. "Regularity" is never defined. The theorem **assumes** a threshold sign pattern of virtual weights, and fails to apply to non-regular distributions, where Riley–Zeckhauser still say a posted price is optimal. The multi-bidder optimal auction is absent: no allocation to the highest nonnegative virtual value, no reserve r = φ⁻¹(0), and no continuous φ(θ) = θ − (1−F)/f. |
| `fpBid`, `fpWinProb`, `firstPrice_equilibrium` | FirstPrice | Krishna Prop 2.2 | WEAK | Only i.i.d. **U[0,1]** values with n = m+1 bidders. It is a best response against symmetric opponents using β(v) = m/(m+1)·v, so the general β(v) = E[Y₁ | Y₁ < v] is missing. It is not connected to `IsBNE`, and uniqueness is not stated. The correct form for the uniform case. |
| `firstPrice_revenue` | FirstPrice | Krishna §2.2 | faithful (uniform case) | (n−1)/(n+1) = m/(m+2). Checked by hand: (m+1)·∫ (m/(m+1)) v·v^m dv = m/(m+2). |
| `TradeMechanism`, `IsEfficient`, `BuyerDSIC`, `SellerDSIC`, `IsBudgetBalanced` | BilateralTrade | Börgers 3.4; Hurwicz / Green–Laffont | faithful | Ex post, on [a,b]². |
| `no_efficient_dsic_budgetBalanced_trade` | BilateralTrade | Green–Laffont 1979; Hurwicz 1972 | faithful | Needs no IR. Checked by hand: DSIC plus efficiency gives Groves form tB = c·1[c<v] + h_B(c) and tS = v·1[c<v] + h_S(v). Exact budget balance then gives a contradiction using four interior points. |
| `QB`,`PB`,`QS`,`RS`,`IsBIC`,`IsInterimIR`,`IsExAnteBudgetBalanced` | MyersonSatterthwaite | MWG 23.E; Krishna 5.3; Börgers 3.3 | faithful with documented deviation | Independent priors; budget balance in its weakest form (ex ante, expected deficit ≤ 0). Junk integrals cannot produce a fake mechanism: IC forces `PB` and `RS` to be the bounded envelope functions on [a,b], and those are integrable. |
| `myerson_satterthwaite` | MyersonSatterthwaite | Myerson–Satterthwaite 1983 Thm 1; MWG Prop 23.E.1 | **faithful with documented deviation (strictly weaker)** | It is the **real impossibility over all** efficient + BIC + interim-IR + ex-ante-weakly-budget-balanced mechanisms (`M` is universally quantified), not a statement about one mechanism. The deviation: buyer and seller must share a single interval [a,b], and efficiency, IC and IR are imposed on all of [a,b]², off-support pairs included. "Overlapping supports" is replaced by `hgain > 0`. For buyer U[1,2] and seller U[0,1] every distributional hypothesis holds, but the textbook theorem's conclusion is false there (a posted price at 1 is efficient, IC, IR and BB on the supports). The formal theorem is only "true" there because it also demands efficiency at off-support pairs such as (v,c) = (1/2,1/4). |
| `myerson_satterthwaite_expost` | MyersonSatterthwaite | same | faithful with documented deviation | Same as above. Needs an extra integrability hypothesis `hint`. |
| `uniform_satisfies_hypotheses` | MyersonSatterthwaite | n/a | faithful | Shows the distributional hypotheses can be met. The mechanism hypotheses are jointly unsatisfiable by design, as the theorem intends. Dropping BB, the pivot mechanism satisfies the rest (see the sanity file). |
| `IsMatching`, `IsBlocking`, `IsStableMatching` | GaleShapley | Roth–Sotomayor Def 2.1–2.3 | faithful with documented deviation | No outside options: everyone finds everyone acceptable, so there is no IR or acceptability condition. Unmatched agents prefer any partner. |
| `exists_stable_matching`, `exists_menOptimal_stable_matching` | GaleShapley | Gale–Shapley 1962; Roth–Sotomayor Thm 2.8, 2.12 | faithful with documented deviation | Strict preferences via injective `ℝ` utilities. Complete lists only. Women-pessimality (Knuth, R–S Cor 2.13) and the lattice structure are not stated. |
| `daMatching_isStable`, `daMatching_menOptimal` | StrategyProof | R–S Thm 2.8, 2.12 | faithful | Shows the DA algorithm actually defined here produces the matching. Iterating `daRounds` is enough. |
| `gs_blocking_lemma` | StrategyProof | Gale–Sotomayor 1985; R–S Lemma 4.8 (Blocking Lemma) | WEAK | Drops the canonical conclusion **w ∈ μ'(M')**, i.e. that the blocking woman is matched under μ' to an improving man. |
| `daMatching_strategyproof` | StrategyProof | Roth 1982; Dubins–Freedman 1981; R–S Thm 4.7 | faithful with documented deviation | Only one man deviates. The coalitional Dubins–Freedman statement (no coalition of men all strictly gain) is missing. Misreports are limited to complete rankings (truncations cannot be expressed). Misreports with ties are allowed, which is harmless. |
| `HasIncreasingDifferences` | Assortative | Becker 1973; Topkis | WEAK | Supermodularity is required on **all of ℝ²** rather than on the type domain. It excludes standard positive-type surpluses. Example: f(x,y) = log x · log y is supermodular on [1,∞)² but fails here because Mathlib has `Real.log (-x) = Real.log x`. Similarly `x^(1/3) * y^(1/3)` with Mathlib's `rpow` on negative bases. |
| `becker_pam` | Assortative | Becker 1973 Thm; Legros–Newman | faithful with documented deviation | Equal-size sides, efficiency (surplus maximisation) only. It does not state that strict supermodularity makes PAM the unique optimum, and it does not state the TU-equilibrium/core version (that the stable matching is PAM). |

## Details of the non-faithful items

### 1. OptimalMechanism: "Myerson optimal auction" is single-buyer discrete monopoly pricing with regularity assumed (WEAK / coverage)
- `postedPrice_optimal` assumes `hlow`/`hhigh`: there is an index m with weights ≤ 0 below m and ≥ 0 from m on. This sign pattern is what regularity is used for, so the key economic step is assumed. Regularity (monotone φ) is never defined, and no lemma shows that it implies the threshold pattern.
- Non-regular counterexample, where the theorem is silent: n = 3, θ = (1,2,3), f = (3/5, 1/10, 3/10). The weights are w = (1/5, −1/10, 9/10), so no m satisfies both hypotheses. The single-buyer optimum is still a posted price (Riley–Zeckhauser; with discrete types, optimising over 0 ≤ q ≤ 1 under IC and IR gives a step function after ironing). Neither the theorem nor any ironing result covers this case. See `sanity_tests.lean`, §OptimalMechanism.
- Missing entirely: multiple bidders, allocating to the bidder with the highest nonnegative virtual value, a reserve price independent of n, and the continuous virtual value θ − (1−F(θ))/f(θ).

### 2. MyersonSatterthwaite: genuine all-mechanism impossibility, but not the textbook one (documented deviation)
- **Good:** `M : TradeMechanism` is universally quantified. Allocation is real-valued, so randomised trade is allowed. BIC is interim with independent priors, IR is interim, and BB is the weakest version: ex ante, with seller receipts ≤ buyer payments. The integrals behave correctly: efficiency plus no atoms make `x v ·` a.e. an indicator. IC forces `PB` and `RS` to be the bounded envelope functions on [a,b], so the junk value `∫ = 0` for non-integrable functions cannot rescue a mechanism.
- **Deviation:** one interval [a,b] serves as the type space for both traders, and `IsEfficient`, `IsBIC` and `IsInterimIR` are required at every point of [a,b] or [a,b]². That includes types and pairs outside the supports. Take buyer U[1,2] and seller U[0,1] with [a,b] = [0,2]. All of `hB, hS, hBna, hSna, hgain` hold. The posted price p = 1 is efficient on supp μB × supp μS, dominant-strategy IC, IR, and ex post BB. So the canonical conclusion fails, which is fine because the canonical theorem needs overlapping interiors. Yet the formal theorem's distributional hypotheses still hold, and its mechanism hypotheses rule out p = 1 only through off-support pairs (e.g. (1/2, 1/4) must trade). The formal result is therefore a different, strictly weaker theorem: it constrains a larger set of types. It coincides with the textbook statement when both distributions have full support [a,b], which is MWG's and Krishna's main case.
- Suggested fix: separate intervals [v̲,v̄] for the buyer and [c̲,c̄] for the seller with v̲ < c̄ (overlap), and efficiency, IC and IR on the supports only.

### 3. FirstPrice: uniform only (WEAK)
Only β(v) = m/(m+1)·v under i.i.d. U[0,1] is stated. The general symmetric equilibrium β(v) = E[max of rivals | max < v] (Krishna Prop 2.2) is absent, as are the link to the library's `IsBNE` and uniqueness. Within the uniform case the statement is correct: a single deviation to any real bid, with ties ignored (they have probability zero).

### 4. Assortative: supermodularity over ℝ² (WEAK)
`HasIncreasingDifferences f` must hold for all real x, y, including negatives. Becker's types are positive, and standard surplus functions written with Mathlib's `log` or `rpow` misbehave on negatives. See the example in the sanity file: `fun x y => Real.log x * Real.log y` fails at (x, x', y, y') = (−e, −1, 1, e). Suggested fix: require the condition only on the type set, e.g. on `Set.range x ×ˢ Set.range y` or on `Ici 0`.

### 5. gs_blocking_lemma: weaker conclusion (WEAK)
The canonical Blocking Lemma (Gale–Sotomayor) says that if M' (the men who strictly prefer μ' to μ_M) is nonempty, then some pair (m₀, w) blocks μ' with m₀ ∉ M' **and w ∈ μ'(M')**. The formal statement keeps only m₀ ∉ M' and drops the location of w. It is still nontrivial and enough for single-agent strategy-proofness, but it is not the canonical lemma.

### 6. Matching: model restrictions (documented deviation)
- There is no outside option or acceptability. Stability has no IR clause, and a man cannot report a truncated list. Roth's and Dubins–Freedman's strategy space includes truncations, and those are the profitable manipulations for women.
- `daMatching_strategyproof` covers a single deviator. The coalitional Dubins–Freedman theorem is missing. Women-pessimality is also missing.

### 7. Myerson.lean: revenue equivalence (WEAK)
`expected_revenue_eq` averages only over finitely supported `SimpleLottery` distributions. The textbook statement, Krishna Prop 3.1 with continuous F and n bidders, is not stated.

### 8. VCG: coverage
Efficiency is assumed (`hk`) rather than derived. The converse (Green–Laffont: on rich domains, every efficient DSIC mechanism is Groves) is missing.

## Checks that passed (adversarial attempts that failed)
- `myerson_ic_iff`: both directions hold. A monotone `q` on `Icc a b` is interval-integrable, so the integral is not junk. For a > b both sides are vacuous.
- `revenue_le_virtual`: holds without θ being monotone. `rentFloor_le` follows from adjacent downward IC plus IR at type 0.
- `no_efficient_dsic_budgetBalanced_trade`: true without IR. Hand proof with points x < y < z < w in (a,b).
- `clarke_individuallyRational`: true for `v ≥ 0`.
- `daMatching_strategyproof` with a tied misreport `um'`: m's proposals are a deterministic function of `R m`, and `R m` only grows. Any tied report therefore acts like some strict list, so the statement is still true.
- `firstPrice_equilibrium`: a negative bid wins with probability 0 and pays 0, which is consistent.
