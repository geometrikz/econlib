# Statement review: 15 focus files (statements and definitions only; proofs are `sorry`)

Scope: only `/home/user/review4/stripped`. Supporting files (Games/ZeroSum, Games/Strategic,
Matching/GaleShapley, Mechanism/BilateralTrade, Mechanism/Myerson, Uncertainty/VNM) were read
only to resolve definitions.

Verdicts: **OK** = faithful; **WEAK** = true and faithful in spirit but weaker or narrower than the
textbook, or the docstring claims more than is stated; **MISMATCH** = says something different
from the cited result; **VACUOUS-RISK** = hypotheses can be unsatisfiable in natural cases;
**SUSPICIOUS** = possibly false.

No statement in the 15 files was found to be false (SUSPICIOUS) or wholly vacuous. Every
problem found is a hypothesis that is stronger than the textbook's, a conclusion that is weaker,
or a docstring that claims more than the statement gives.

## Summary table

| Declaration | File | Textbook reference | Verdict | Reason |
|---|---|---|---|---|
| `norm_le_of_mem_Icc`, `integrable_ite_one`, `integrable_ite_self` | Mechanism/MyersonSatterthwaite | auxiliary | OK | Correct technical lemmas (finite measure, measurable `f`). |
| `vcg_isICMech` | Mechanism/MyersonSatterthwaite | Krishna Ch. 5 (VCG / pivot) | OK | Interim VCG with price `f c` is IC; true for a finite measure. |
| `payment_eq_vcg` | Mechanism/MyersonSatterthwaite | Myerson lemma + VCG (Krishna 5.3) | OK | `p v = VCG(v) − U(a)`; checked at `v = a` (both sides give `p a`) and by the envelope formula. |
| `QB`,`PB`,`QS`,`RS` | Mechanism/MyersonSatterthwaite | MWG 23.E interim quantities | OK | Bochner junk (non-integrable gives 0) is harmless: the theorem uses only the interim functions. |
| `IsBIC`, `IsInterimIR` | Mechanism/MyersonSatterthwaite | MWG 23.D/23.E | WEAK | Imposed at **every** type in `[a,b]`, including types outside either trader's support (see §1). |
| `IsExAnteBudgetBalanced` | Mechanism/MyersonSatterthwaite | Krishna 5.3 (ex ante BB) | OK | `E[tS] ≤ E[tB]`, the right (weak) direction. |
| `myerson_satterthwaite` | Mechanism/MyersonSatterthwaite | MWG Prop. 23.E.1; M–S 1983 | WEAK (docstring MISMATCH) | True, but "supported in `[a,b]`" plus constraints on all of `[a,b]²` means that for non-overlapping supports it rules out mechanisms that work for every real type. The economic condition (overlapping supports) is not captured (§1). |
| `TradeMechanism.isExAnteBudgetBalanced_of_expost` | Mechanism/MyersonSatterthwaite | Fubini | OK | Joint integrability is assumed; correct. |
| `myerson_satterthwaite_expost` | Mechanism/MyersonSatterthwaite | MWG 23.E.1 (ex post BB) | WEAK | Inherits §1. |
| `uniform_satisfies_hypotheses` | Mechanism/MyersonSatterthwaite | Krishna Ex. (uniform) | OK | Distributional hypotheses are satisfiable (`E(v−c)⁺ = 1/6`). Only the distributional part is witnessed. |
| `rivalsLaw`, `fpBid`, `fpWinProb`, `fpPayoff` | Mechanism/FirstPrice | Krishna §2.3 | OK | Product uniform law; strict `<` for winning; ties have measure 0. |
| `volume_Iio_inter_Icc`, `firstPrice_winProb`, `pow_tangent_le` | Mechanism/FirstPrice | — | OK | `P(win | b) = clamp((m+1)b/m)^m`; checked. |
| `firstPrice_equilibrium` | Mechanism/FirstPrice | Krishna Prop. 2.2 (uniform case) | OK | All `b ∈ ℝ` are allowed; checked the `b ≥ m/(m+1)` region (`g(v)=v^{m+1}/(m+1)−v+m/(m+1) ≥ 0`). Covers the uniform case only, as the docstring says. Uniqueness is not claimed. |
| `firstPrice_revenue` | Mechanism/FirstPrice | Krishna §2.3; RET | OK | `m/(m+2) = (n−1)/(n+1)`; checked. |
| `daIter`…`exists_proposer_ge` (Iter section) | Matching/StrategyProof | DA mechanics | OK | Internal; termination bound `|M||W|+1` is correct. |
| `daMatching`, `Improves`, `NoRejection` | Matching/StrategyProof | Roth–Sotomayor Ch. 2/4 | WEAK | Model: every partner acceptable, and preferences are complete rankings over `W` only. The "unacceptable" report is not available (§4). |
| `daMatching_isStable` | Matching/StrategyProof | GS 1962 Thm 1 | OK | Needs only women's strictness; plausible (proposals go in weakly decreasing order). |
| `daMatching_menOptimal` | Matching/StrategyProof | GS 1962 Thm 2 | OK | |
| `gs_blocking_lemma` | Matching/StrategyProof | Gale–Sotomayor 1985 blocking lemma (R–S Ch. 4) | WEAK | Drops the conclusion `w ∈ μ(M')` (the blocking woman is matched under DA to an improving man) (§5). |
| `daMatching_strategyproof` | Matching/StrategyProof | Dubins–Freedman 1981; Roth 1982; R–S Thm 4.7 | WEAK | Correct individual SP. The deviation report `um' m` may have ties (harmless: DA under a tied report behaves like some strict order). Restricted strategy space (no truncation or unacceptability); no coalitional version (D–F) (§4). |
| `HasIncreasingDifferences`, `matchingSurplus`, `movedSet` | Matching/Assortative | Becker 1973 | OK | `movedSet` is unused in statements. |
| `becker_pam` | Matching/Assortative | Becker 1973 | WEAK | Correct. The docstring invokes the Shapley–Shubik "maximizers = stable outcomes" link, which is not stated. There is no strict-supermodularity uniqueness and no NAM counterpart (§10). |
| `IsParetoExt` | Partial/Externalities | MWG 11.B | WEAK | Does not require the outcome itself to be feasible (`h ∈ H`). |
| `coase_pareto_iff` | Partial/Externalities | MWG 11.B (quasilinear efficiency) | OK | True for any `h` (even an infeasible one). |
| `coase_theorem` | Partial/Externalities | MWG 11.B (Coase) | WEAK | No bargaining is modelled. The 2nd conjunct does not mention `h₀` (rights), so "independent of rights" is trivially built in (§6). |
| `pigou_tax` | Partial/Externalities | MWG 11.B (Pigouvian tax `t = −φ₂'(h°)`) | OK | FOC `d₁+d₂=0` and concavity of `φ₁` suffice. `φ₂` need not be concave, and that is correct. |
| `IsPartialEq`, `competitive_maximizes_surplus` | Partial/Externalities | MWG Prop. 10.D.1 | OK | |
| `concaveOn_le_tangent`, `convexOn_tangent_le` | Partial/PublicGoods | — | OK | Mathlib's `ConcaveOn` carries convexity of `S`. |
| `publicSurplus`, `IsEfficientLevel`, `samuelson_condition` | Partial/PublicGoods | MWG (11.C.1) | OK | |
| `samuelson_sufficient` | Partial/PublicGoods | MWG 11.C | OK | Equality at `G = 0` is a sufficient (not necessary) corner condition; fine. |
| `IsLindahlEq`, `lindahl_efficient` | Partial/PublicGoods | MWG 11.D | OK | Constant MC only; prices sum to `c`. |
| `IsVoluntaryEq`, `voluntary_underprovision` | Partial/PublicGoods | MWG Prop. 11.C.1 | OK | Satisfiable (e.g. `φᵢ = −e^{−x}`). The proof idea `d_j(G)=1` for a contributor, so `Σdᵢ(G) > 1`, works. |
| `salopLocalDemand`, `salop_equilibrium` | Partial/Salop | Salop 1979; Tirole §7.1.2 | OK | Demand is postulated, not derived, but correct for `q ≥ c`. Below `c` any `D ≥ 0` gives negative profit. Verified that the max is at `c+t/n`. |
| `salop_free_entry` | Partial/Salop | Tirole 7.1.2 | WEAK | Only the identity `t/(√(t/F))² − F = 0`, not "zero profit iff `n = √(t/F)`" (§9). |
| `salopTransportCost(_eq)`, `salop_social_optimum`, `salop_excess_entry` | Partial/Salop | Tirole 7.1.2 | OK | `n` is real (continuum), as in Tirole. |
| `monopolyProfit`, `IsMonopolyOptimum`, `monopoly_foc` | Partial/Monopoly | MWG (12.B.4) | OK | |
| `lerner_rule` | Partial/Monopoly | Lerner | OK | At `P' = 0` the RHS is `1/(x/0) = 0` (junk), but the LHS is also 0 by the FOC, so it is consistent (and = 1/∞). |
| `monopoly_price_gt_mc` | Partial/Monopoly | MWG 12.B | OK | |
| `monopoly_output_lt` | Partial/Monopoly | MWG Prop. 12.B.1 | WEAK (minor) | Pure order fact. `qm` is not tied to a monopoly optimum (it must be chained with `monopoly_price_gt_mc`). |
| `linearSurplus(_eq)`, `linear_monopoly` | Partial/Monopoly | standard | OK | DWL `(a−c)²/(8b)` checked. |
| `discrimination_price_le` | Partial/Monopoly | Tirole §3.2 (3rd-degree PD) | WEAK | Algebraic fact about `p(1−1/ε)=c`. No multi-market profit maximization is stated (§7). |
| `bertrandShare`, `bertrandProfit`, `bertrandProfit_update`, `bertrand_not_lt` | Partial/Oligopoly | MWG 12.C | OK | |
| `bertrand_isNash_iff` | Partial/Oligopoly | MWG Prop. 12.C.1 | WEAK | Assumes `x p > 0` for **all** `p`, which excludes every demand with a choke price (e.g. linear). MWG needs only continuity and `x(c) > 0` (§3). |
| `cournotProfit`, `IsCournotEq`, `cournot_sum_update`, `cournotQ` | Partial/Oligopoly | MWG 12.C | OK | |
| `cournot_isEq_iff` | Partial/Oligopoly | MWG 12.C | OK | Checked that no asymmetric equilibrium with zero-output firms exists when `a>c`. Empty `I`: both sides are true. |
| `cournot_price`, `cournot_price_gt`, `cournot_price_tendsto` | Partial/Oligopoly | MWG 12.C | OK | The limit is of the closed form, linked through `cournot_price`. |
| `stackelbergBR`, `stackelbergBR_optimal`, `stackelbergLeader` | Partial/Oligopoly | MWG Ex. 9.D.1 | OK | |
| `stackelberg_leader_optimal` | Partial/Oligopoly | MWG Ex. 9.D.1 | WEAK (minor) | The Cournot comparison `(a−c)²/(9b) < (a−c)²/(8b)` is bare arithmetic, not tied to `cournotProfit`/`cournotQ` for 2 firms. |
| `searchProfit`, `IsSearchEq` | Partial/DiamondParadox | Diamond 1971; Tirole §2.6 | WEAK (minor) | The consumer search rule ("stay iff `q ≤ min(u, p+s)`") is hard-coded in the profit, not derived (§8). |
| `diamond_paradox` | Partial/DiamondParadox | Diamond 1971 | OK | Checked both directions (`p<u`: deviate to `min(u,p+s)`; `p>u`: deviate to `u`). |
| `IsVoteProfile`, `majorityRule`, `IsAnonymous`, `IsNeutral`, `IsPositivelyResponsive` | SocialChoice/May | MWG 21.B | OK | Axioms are quantified over vote profiles only. `F` is ℤ-valued, but the conclusion forces values in {−1,0,1}. |
| `IsVoteProfile.neg`, `sum_eq_card_sub_card`, `IsAnonymous.eq_of_card` | SocialChoice/May | — | OK | |
| `may_theorem` | SocialChoice/May | May 1952; MWG Prop. 21.B.1 | OK | Both directions checked. `I = ∅`: neutrality forces `F 0 = 0 = sign 0`. |
| `SinglePeaked` | SocialChoice/MedianVoter | MWG §21.D | OK | |
| `IsMedianPeak` | SocialChoice/MedianVoter | MWG 21.D (median) | MISMATCH | **Strict**-majority median. Unsatisfiable for every even `n` with distinct peaks (e.g. `n=2`) (§2). |
| `median_condorcet` | SocialChoice/MedianVoter | Black 1948; MWG Prop. 21.D.1 | WEAK / VACUOUS-RISK | Vacuous for even `n` with generic peaks. The textbook (weak, any `n`) form "the median is not defeated" is absent (§2). |
| `exists_median` | SocialChoice/MedianVoter | — | OK | Odd `n` only, consistent with above. |
| `BargProblem`, `nashProduct`, `IsNashSolution`, `affMap`, `BargProblem.affine`, `IsSymmetric` | Bargaining/Nash | Nash 1950; O–R Ch. 2 | OK | Compact convex `S`, `d ∈ S`, strict improvement exists: standard. |
| `IsWeakPareto`, `IsSymmetricSol`, `IsAffineInvariant`, `IsIIA` | Bargaining/Nash | Nash axioms | OK | Weak PO is weaker than Nash's PO, so the characterization is stronger; still true (the symmetric dominating problem `{s ≥ −K, s₁+s₂ ≤ 2}` is compact). |
| `exists_nashSolution`, `sum_le_two_of_max`, `nash_bargaining_theorem`, `nashProduct_pos`, `nashSolution_unique`, `nashSol(_spec)`, `eq_nashSol_of_axioms`, `nashSol_axioms` | Bargaining/Nash | Nash 1950 | OK | `sum_le_two_of_max` checked for points with a negative coordinate via convexity along the segment to `(1,1)`. |
| `IsInCore`, `IsBalancedFamily`, `IsBalanced` | Cooperative/Core | Bondareva/Shapley; O–R 13.1 | OK | `∅` is included on both sides (the docstring explains). Both sides force `v ∅ ≤ 0`. |
| `sum_weight_mul_sum`, `isBalanced_of_mem_core`, `singletonWeights*`, `matrixPayoff_degenerate_*`, `exists_mem_core_of_pos` | Cooperative/Core | — | OK | |
| `bondareva_shapley` | Cooperative/Core | Bondareva 1963; Shapley 1967 | OK | Also true for empty `N` (both sides ⇔ `v ∅ = 0`), so `[Nonempty N]` is harmless. |
| `TUGame`, `PlayerOrder`, `predSet`, `marginalContribution`, `shapley` | Cooperative/Shapley | Shapley 1953 | OK | Random-order formula; `card (N ≃ Fin n) = n!`. |
| `IsSymmetricPair`, `IsNullPlayer`, `IsShapleyAxioms` | Cooperative/Shapley | Shapley 1953; O–R 14.4 | OK | Efficiency is `v N − v ∅`. The constant game (`T=∅` dividend) gets 0 from null player + efficiency, consistently. |
| `sum_marginal` … `eq_shapley_of_axioms` | Cooperative/Shapley | Shapley 1953 | OK | `apply_unanimity` at `T=∅` avoids the `c/0` junk because `i ∉ ∅`. |

## Non-OK items in detail

### 1. `myerson_satterthwaite` / `myerson_satterthwaite_expost` / `IsBIC` / `IsInterimIR`: WEAK, docstring MISMATCH

The distributions are only required to be **supported in** `[a,b]`. Efficiency (`IsEfficient a b`),
BIC and interim IR are required at **every** point of `[a,b]` (resp. `[a,b]²`), including types
that occur with probability zero for that trader. MWG 23.E.1 assumes both traders' densities are
positive on the common interval `[θ_lo, θ_hi]`. The economically correct general condition (when
constraints bind only on the supports) is overlapping supports, not `E(v−c)⁺ > 0`.

Concrete example: `μB = U[2,3]`, `μS = U[0,1]`, `a = 0`, `b = 3`. All hypotheses of the theorem hold
(`hgain = 1.5 > 0`, atomless, supported in `[0,3]`). The posted price `p = 1.5` (trade iff
`c ≤ 1.5 ≤ v`, buyer pays and seller receives 1.5) is efficient, IC, IR and exactly budget
balanced for **every type that actually occurs**. Yet the theorem "rules it out". It can do so only
because `IsEfficient 0 3` demands trade at the phantom profile `(v,c) = (1.2, 1.0)`, and BIC/IR
are demanded for buyer types in `[0,2)` and seller types in `(1,3]`. The formal statement is true
(the VCG comparison works with these phantom constraints), but the docstring says "no mechanism is
efficient, BIC, IR and BB" whenever `E(v−c)⁺ > 0`, and that is false in the textbook sense.

Fix: require full support (e.g. `μB (Ioo x y) > 0` for `a ≤ x < y ≤ b`, and likewise for `μS`), or
restate efficiency, IC and IR only on the supports and add an overlap hypothesis.

Secondary: no witness that IC + IR + BB are jointly satisfiable without efficiency (only the
distributional hypotheses are witnessed). The posted-price example in `BilateralTrade.lean` covers
the DSIC analogue only.

### 2. `IsMedianPeak` / `median_condorcet`: MISMATCH / VACUOUS-RISK

`IsMedianPeak` requires `n < 2·#{peak ≤ m}` **and** `n < 2·#{peak ≥ m}` (strict majorities on
both sides). With `n = 2` and peaks `0, 1`, the condition needs `#{≤ m} = 2` and `#{≥ m} = 2`,
which is impossible. For every even `n` with pairwise distinct peaks, no `m` qualifies, so
`median_condorcet` is vacuous there. MWG Prop. 21.D.1 uses the weak median
(`#{peak ≤ m} ≥ n/2`, `#{peak ≥ m} ≥ n/2`) and concludes, for every `n`, that the median is not
defeated (`#{u_i m ≥ u_i y} ≥ n/2`). That version is not stated anywhere. The stated strict
version is a correct but narrower result (odd `n`, or even `n` with a repeated median peak), and
the docstring "(MWG Prop. 21.D.1)" overstates it.

### 3. `bertrand_isNash_iff`: WEAK

`hpos : ∀ p, 0 < x p` excludes every demand function with a choke price, including the textbook
linear demand `x(p) = max(0, A − p)` (it is 0 for `p ≥ A`). MWG Prop. 12.C.1 assumes only that `x`
is continuous and `x(c) > 0` (positive somewhere above `c`). The conclusion still holds under that
weaker hypothesis. If both firms charge `p > c` with `x(p) = 0`, a deviation to a price just above
`c` with `x > 0` is profitable, and the other cases are unchanged. So the formalization proves the
paradox only for demands that are positive at all prices, including absurdly high and negative
ones.

### 4. `daMatching_strategyproof` / DA model: WEAK

(a) Every woman is acceptable to every man and vice versa ("unmatched is worst"). A report is a
utility `W → ℝ`, so a man cannot declare a woman unacceptable. Roth (1982) and
Dubins–Freedman/R–S Thm. 4.7 are stated for preferences that include the outside option, so the
strategy space there includes truncations. The theorem rules out a smaller class of manipulations.
(b) Only individual strategy-proofness is stated. Dubins–Freedman's theorem is coalitional (no
coalition of men can all strictly gain). The file cites D–F, but the group version is absent.
(c) Harmless point: `um' m` may have ties. DA under a tied report proceeds through a fixed sequence
of distinct proposals, so it is equivalent to some strict report and no exploit arises.

### 5. `gs_blocking_lemma`: WEAK

The Gale–Sotomayor blocking lemma (as presented in Roth–Sotomayor Ch. 4) concludes that `μ'` is blocked by
`(m₀, w)` with `m₀ ∉ M'` **and `w ∈ μ(M')`** (the blocking woman is DA-matched to an improving
man). The formal conclusion keeps only `m₀ ∉ M'`. That is enough for individual SP, but it is not
the lemma as published, and it is the form used for the coalitional result.

### 6. `coase_theorem` (and `IsParetoExt`): WEAK

The statement has two parts. (i) There exists `T` making `(h*,T)` Pareto efficient and IR relative
to the disagreement level `h₀`. (ii) Every Pareto efficient outcome has maximal surplus. Part (ii)
does not involve `h₀` at all, so "independence of the allocation of rights" holds by construction
(it is just `coase_pareto_iff`). No bargaining process or outcome is modelled; MWG's claim is that
bargaining reaches the efficient level. Also, `IsParetoExt H φ₁ φ₂ h T` does not require
`h ∈ H`. For example, with `H = {0}`, `φ₁ = id`, `φ₂ = 0`, the infeasible outcome `(5, 0)` is
"Pareto efficient". The theorems add `h ∈ H` where it matters, so the statements are fine, but the
definition is not.

### 7. `discrimination_price_le`: WEAK

The hypotheses are the already-solved per-market conditions `pₖ(1−1/εₖ)=c`. The theorem is the
fact that `cε/(ε−1)` decreases in `ε`. Nothing states that a third-degree discriminating
monopolist's profit maximum satisfies these conditions (there is no multi-market profit function).
The header's "third-degree price discrimination" result is only half present.

### 8. `searchProfit` / `diamond_paradox`: WEAK (minor)

The theorem is correct for its reduced form. The deviant keeps its `1/n` share iff
`q ≤ min(u, p+s)` and has no way to attract customers by undercutting. That is Diamond's
equilibrium logic, but it is assumed in the payoff rather than derived from consumers' optimal
sequential search (reservation price `min(u, p+s)` given the belief that others charge `p`). As a
check that the theorem leans on `hs`: at `s = 0` the same profit function makes every `p ≤ u` an
equilibrium, not Bertrand pricing. So the formula is meaningful only as the `s>0` reduced form.

### 9. `salop_free_entry` (and `stackelberg_leader_optimal`'s last conjunct, `monopoly_output_lt`): WEAK (minor)

`salop_free_entry` is the identity `t/(√(t/F))² − F = 0`. It does not say that zero profit happens
**only** at `√(t/F)` (`salop_excess_entry` partly covers this). Stackelberg's "more than its Cournot
profit" is the number inequality `1/9 < 1/8`, unconnected to `cournotProfit` with two firms.
`monopoly_output_lt` takes any `qm` with `MC qm < P qm`, not the monopoly optimum. The chain is left
to the reader.

### 10. `becker_pam`: WEAK (docstring)

The statement is correct (identity permutation maximizes `Σ f(xᵢ, y_σ(i))` under increasing
differences). The docstring claims the result is Becker's "stable = surplus maximizing
(Shapley–Shubik)" assortative-mating theorem, but no transfers, stability or the Shapley–Shubik
equivalence are formalized. Strict supermodularity giving PAM as the **unique** optimum (for
distinct types), and the submodular/NAM counterpart, are absent.

## Items checked and found OK (selected reasoning)

- **First-price auction**: the deviation set is all of `ℝ`. For `b ≥ m/(m+1)`,
  `v − b ≤ v^{m+1}/(m+1)` holds on `[0,1]`. Revenue `(m+1)·∫ (m/(m+1))v·v^m = m/(m+2) = (n−1)/(n+1)`.
- **Myerson–Satterthwaite junk values**: a non-integrable `tB v ·` gives `PB v = 0`. The theorem
  quantifies over interim functions anyway, so junk cannot make it true for the wrong reason. The
  outer integrals are of a.e.-bounded measurable functions (forced by `payment_eq_vcg`).
- **Atomlessness** makes the diagonal `c = v` null, so efficiency pins `x` a.e.
- **May**: positive responsiveness matches MWG. The forward direction works through tie profiles.
  `I = ∅` is fine.
- **Cournot**: there is no corner equilibrium with some firms at zero output, since
  `(a−c)(1 − k/(k+1)) > 0`.
- **Nash bargaining** with *weak* Pareto: still a full characterization. The bounding symmetric
  problem `{s ≥ −K, s₁+s₂ ≤ 2}` is compact, and its only weakly-PO symmetric point is `(1,1)`.
- **Bondareva–Shapley / Shapley** with no `v ∅ = 0` normalization: both handled consistently
  (core and balancedness both force `v ∅ ≤ 0`; Shapley efficiency is `v N − v ∅`).
- **Lerner** at `P' = 0`: the junk `1/0 = 0` coincides with the true value `1/∞`.

## Re-review (revised files)

Same isolation rules: I read only `/home/user/review4/stripped`, built nothing, and judged statements only.

| # | Item | Earlier finding | Status now | New issue? |
|---|---|---|---|---|
| 1a | `bertrand_isNash_iff` | WEAK (`x > 0` everywhere excluded choke prices) | **Resolved** | None. See below. |
| 1b | `stackelberg_leader_optimal` docstring | WEAK minor (bare `1/9 < 1/8`) | **Partly resolved** (documented scope) | Residual wording only: the module header now says "bare comparison", but the theorem's own docstring still says "its Cournot profit". |
| 2 | `IsMedianPeak` / `median_condorcet`; new `IsWeakMedianPeak`, `median_not_defeated`, `exists_weakMedian` | MISMATCH / VACUOUS-RISK | **Resolved** | None. |
| 3 | `IsParetoExt`, `coase_pareto_iff`, `coase_theorem` | WEAK | **Resolved** (feasibility). **Partly resolved** (no bargaining model, now stated as scope) | None. |
| 4a | `monopoly_optimum_lt_competitive` (new) | WEAK minor (`monopoly_output_lt` not tied to the optimum) | **Resolved** | Minor: `MC` is tied to `C'` only at `qm`, not everywhere (see below). Not wrong. |
| 4b | `discrimProfit`, `third_degree_discrimination` (new) | WEAK (algebra only) | **Resolved** | None; junk-division cases are excluded by `ε > 1`. |
| 5 | `salop_free_entry` | WEAK (identity only) | **Resolved** | None. |
| 6 | `myerson_satterthwaite(_expost)`, docstrings only | WEAK / docstring MISMATCH | **Partly resolved**: the documentation is adequate as a scoping | No statement change. Optional suggestion below. |
| 7a | `gs_blocking_lemma` docstring | WEAK (dropped `w ∈ μ(M')`) | **Partly resolved** (honestly documented) | None. |
| 7b | `daMatching_strategyproof` docstring | WEAK (no truncation, no coalitional version) | **Partly resolved** (documented scope) | Minor: the module-header bullet still reads unqualified ("no man can obtain a strictly better partner by misreporting"); it could point to the scope note. |
| 7c | `becker_pam` (module docstring) | WEAK (docstring overclaim) | **Resolved** (overclaim removed, gaps listed) | None. |

### Details

**1a. Bertrand.** New hypotheses: `Continuous x`, `Antitone x`, `x ≥ 0`, `x c > 0`. I re-checked both directions.
- `(c,c)` is Nash: undercutting gives `(t−c)x(t) ≤ 0` because `x ≥ 0`, and raising the price gives 0.
- Uniqueness, case `p₁ = p₂ = p > c`: if `x p > 0`, undercut slightly (continuity). If `x p = 0`, profit is 0, and `bertrand_exists_pos` gives a price `t ∈ (c, p)` with positive profit.
- Case `p₁ = p₂ < c`: profit is strictly negative because `x p ≥ x c > 0` (antitone), so raising the price to get 0 is a profitable deviation.
- Case `p₁ < p₂`: if `p₁ < c`, firm 1 loses money (antitone again). If `p₁ = c`, firm 1 can move into `(c, p₂)`. If `p₁ > c`, firm 2 can move into `(c, p₁)`.

The theorem is true. Some condition like `Antitone` is genuinely needed. Without it, `x p = 0` at some `p < c` would make `p₁ = p₂ = p` an equilibrium. Monotone demand is also MWG's setting. Linear demand with a choke price `A > c` now qualifies, and `bertrand_exists_pos` is correct as stated.

**2. Median voter.** `median_not_defeated` is correct for every `n`.
- If `y > m`, every voter with peak `≤ m` strictly prefers `m`, and there are `≥ n/2` of them. So at most `n/2` voters strictly prefer `y`, and these are no more than the voters who weakly prefer `m`. The case `y < m` is symmetric, and `y = m` is trivial.
- The second conjunct is exactly MWG 21.D.1's "not defeated".
- `exists_weakMedian` correctly needs `[Nonempty I]`: with `n = 0` every `m` is a weak median, but there is no peak to name.
- The `Fin 2` witness (peaks 0 and 1) is correct and shows that the weak form is not vacuous while the strict form has no median at all.
- `median_condorcet` is now labelled "strict form" and points to the weak form.

**3. Coase.** `IsParetoExt` now requires `h ∈ H`. The right side of `coase_pareto_iff` adds `h ∈ H`, so the iff is still true. `coase_theorem` is unchanged in content and now says plainly that bargaining is not modelled and that the surplus half does not involve `h₀` by design. This is acceptable as an "efficiency form" of Coase.

**4a. `monopoly_optimum_lt_competitive`.**
- The proof goes through: the FOC `P(qm) + P'qm = MC(qm)` with `P' < 0` gives `MC(qm) < P(qm)`. Then if `qm ≥ qo`, `P(qm) ≤ P(qo) = MC(qo) ≤ MC(qm)`, a contradiction.
- Minor point: `hC : HasDerivAt C (MC qm) qm` ties `MC` to `C'` only at `qm`. Elsewhere `MC` is any monotone function, so "competitive output" `qo` is defined against `MC`, not against `C'`. This makes the statement more general, not wrong. When `MC = C'` everywhere it is exactly MWG 12.B.1. Optionally, assume `∀ q, HasDerivAt C (MC q) q`.
- The hypotheses are satisfiable, for example by linear demand with constant MC.

**4b. Third-degree discrimination.**
- `hopt` is a genuine joint maximization over `q ≥ 0`. With interior `q₁, q₂`, the partial FOCs give `Pₖ + Pₖ'qₖ = c`.
- `εₖ > 1` rules out the junk cases. `Pₖ' = 0` or `Pₖ = 0` would make the ratio 0. A positive slope would force `p < 0` and hence `c < 0`, which contradicts `c ≥ 0`.
- With those cases gone, `p(1 − 1/ε) = p + P'q = c`, and `discrimination_price_le` applies.

The statement is correct, and the header now describes it accurately.

**5. Salop.** For `n > 0`, `t/n² − F = 0 ↔ n = √(t/F)` is a genuine characterization. Resolved.

**6. Myerson–Satterthwaite.** The module docstring's "Scope" paragraph is accurate. It says that the type space is all of `[a,b]`, that this equals MWG 23.E.1 under full support, and that without full support the theorem can rule out mechanisms only through constraints at types that never occur. It gives the `U[2,3]` / `U[0,1]` posted-price example and says the support-only version is not formalized. The theorem docstring points to it. I consider this an adequate scoping, so the earlier docstring MISMATCH is removed. The statement stays WEAK relative to the general (support-only constraints) theorem, but it is now honestly labelled.

Optional improvement: add a full-support corollary, e.g. `(∀ x y, a ≤ x → x < y → y ≤ b → 0 < μB (Ioo x y))` and likewise for `μS`. A reader could then cite a statement whose hypotheses literally match MWG. This is a convenience, not a correctness issue.

**7. Matching.** The `gs_blocking_lemma` and `daMatching_strategyproof` docstrings now state exactly what is missing (`w ∈ μ(M')`; truncation strategies; the coalitional version). Since only docstrings changed, these remain narrower than the literature but are correctly scoped. The `becker_pam` module docstring now disclaims the Shapley–Shubik link, uniqueness and the NAM counterpart. Resolved as a docstring issue.

### Net after re-review

The two most serious items are fixed in the statements themselves:
- The median voter theorem now has the weak form for any `n`.
- Bertrand now assumes textbook demand.

Coase feasibility, Salop free entry, monopoly underprovision and third-degree discrimination are also fixed in the statements. Myerson–Satterthwaite, the matching items and Stackelberg are acceptable as documented scope. Only small residuals are left: two wording nits (the Stackelberg theorem docstring and the DA module-header bullet) and the optional `MC = C'` everywhere hypothesis. None of them affects correctness.
