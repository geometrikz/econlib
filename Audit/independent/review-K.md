# Statement review: Information/*, Games/Repeated, Bargaining/Nash

Reviewer K. I read only `/home/user/rv4/in/` (statements with `sorry` proofs). I checked context definitions in `Uncertainty/MoneyLottery.lean` (`SimpleLottery`, `expect`), `Uncertainty/VNM.lean` (`lotteries`) and `Games/Strategic.lean` (`IsNash`, `pdPayoff`).

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `offeredMass`, `offeredQuality`, `IsLemonsEq` | Information/Lemons | Akerlof 1970; MWG 13.B (eq. w* = E[θ \| r(θ) ≤ w*]) | WEAK | Only the case r(θ)=θ (buyer value = seller value). There are no gains from trade, so there is nothing to lose welfare-wise and full unraveling is automatic. A buyer premium (Akerlof's 3/2·x) can't be expressed. |
| `isLemonsEq_iff` | Lemons | MWG 13.B, r(θ)=θ special case | faithful with documented deviation | Correct (p ⇒ only the minimum quality trades), but only in the degenerate no-gains model above. |
| `IsLemonsEq.only_worst` | Lemons | same | faithful with documented deviation | Same model. |
| `outcomeMean`, `ImplementsHigh` | Information/MoralHazard | MWG 14.B; Grossman–Hart 1983 (utility-space contract ν = u(w)) | faithful | Standard IR + IC in utility units, with separable effort cost. |
| `outcomeMean_const` | MoralHazard | – | faithful | Trivial. |
| `fullInsurance_optimal` | MoralHazard | MWG 14.B.2 (first-best cost: full insurance) | WEAK | φ = u⁻¹ must be convex and monotone on **all of ℝ**. That excludes CARA (φ(v) = −log(−v)/r exists only on v<0 and blows up) and every utility whose range is bounded above. |
| `implementsHigh_nonconstant` | MoralHazard | MWG 14.B | faithful | Constant ν can't satisfy IC when gL<gH. |
| `implementsHigh_cost_gt` | MoralHazard | MWG Prop. 14.B.2 (second-best cost > first-best when agent strictly risk averse) | WEAK | Needs `StrictConvexOn ℝ univ φ` plus `Monotone φ` on all of ℝ. That excludes CARA, and also √w or any CRRA with ρ<1 (φ(v)=v² on v≥0 has no strictly convex monotone extension to ℝ). In practice only log-type u, whose range is ℝ, can be plugged in. |
| `sellTheFirm` | MoralHazard | MWG 14.B (risk-neutral agent ⇒ first best) | WEAK | Pure algebra. `heff` assumes high effort is efficient. The 3rd conjunct is `outcomeMean_const`. It never states that the principal's payoff is the *maximal* (first-best) payoff over all contracts and efforts. |
| (coverage) informativeness principle | MoralHazard | Holmström 1979; Bolton–Dewatripont §4.2 | MISSING | The headline names it, but nothing states it: no extra signal, no sufficient-statistic condition, no likelihood-ratio form of the contract, and no "second-best may implement low effort" result. |
| `beliefs`, `Signal`, `msgProb`, `post`, `signalValue` | Information/Persuasion | Kamenica–Gentzkow 2011 §II | faithful | `post` is junk (= μ₀) when msgProb = 0, but it always carries weight 0. Harmless. |
| `msgProb_nonneg`, `sum_msgProb`, `joint_eq_zero`, `post_mem`, `signal_mean` | Persuasion | KG Prop. 1 (Bayes plausibility, ⇒ direction) | faithful | |
| `Splitting`, `toSplitting`, `toSignal`, `value_*`, `joint`, `msgProb_toSignal`, `ν_zero` | Persuasion | KG Prop. 1 (both directions) | faithful | The splitting ↔ signal correspondence preserves value. Checked the μ₀ ω = 0 branch of `toSignal`: `joint` still holds because the τ·ν terms are nonnegative. |
| `V` | Persuasion | KG: concave closure of v̂ | faithful with documented deviation | Defined as `sSup`. It is junk (0) if v is unbounded above, but every theorem about V assumes `hB`, concavity or USC on the compact simplex. v is a reduced-form indirect utility rather than one built from a receiver problem. |
| `value_le`, `bddAbove`, `value_le_V`, `le_V`, `V_le_of_concave`, `V_concave`, `convex_beliefs` | Persuasion | KG Cor. 2 (V = smallest concave majorant) | faithful | Together these give the full concavification characterization. |
| `Splitting.mix`, `value_mix` | Persuasion | – | faithful | |
| `benefits_iff` | Persuasion | KG Cor. 1–2 | faithful | |
| prosecutor example (`prior`, `convict`, `prosecutorSplitting`, `prosecutor_*`, `concave_majorant`) | Persuasion | KG §I example (0.3 prior → 60% conviction) | faithful | Numbers match KG. Ties are broken toward conviction (≥ 1/2), which matches sender-preferred tie-breaking. |
| `isCompact_beliefs`, `uscOn_mul`, `bounded`, `toSplitting`, `bValue`, `isCompact_bounded`, `sum_extend`, `exists_small` | Information/PersuasionExistence | Carathéodory | faithful | I checked `uscOn_mul` at g(p₀)=0 and found no counterexample. |
| `exists_optimal_splitting`, `exists_optimal_signal` | PersuasionExistence | KG Cor. ("an optimal signal exists"; Prop. 4-type bound ≤ min(\|A\|,\|Ω\|) messages) | faithful with documented deviation | Existence holds under USC. The message bound is \|Ω\|+2, weaker than KG's \|Ω\|. |
| `convict_usc`, `prosecutor_exists_optimal` | PersuasionExistence | KG example | faithful | |
| `ScreeningModel`, `Feasible`, `profit`, `surplusH`, `virtualL`, `VS` | Information/Screening | MWG 14.C; Bolton–Dewatripont §2.3 (two types) | faithful | The standard two-type model. v is unrestricted, but the theorems are argmax-based so this does no harm. |
| `screeningProfit_le`, `tLBind`, `tHBind`, `bindingMenu_feasible`, `screeningProfit_bindingMenu` | Screening | relaxed-problem reduction | faithful | I checked the algebra. Only IR_L and IC_H are used, as in the textbook. |
| `isOptimalMenu_binding` | Screening | MWG 14.C / B–D Prop. 2.? | faithful with documented deviation | Monotonicity `v qL ≤ v qH` is **assumed**, not derived. The textbook derives it from v increasing and θL<θH. |
| `IsOptimalMenu.noDistortionAtTop` | Screening | "no distortion at the top / IR binds at bottom / IC_H binds" | WEAK | Correct (I checked pL = 0 and θL = θH as well). It assumes a monotone relaxed solution exists. It does **not** state downward distortion at the bottom (qL < qL^FB) or the high type's positive information rent. |
| `spenceWage`, `IsSpencePBE` | Information/Signaling | MWG 13.C; Spence 1973 | faithful | Pure-strategy PBE, wage = expected productivity, off-path beliefs free. |
| `separating_eL`, `separating_bounds`, `isSpencePBE_separating`, `pooling_bound`, `isSpencePBE_pooling` | Signaling | MWG 13.C (separating & pooling equilibrium conditions) | faithful | Necessary and sufficient conditions check out by hand. |
| (coverage) intuitive criterion / Riley outcome | Signaling | Cho–Kreps 1987; MWG 13.AA | MISSING / MISMATCH with headline | No refinement is defined. Pooling PBEs that the intuitive criterion eliminates are certified by `isSpencePBE_pooling` (see sanity test). The least-cost separating equilibrium is never characterized. |
| `RepeatedProfile`, `histFrom`, `pathFrom`, `discPayoff` | Games/Repeated | Fudenberg–Tirole ch. 5 | faithful with documented deviation | Pure strategies with perfect monitoring. `discPayoff` is junk outside δ∈[0,1) (`(1-δ)=0` at δ=1; `∑'` = 0 when not summable). |
| `IsRepeatedSPE` | Repeated | F–T Def. 5.? (SPE) | VACUOUS-RISK | It quantifies over all histories and all deviations, which is correct. But with no δ restriction, **every** profile is an SPE at δ = 1 (both sides are 0). All theorems assume `δ < 1`, so none is affected today. |
| `summable_disc`, `discPayoff_le_of_bellman`, `disc_const` | Repeated | – | faithful | |
| `IsClean`, `grimTrigger`, `isClean_cons`, `grimTrigger_apply_*`, `grimTrigger_path`, `discPayoff_grimTrigger` | Repeated | – | faithful | |
| `grimTrigger_isSPE` | Repeated | F–T Thm 5.? (Nash reversion; one-shot condition) | faithful | The `hdev` condition is the right one-shot inequality, and boundedness is assumed. The PD example threshold δ ≥ 1/5 is correct. |
| `nashReversion_folk` | Repeated | Friedman 1971 | faithful with documented deviation | It is only the Nash-reversion folk theorem for a **pure** profile a that strictly dominates a stage Nash e. |
| (coverage) one-shot deviation principle; Fudenberg–Maskin folk theorem | Repeated | F–T Thm 4.2, Thm 5.4 | MISSING | The headline says "folk theorem / OSDP". There is no general infinite-horizon OSDP (the only OSDP is for finite trees in Games/Extensive). There is no minmax / feasible-IR-set folk theorem. Payoffs between minmax and stage-Nash, and convex combinations, are not covered. |
| `BargProblem`, `nashProduct`, `IsNashSolution` | Bargaining/Nash | Nash 1950; Osborne–Rubinstein *Bargaining & Markets* Thm 2.3 | faithful | |
| `exists_nashSolution`, `nashProduct_pos`, `nashSolution_unique`, `nashSol`, `nashSol_spec` | Nash | O–R Lemma 2.2 | faithful | |
| `IsWeakPareto`, `IsSymmetricSol`, `IsAffineInvariant`, `IsIIA` | Nash | O–R §2.3 | faithful | Weak Pareto is *weaker* than O–R's PAR, which makes the characterization stronger. It is still true: the symmetric-hull proof only needs weak PO. |
| `sum_le_two_of_max`, `nash_bargaining_theorem`, `eq_nashSol_of_axioms`, `nashSol_axioms` | Nash | O–R Thm 2.3 (both directions) | faithful | Full characterization. The axioms are shown jointly satisfiable. |

## Details on non-faithful items

### 1. Signaling: no intuitive criterion (headline gap)
The headline promises "Spence signaling (separating equilibria, intuitive criterion)". `Signaling.lean` defines only PBE. Take θL=1, θH=2, pH=1/2, c(e,θ)=e/θ. Pooling at e=0 with beliefs μ(0)=1/2 and μ(x≠0)=0 is a PBE by `isSpencePBE_pooling` (sanity test S1). The intuitive criterion kills it: an education level e' with 1/2 < e' < 1 is equilibrium-dominated for L but not for H. Nothing in the file selects the Riley (least-cost separating) equilibrium, where eH = θH − θL = 1 with these costs.

### 2. MoralHazard: φ = u⁻¹ required convex/monotone on all of ℝ
`fullInsurance_optimal` and `implementsHigh_cost_gt` quantify convexity and monotonicity over `Set.univ`, not over the range of u. This has the same structure as the earlier Σ√xᵢ finding.
- CARA u(w) = −e^{−rw} has range (−∞,0), and φ(v) = −log(−v)/r → ∞ as v↑0. No monotone φ: ℝ→ℝ can agree with it on v<0 (sanity test S2, fully proved). Neither theorem can be applied to CARA.
- u(w)=√w on w≥0 gives φ(v)=v² on v≥0. Any monotone, convex extension to ℝ must be identically 0 on (−∞,0], so it is not strictly convex. `implementsHigh_cost_gt` cannot be applied (sanity test S3, sketched with sorry).
To fix this, quantify over an interval `U` (the utility range), require `ν ω ∈ U`, and use `ConvexOn ℝ U φ` and `MonotoneOn φ U`.

### 3. MoralHazard: informativeness principle and first-best optimality missing
There is no statement of Holmström's informativeness principle, even in its two-outcome / likelihood-ratio form. There is also no characterization of the optimal second-best contract. `sellTheFirm` checks feasibility and a payoff identity (the third conjunct reduces to `outcomeMean_const`, sanity test S4). It never states that this payoff equals the first-best maximum over all efforts and contracts.

### 4. Repeated: OSDP and the real folk theorem missing
`nashReversion_folk` is Friedman's theorem. It is true as stated, but it can't sustain payoffs below the stage-Nash payoff, mixed or correlated targets, or anything that needs minmax punishments. Fudenberg–Maskin is absent. There is no infinite-horizon one-shot deviation principle (`σ` is an SPE iff no profitable one-shot deviation, for bounded u and δ<1). `grimTrigger_isSPE` builds its one-shot condition in by hand.

### 5. Repeated: `IsRepeatedSPE` is vacuous at δ = 1
`discPayoff u 1 σ h i = (1-1)·… = 0`, so `IsRepeatedSPE u 1 σ` holds for every σ (sanity test S5). For δ>1, a nonsummable `∑'` is also 0. The theorems all assume `δ < 1`, but the definition should carry `0 ≤ δ < 1`, or downstream users could state theorems about it with no content.

### 6. Lemons: no gains from trade
Sellers sell iff x ≤ p, and buyers pay E[x | x ≤ p]: buyer value equals seller value. In this model every competitive outcome is efficient, because trade creates no surplus. So "unraveling to the worst type" is automatic and carries no welfare loss, even though the welfare loss is the point of Akerlof. In Akerlof's version, buyer value is (3/2)·x and qualities are uniform on {1,2}. Then p = 9/4 with both qualities trading is an equilibrium (p = 1.5·E[x|x≤p] = 2.25 ≥ 2). `IsLemonsEq F (9/4)` is false, and the file can't express this (sanity test S6, sorry). A generalization would use a seller reservation r(x) ≤ buyer value b(x).

### 7. Screening: monotonicity assumed; downward distortion missing
`isOptimalMenu_binding` and `noDistortionAtTop` take `v qL ≤ v qH` as a hypothesis. The textbook derives it. There is no statement that qL is distorted *downward* relative to the efficient level, or that the H type earns a positive rent (θH−θL)v(qL). In the file's own example, qL = 1/4 while the efficient level is 1/2. That fact is never stated as a theorem.

### 8. Persuasion: message bound
`exists_optimal_signal` uses |Ω|+2 messages. KG show that min(|A|,|Ω|) suffices, and the Carathéodory/concavification argument gives |Ω|. This is minor.

### Things checked and found fine
- Nash bargaining. Weak Pareto with SYM, INV and IIA still forces Nash: the symmetric convex hull of S ∪ reflect(S) is compact and lies inside {s₁+s₂ ≤ 2}. All four axioms are shown satisfiable (`nashSol_axioms`).
- Persuasion concavification. `le_V`, `V_concave` and `V_le_of_concave` together say V is the smallest concave majorant. The prosecutor numbers match KG.
- Spence. I verified all four PBE condition theorems by hand, including that μ stays in [0,1].
- `uscOn_mul`, `Splitting.joint` (μ₀ ω = 0 branch), and `noDistortionAtTop` when pL = 0: no counterexample found.
