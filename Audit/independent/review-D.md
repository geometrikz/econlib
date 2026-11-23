# Statement review: Macro/DP and Macro/Growth (Ramsey, Lucas, AK, Romer)

Reviewer D. Inputs: the statement files under `/home/user/rv/in/EconLean/` only; Lean was not run.
References: SLP = Stokey–Lucas–Prescott (1989); Acemoglu (2009); LS = Ljungqvist–Sargent.

**Bottom line.** I found no theorem that is false as stated, and no hypothesis set that cannot be satisfied. Brock–Mirman, the RCK `sqrtExample`, the DP `Examples`/`StochasticExamples` and the Lucas example all instantiate the headline theorems non-trivially. The problems are of three kinds:
- **Weaker than the textbook:** the Ramsey convergence result and Doeblin.
- **Stipulated, not derived:** the Romer equilibrium growth rate.
- **Coverage gaps:** stochastic DP beyond the Bellman equation; the continuous-time RCK model; Lucas with physical capital.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `blackwell`, `blackwell_fixedPoint` | DP/Blackwell | SLP Thm 3.3, 3.2 | faithful with documented deviation | Stated on `X →ᵇ ℝ` (bounded continuous) instead of B(X). Monotonicity, discounting, conclusion and a-priori bound are correct. |
| `IsFeasiblePlan`, `partialPayoff` | DP/SequenceProblem | SLP §4.1 Π(x₀), u_n | faithful | |
| `IsOptimalValue` | DP/SequenceProblem | SLP v* (eq. 4.? sup) | faithful with documented deviation | Requires the sup to be attained by a plan with convergent payoffs. When the sup is not attained, no `w` qualifies (test §4). |
| `IsOptimalPlan` | DP/SequenceProblem | SLP "u(x*) = v*" | faithful with documented deviation | Uses the catching-up criterion (limsup (Pₙ(x′) − Pₙ(x)) ≤ 0). This equals SLP when payoffs converge. |
| `IsOptimalValue.unique / .isOptimalPlan / .tendsto_of_isOptimalPlan` | DP/SequenceProblem | — | faithful | Checked by hand. |
| `telescope`, `partialPayoff_add_le/_eq`, `IsFeasiblePlan.mem` | DP/SequenceProblem | — | faithful | Algebra checked. |
| `verification` | DP/SequenceProblem | SLP Thm 4.3 | faithful | Its one-sided limit conditions are weaker hypotheses than SLP's lim βⁿv(xₙ)=0. |
| `tendsto_zero_of_le_mul_add_pow` | DP/SequenceProblem | — | faithful | True even for r<0. |
| `verification_of_lowerBound` | DP/SequenceProblem | SLP §4.4-style (unbounded returns) | faithful | Checked: sₙ=(Pₙ−v₀)⁺ satisfies sₙ₊₁ ≤ (1−1/b)sₙ + (|a|/b)βⁿ, so the statement is true. |
| `euler_transversality(_along)` | DP/SequenceProblem | SLP Thm 4.15 | faithful with documented deviation | Concavity + differentiability are supplied as a supergradient inequality with abstract linear maps. Only sufficiency is stated. Necessity of Euler/TVC is a gap (§G). |
| `DynProg` structure | DP/Bellman | SLP Assump. 4.3–4.4 | faithful with documented deviation | F must be continuous on all of X×X, not just on the graph A. This is harmless because any continuous u on ℝ₊ can be extended. Bounded returns only. |
| `contracting`, `value`, `bellman_equation`, `value_unique`, `iterate_converges` | DP/Bellman | SLP Thm 4.6 | faithful | Uniqueness is among bounded continuous functions, as in SLP. |
| `policy`, `mem_policy_iff`, `policy_nonempty_compact_uhc`, `continuous_policy_of_singleton` | DP/Bellman | SLP Thm 4.6 (G), Berge | faithful | |
| `payoff`, `summable_payoff`, `payoff_le_value`, `payoff_eq_value_of_policy`, `policy_of_payoff_eq_value`, `principle_of_optimality`, `isOptimalValue_value` | DP/Bellman | SLP Thms 4.2–4.5 (bounded case) | faithful | `tsum` junk is ruled out because summability is proved. In the unbounded case, SLP 4.2 ("v* satisfies FE") is not stated (§G). |
| `value_monotone`, `value_strictMono` | DP/Bellman | SLP Thm 4.7 | faithful | |
| `ConvexGraph`, `StrictlyConcaveReturn`, `ConcaveFn`, `StrictlyConcaveFn` | DP/Concavity | SLP Assump. 4.7, 4.8 | faithful | Strictness only when x≠x′, exactly as in SLP 4.7. |
| `extendS` | DP/Concavity | — | faithful | Junk value 0 off S. It is used only at interior points or on S. |
| `strictlyConcave_bellmanOp`, `value_strictlyConcave`, `exists_continuous_policy` | DP/Concavity | SLP Thm 4.8 | faithful | |
| `hasDerivAt_of_concaveOn_of_le` | DP/Concavity | SLP Lemma 4.10 (Benveniste–Scheinkman) | faithful | W need not be concave, which is a valid generalization. |
| `DynProg.hasDerivAt_value` | DP/Concavity | SLP Thm 4.11 | WEAK | Scalar state (S ⊆ ℝ) only; SLP 4.11 is for X ⊆ ℝˡ. Its hypotheses (hloc, partial derivative at one point) are otherwise weaker than SLP's. |
| `policy_monotone` | DP/Monotone | Topkis / SLP Ex. 4.? | faithful | Strictly increasing differences + ascending Γ. Proof sketch checked. |
| `orbit_monotone_or_antitone`, `orbit_tendsto_fixedPoint` | DP/Monotone | — | faithful | |
| `BrockMirman.*` (`bellman_*`, `lowerBound`, `brockMirman_value`, `supergradient`, Euler, TVC, `_optimal_of_euler`) | DP/BrockMirman | SLP §2.?, LS ch.3 | faithful | A and B match the textbook. Euler and TVC checked by hand. Γ requires c>0 and k>0, the standard interior setup with log utility. |
| `IsStochastic`, `Distributions`, `IsInvariant`, `exists_invariant`, `l1Dist_*` | DP/MarkovChain | SLP §11.1 | faithful | |
| `doeblin` | DP/MarkovChain | SLP Thm 11.4 (Doeblin) | WEAK | Requires **every** one-step entry Q z z′ ≥ ε>0. Doeblin's condition allows N-step, single-column/minorizing-measure bounds. Ergodic chains with zero entries are excluded (test §3). |
| `StochDynProg` + `bellman_equation`, `value_unique`, `iterate_converges`, `policy_*` | DP/Stochastic | SLP Thm 9.6 | faithful with documented deviation | Finite shock space only (SLP: general Z, Feller Q). |
| SLP ch. 9 beyond 9.6 | DP/Stochastic | SLP Thms 9.2–9.5, 9.7–9.10 | WEAK (coverage gap) | Missing: sequence problem with contingent plans / principle of optimality, and the stochastic concavity, monotonicity and differentiability results. |
| `StochExample.*` | DP/StochasticExamples | — | faithful | Non-vacuity witness. |
| `RCKModel` | Growth/Ramsey | SLP ch. 6 / Acemoglu ch. 6 (discrete) | faithful with documented deviation | Discrete time, f includes undepreciated capital, no δ/n/g, bounded u (log excluded), no Inada. |
| `value_strictMono`, `convexGraph`, `strictlyConcaveReturn`, `exists_monotone_policy` | Growth/Ramsey | SLP Thms 4.7, 4.8, 6.? | faithful | Checked: F has strictly increasing differences via `increment_lt`. |
| `optimal_capital_converges` | Growth/Ramsey | SLP §6.1 / Acemoglu Prop. 6.? (global stability) | WEAK | The limit `kinf` is only *some* fixed point of g. g 0 = 0 always (test §2). Nothing excludes kₜ→0 for k₀>0, and no link is made to k* or to the MGR. |
| `modified_golden_rule`, `steady_state_of_modified_golden_rule`, `modified_golden_rule_unique` | Growth/Ramsey | Acemoglu eq. (6.?) β f′(k*) = 1 | faithful | Checked: k<kbar follows from k<f k, Euler sufficiency gives the converse, and strict concavity gives uniqueness. |
| "Ramsey–Cass–Koopmans" in continuous time | Growth/Ramsey | Acemoglu ch. 8 | WEAK (coverage gap) | Missing: continuous-time Euler ċ/c=(f′−δ−ρ)/θ, saddle-path stability, and MGR f′(k*)=ρ+δ+θg. |
| `Lucas.Economy`, `planU`, `privU`, `IsEquilibrium`, `IsEfficient` | Growth/Lucas | Lucas (1988) §4 | faithful with documented deviation | Stylized model: no physical capital, log utility, discrete time. Output = A u h h̄^γ. |
| `phi_le`, `privOptimal`, `isEquilibrium_iff`, `isEfficient_iff`, `uStar_comparison`, `lucas` | Growth/Lucas | Lucas (1988): eq. underinvests when γ>0 | faithful (within stylized model) | uStar formulas checked. `hint` ⇔ interior u ≤ 1. The BGP growth factor 1+B(1−u*) is implicit and not stated as a BGP theorem. |
| `AK.kpath`, `kpath_eq`, `growthRate_eq`, `tendsto_atTop` | Growth/AK | Acemoglu §11.1 (Solow-AK) | faithful | `tendsto_atTop` is one direction only (minor). |
| `AK.Plan`, `optimal_finite`, `optimal`, `cstar_strictMono_iff` | Growth/AK | LS cake-eating / Acemoglu §11.1 (θ=1) | faithful with documented deviation | Log utility only. Checked the finite-horizon slack β^T/(1−β), using −log(1−x) ≤ x/(1−x). |
| Romer static block (`demand*`, `monopoly_price`, `freeEntry_iff`, `xPlan_gt`, `netOutput_xPlan`, `planner_static`) | Growth/Romer | Acemoglu §13.1 (lab-equipment) | faithful | Demand, markup 1/(1−a), π=aL, r=ηaL all check out. |
| `PlannerPlan`, `planner_optimal`, `plannerPlan_*` | Growth/Romer | Acemoglu Prop. 13.? | faithful with documented deviation | The planner is restricted to symmetric x across varieties, and symmetry is not proved optimal. |
| `eulerGrowth`, `eulerGrowth_lt_optimal`, `eulerGrowth_strictMono_L` | Growth/Romer | Acemoglu Props. 13.1–13.3 | WEAK | The equilibrium growth factor is *defined* as β(1+ηaL); no decentralized equilibrium is defined or solved (test §5). The comparison "eq < optimal" is therefore a comparison of two formulas. The model is the lab-equipment variant, not Romer (1990)'s knowledge-spillover model with H_A. |

## Detailed findings

### F1. `RCKModel.optimal_capital_converges` (Ramsey.lean) is WEAK
- **What is stated:** monotone convergence of the optimal capital path to *some* fixed point `kinf` of the policy.
- **Why that is weak:** because `f 0 = 0`, Γ(0) = {0}, so g(0) = 0 for every model (proved in `sanity_tests.lean` §2). The statement is therefore compatible with kₜ → 0 for every k₀ > 0.
- **Canonical result:** for k₀ > 0, kₜ → k* > 0 with βf′(k*) = 1 (SLP ch. 6; Acemoglu Thm 6.? for discrete time).
- **What would close it:** the MGR theorems characterize interior positive fixed points. Still missing are (i) kinf > 0 for k₀ > 0, which needs an Inada-type assumption βf′(0⁺) > 1 that `RCKModel` lacks, and (ii) kinf < f(kinf).
- **Effect on the example:** in `sqrtExample` a positive steady state 1/16 is exhibited, but convergence *to it* is not.

### F2. `doeblin` (MarkovChain.lean) is WEAK
- **What is stated:** the hypothesis is `∀ z z', ε ≤ Q z z'`, so every one-step transition must be positive.
- **Canonical result:** Doeblin's condition (SLP §11.? Thm 11.4; Meyn–Tweedie) is ∃N, ε, j with Q^N(z, j) ≥ ε for all z, or a minorizing measure.
- **Counterexample:** Q = [[0,1],[½,½]] is stochastic, irreducible and aperiodic, has Q² > 0, and has a unique attracting invariant distribution (1/3, 2/3). Yet ¬∃ε>0, ∀z z′, ε ≤ Q z z′ (proved in the tests, §3).
- **Effect:** the theorem name overstates coverage; the N-step version is a one-line corollary that is missing.

### F3. Stochastic DP (Stochastic.lean) covers only SLP Thm 9.6, with finite Z
- **Present:** the functional equation (existence, uniqueness, iteration) and the Berge policy correspondence.
- **Missing parts of SLP ch. 9:**
  - The connection to the stochastic sequence problem (contingent plans, measurability, SLP Thms 9.2–9.5): there is no `payoff` or `principle_of_optimality` analogue.
  - Concavity and strict concavity of v, single-valued continuous policy (9.8).
  - Monotonicity (9.7) and differentiability (9.10).
- **Also missing:** the invariant distribution for the joint (x, z) process (SLP ch. 12).
- **Assessment:** this is not wrong, but a reader of "stochastic DP" would expect these.

### F4. Romer.lean: the equilibrium is stipulated
- **What is stated:** `eulerGrowth := β * (1 + rEq)` with `rEq := η a L`, which is the textbook answer typed in.
- **What is missing:** a definition of a decentralized equilibrium (household optimality given r, monopolist pricing, free entry, resource constraint) and a theorem that its consumption growth factor equals `eulerGrowth`.
- **Consequence:** `eulerGrowth_lt_optimal` compares two formulas. It does not compare an equilibrium allocation with the optimum.
- **Two further deviations:**
  - `PlannerPlan` restricts the planner to symmetric machine use `x t` across varieties.
  - The model is Acemoglu's lab-equipment variant (§13.1). Romer (1990)'s original knowledge-spillover model with researchers H_A and growth g = (δH − Λρ)/(Λσ + 1) is not covered.

### F5. Lucas.lean is a stylized model, not Lucas (1988)
- **What is modeled:** no physical capital, output A·u·h·h̄^γ consumed entirely, log utility, discrete time.
- **What holds:** within that model the results are correct. I checked u*_priv = (1−β)(1+B)/B, u*_plan = (1+B)/(B(1+κ)) with κ=(1+γ)β/(1−β), and the comparison.
- **What is not covered:** the canonical BGP of Lucas (1988) with k, σ and the ratio k/h, and an explicit statement that h, y, c grow at the common rate 1+B(1−u*). This should be documented as a deviation.
- **Minor:** `IsPrivOptimal` and `IsEfficient` compare only against plans with summable utility. That is harmless, because non-summable plans diverge to −∞ (utility is bounded above by a summable sequence).

### F6. `IsOptimalValue` / `IsOptimalPlan` (SequenceProblem.lean): documented deviations
- **`IsOptimalValue w`:** requires a plan whose partial payoffs converge to w, so it means "the max exists and equals w". SLP's v* is a sup. In the counterexample X=ℝ, Γ≡(0,1), F x y = y, β=0, v* = 1 but no `w` satisfies the predicate (tests §4, proof sketched).
- **`IsOptimalPlan`:** is catching-up optimality. It equals SLP's notion when payoffs converge, which they do in every use here.
- **Recommendation:** document both, or rename to `IsAttainedOptimalValue`.

### F7. Scope restrictions in the DP core
- **`DynProg.hasDerivAt_value`:** S ⊆ ℝ only. SLP Thm 4.11 is multivariate.
- **`blackwell`:** stated on bounded *continuous* functions, whereas SLP Thm 3.3 is on B(X). It cannot be applied to operators with discontinuous returns.
- **`DynProg.F_continuous`:** F must be continuous on all of X×X rather than on the graph. Harmless by extension.

### G. Coverage gaps the names suggest are covered
- **Principle of optimality, unbounded case:** SLP 4.2 (v* satisfies the FE) and 4.4 are not stated. Only the bounded case (`principle_of_optimality`) and verification (4.3-type) are.
- **SLP Thm 4.9:** convergence of policies gₙ → g of the value-iteration iterates is missing.
- **Euler equations:** only sufficiency (SLP 4.15) is stated. Necessity of interior Euler equations and TVC (Kamihigashi 2002; Ekeland–Scheinkman) is missing.
- **Continuous-time Ramsey–Cass–Koopmans (Acemoglu ch. 8):** absent. The Ramsey file is discrete-time optimal growth.
- **AK:** log utility only. The CRRA growth formula g = (A − δ − ρ)/θ is missing.

## Non-vacuity checks performed (by hand)
- **BM** (α=1/3, β=1/2, k₀=1): all hypotheses hold (tests §1).
- **RCK `sqrtExample`:** satisfies every structure field. The MGR k*=1/16 is checked: f′(1/16)=2 and β=1/2.
- **Lucas** (A=B=γ=1, β=9/10): `hint` holds.
- **`Examples.P` and `StochExample.P`:** satisfy the strict-monotonicity and concavity hypotheses non-trivially.
- **`euler_transversality`:** BM supplies a non-degenerate instance (`brockMirman_optimal_of_euler`).
