# Statement review: Macro targets (reviewer N)

Scope: NK/{BlanchardKahn, ThreeEquation, Shocks, StickyInformation}, Fiscal/ChamleyJudd, HA/Aiyagari, DP/{Doeblin, ParamInvariant, MarkovChain}, Consumption/{PIH, Precautionary}, BaqaeeFarhi, ProductionNetworks, Climate/SocialCostCarbon, Growth/Romer, Labor/HosiosDiscounted.
I read only files under `/home/user/rv4/in/`, plus one web search to confirm how GHKT (2014) normalise the SCC. Lean was not run.

## Summary table

| Declaration | File | Reference | Verdict | One-line reason |
|---|---|---|---|---|
| `NK.DeterminateN`, `determinateN_iff` | NK/BlanchardKahn | Blanchard–Kahn (1980); Galí Ch. 3 App. | **WEAK** (coverage gap) | Proves only the all-jump case (zero predetermined variables): determinate iff every eigenvalue satisfies \|μ\|>1. The headline "number of unstable eigenvalues = number of jump variables" is never stated. There is no predetermined block and no rank condition. |
| `not_determinate_of_eigenvalue`, `isUnit_cplx`, `norm_lt_of_mem_spectrum` | NK/BlanchardKahn | lemmas | faithful | Correct, including the unit-root case. |
| `NK.Determinate`, `determinate_iff` (2×2) | NK/ThreeEquation | Galí Ch. 3 appendix; LS | faithful with documented deviation | Under det>0, the 2×2 Schur–Cohn test is correct. It too treats all variables as jump variables, which is right for the 3-equation model. |
| `Model.IsEquilibrium`, `forward`, `isEquilibrium_iff` | NK/ThreeEquation | Galí Ch. 3 (IS, NKPC, Taylor rule) | faithful with documented deviation | Deterministic perfect-foresight deviations with no r^n. I checked the forward matrix by hand and it matches. |
| `Model.taylor_principle` | NK/ThreeEquation | Galí Ch. 3; Bullard–Mitra (2002) | faithful | I re-derived it from det/trace: κ(φπ−1)+(1−β)φx>0. |
| `taylor_principle_strict` | NK/ThreeEquation | Galí | faithful | |
| `divine_coincidence`, `zero_isShockEquilibrium` | NK/Shocks | Galí Ch. 4–5; Blanchard–Galí (2007) | faithful | The rule tracks r^n with u=0, so the only bounded equilibrium is zero. |
| `no_firstBest_of_costPush` | NK/Shocks | Galí Ch. 5 | faithful (trivial) | Follows in one line from the NKPC at date t. |
| `discretion_static`, `discretion_unique` | NK/Shocks | Galí Ch. 5 (discretion, AR(1) u) | faithful | Formulas match Galí, with α_x = lam. |
| `StickyInfo.IsEquilibrium`, `output`, theorems | NK/StickyInformation | Mankiw–Reis (2002) | faithful with documented deviation | This is a two-vintage simplification, not MR's full distribution over information vintages with E_{t−j}. The qualitative results hold. |
| `ChamleyJudd.IsRamseyFOC`, `chamley_judd` | Fiscal/ChamleyJudd | Chamley (1986), Judd (1985); LS Ch. 16; Straub–Werning (2020) | **WEAK** (assumes the key step) | Both Euler equations are assumed, including the planner's pre-tax Euler for W_c, which is the economic content of Chamley–Judd. No Ramsey problem appears, so the theorem is 3 lines of limit algebra about arbitrary sequences. The convergence assumption is explicit (good, per Straub–Werning), but it is stated on unanchored sequences. |
| `ratio_unbounded`, `wedge_unbounded` | Fiscal/ChamleyJudd | Judd/SW-style wedge argument | faithful (algebra) | Correct but carries no Ramsey content. |
| `ParamSavings`, `StochSavings` | HA/Aiyagari, StochSavings | Aiyagari (1994); LS Ch. 18 | **WEAK** | Assets are truncated to [0, kbar] by an arbitrary box. The household's return need not depend on θ = r, as the `noReturn` instance shows. |
| `exists_asset_market_clearing` | HA/Aiyagari | Aiyagari (1994), Fig. II | **WEAK** (assumes the key step) | `hhi` assumes that supply ≥ demand at r_hi, which is the hard part of Aiyagari (supply → ∞ as r ↑ 1/β−1). Kd is an arbitrary continuous function, not F_K−δ, and wages are not linked. What remains is the IVT. **r < 1/β−1 is not stated anywhere.** |
| `continuous_aggregate` | HA/Aiyagari | SLP Thm 12.13 application | faithful | Requires uniqueness, as it should. |
| `exists_stationary_of_policy`, `UniqueStationary` | HA/Aiyagari | SLP Ch. 12 (Feller + compact) | faithful | |
| `doeblin_step`, `doeblin_convergence`, `doeblin_unique` | DP/Doeblin | SLP Ch. 11 (Thm 11.12 Cond. M), Meyn–Tweedie uniform ergodicity | faithful with documented deviation | Uses one-step minorization K(x,·) ≥ εφ. This is stronger than SLP's Condition D and Condition M. Convergence is stated only for N=1. |
| `unique_invariant_of_pow` | DP/Doeblin | SLP Cond. M / Doeblin N-step | **WEAK** | The N-step version gives only uniqueness. There is no N-step geometric convergence and no existence. SLP's Condition D, which is weaker and allows several ergodic sets, is not formalized. |
| `doeblin`, `doeblin_pow` | DP/MarkovChain | SLP **Thm 11.4** | **WEAK** | SLP 11.4 needs only *one column* of Π^N to be positive. The Lean version needs *every* entry of Q^N ≥ ε. Counterexample: Q=[[1,0],[1,0]] satisfies SLP 11.4 but not the hypothesis. |
| `exists_invariant`, `l1Dist_contract` | DP/MarkovChain | SLP Thm 11.1, Dobrushin | faithful | |
| `invariant_of_tendsto` … `continuous_integral_invariant` | DP/ParamInvariant | SLP Thm 12.13 | faithful | Joint Feller, compact metrizable X, uniqueness. |
| `PIH.Problem`, `euler`, `isOptimal_of_euler` | Consumption/PIH | LS Ch. 17; Hall (1978) | faithful with documented deviation | Finite horizon on a finite tree, with c unrestricted in ℝ (right for quadratic utility). |
| `PIH.Problem.hall` | Consumption/PIH | Hall (1978) Cor. 1 | faithful | E_t c_{t+1} = c_t under βR=1 and quadratic utility. The PIH consumption *function* (annuity value of wealth) is not stated (coverage gap). |
| `Precautionary.*`, `precautionary`, `precautionary_strict` | Consumption/Precautionary | Leland (1968), Sandmo (1970), Kimball (1990) | faithful | Convex u′ is the C³-free form of u‴≥0. The strict version needs nondegenerate risk and strict convexity. |
| `BaqaeeFarhi.Economy`, `logY` | BaqaeeFarhi | Baqaee–Farhi (2019, Ecta) | **WEAK** | This is a single-layer CES aggregator over TFP shocks, not a network. **At θ = 1, logY ≡ 0 (junk: 0⁻¹ = 0)**, not the Cobb–Douglas Σ b_i x_i. |
| `hasDerivAt_logY` | BaqaeeFarhi | Hulten first order | faithful | |
| `complements_le_hulten`, `substitutes_ge_hulten`, `complements_asymmetry` | BaqaeeFarhi | BF (2019) Sect. on nonlinearity | faithful (global inequalities) | |
| *(missing)* second-order formula d²logY = (θ−1)Var_λ(d) | BaqaeeFarhi | BF (2019) Prop. 2/3 | **coverage gap** | The headline "second-order" result is not stated. Only sign inequalities are. |
| `ProdNetworks.Network`, `IsPriceSystem`, `k`, `logGDP` | ProductionNetworks | Acemoglu et al. (2012); Long–Plosser | faithful | The Cobb–Douglas unit-cost log formula is right. 0·log 0 = 0 is the correct convention here. |
| `hulten`, `isSales_iff`, `domar_*`, `aggVar*`, `star_*` | ProductionNetworks | Hulten (1978) for CD; Acemoglu–Carvalho–Ozdaglar–Tahbaz-Salehi (2012) | faithful | `_hz` is unused (with z ≤ 0 the identity holds through junk log, which is harmless). |
| `Climate.Params.scc`, `scc_eq` | Climate/SocialCostCarbon | GHKT (2014) Prop./eq. for Λ^s | **MISMATCH** | The Lean SCC is γ·(1−s)·Y₀·kernel, i.e. γ·C₀·kernel. GHKT's is γ·Y₀·kernel ("as a proportion of GDP"). The gap comes from making Y exogenous: lost savings never reduce future capital, so the 1/(1−αβ) capital channel that cancels the (1−s) is missing. Off by a factor (1−s). |
| `kernel`, `tsum_kernel`, `kernel_mono`, `kernel_unbounded` | Climate/SocialCostCarbon | GHKT | faithful | |
| `Romer.Economy`, `demand_optimal`, `monopoly_price` | Growth/Romer | Acemoglu Ch. 13.1 (lab-equipment) | faithful | |
| `rEq`, `freeEntry_iff`, `household_optimal`, `eulerGrowth` | Growth/Romer | Acemoglu Prop. 13.1 | **WEAK** | Equilibrium growth is assembled from pieces, not derived from an equilibrium. `rEq` is *defined* as ηaL, and free entry uses steady-state V=π/r. The household budget (`AK.Plan`) has **no wage income** and no asset-market clearing (assets = N/η). No `IsEquilibrium` object is shown to grow at `eulerGrowth`. |
| `planner_optimal`, `eulerGrowth_lt_optimal` | Growth/Romer | Acemoglu Prop. 13.2 | faithful with documented deviation | The planner is restricted to symmetric x per period, which is standard. |
| `Discrete.IsSearchEqm`, `hosios` (discounted) | Labor/HosiosDiscounted | Hosios (1990); Pissarides Ch. 8; LS Ch. 28 | faithful | Probabilities ≤ 1 are imposed in both the equilibrium and the planner's feasible set, and the timing is consistent. The theorem says nothing when the Hosios θ has a rate >1 (hypotheses unsatisfiable), which is acceptable. |

## Details on the non-faithful items

### 1. SocialCostCarbon `scc_eq`: MISMATCH (factor 1−s)
`scc = −C₀ · dW/de`, with `W = Σ βʲ log((1−s)·Ỹ_j·exp(−γ(S_j + remain_j e)))`, where Ỹ is exogenous. This gives `scc = γ(1−s)Y₀·kernel`. In GHKT (2014) the marginal externality damage is Λˢ_t = γ·Y_t·[φL/(1−β) + (1−φL)φ0/(1−(1−φ)β)], "as a proportion of GDP".
In GHKT the damage also cuts saving and therefore K_{t+1}. That adds a factor 1/(1−αβ) to the utility loss, which exactly offsets u′(C₀)⁻¹ = (1−αβ)Y₀.
Example: s = 0.3 understates GHKT's SCC by 30%. See `sanity_tests.lean`, `scc_ne_ghkt`.
Fix: either define scc in output units with the capital channel, or state SCC = γ·Y₀·kernel and model K.

### 2. ChamleyJudd `chamley_judd`: WEAK (assumes the economics)
`IsRamseyFOC` is just two Euler equations about arbitrary sequences `uc Wc r τ`. The second, `Wc t = β Wc(t+1)(1+r(t+1))`, is the planner's first-order condition in primal form. Deriving it from a Ramsey problem (with W = u + Φ·(implementability term)) *is* Chamley–Judd. Given both equations and convergence to positive limits, τs = 0 follows by dividing limits.
Example: uc ≡ Wc ≡ 1, r ≡ 1/β−1, τ ≡ 0 satisfies everything. So does any pair of sequences unrelated to any economy (see `sanity_tests.lean`).
Straub–Werning: the convergence assumption *is* explicit (`hucs`, `hWcs`, `hWc`, `hr`, `hτ`). But because Wc is not tied to multipliers, the theorem cannot express SW's point that the multiplier-weighted marginal utility need not converge to an interior limit. `ratio_unbounded` is the right kind of companion lemma, but it too concerns unanchored sequences.

### 3. Aiyagari `exists_asset_market_clearing`: WEAK; r < 1/β−1 absent
- `hhi` assumes that at r_hi the stationary supply is ≥ Kd(r_hi), for every invariant policy. In Aiyagari this is the content: precautionary supply explodes as r → 1/β−1 (Chamberlain–Wilson). `hlo` is trivial because supply ≤ kbar by construction.
- `Kd` is any continuous function, not capital demand from F_K(K,L)−δ = r, and the wage does not enter h.
- `θ` does not have to enter h at all. `noReturn` (h independent of θ and k) still yields an "equilibrium r", so the theorem is the intermediate value theorem.
- There is no statement of r* < 1/β−1, and none of supply → ∞. With assets capped at kbar, the latter is impossible to state.
- The truncation to [0, kbar] is an ad hoc upper bound. Aiyagari proves an endogenous upper bound when βR<1.

### 4. MarkovChain `doeblin_pow`: WEAK vs SLP Thm 11.4
SLP 11.4: Π has a unique ergodic set with no cyclically moving subsets iff, for some N, *some column* of Π^N has all entries positive. The Lean version requires *all* entries of Q^N ≥ ε.
Q = [[1,0],[1,0]] (state 0 absorbing) has a unique invariant distribution (1,0) and a positive column. Yet (Q^N)₀₁ = 0 for all N, so `doeblin_pow` can never be applied (`sanity_tests.lean`, `slp114_not_covered`).

### 5. Doeblin (measure) `unique_invariant_of_pow`: WEAK
The N-step minorization gives only uniqueness. There is no N-step convergence (`doeblin_convergence` is 1-step) and no existence of an invariant measure. SLP's actual "Condition D" (φ(A) ≤ ε ⇒ P^N(x,A) ≤ 1−δ) allows finitely many ergodic sets and is not formalized. The file's minorization is strictly stronger, which is acceptable if documented.

### 6. BlanchardKahn: coverage gap
`DeterminateN M` means every bounded orbit of the *whole* state is zero. That is the case with zero predetermined variables. The canonical BK statement, with n_x predetermined variables pinned by initial conditions and n_y jump variables (unique bounded solution iff #|μ|>1 equals n_y, plus a rank condition), is absent.
Example: diag(1/2, 2) with x predetermined is BK-determinate (saddle path), yet `¬ DeterminateN` holds for it (`sanity_tests.lean`, `bk_saddle_not_covered`).

### 7. BaqaeeFarhi: WEAK and missing second order
`logY = (θ−1)⁻¹ log S`. At θ = 1 Lean gives logY ≡ 0. The theorems exclude θ = 1, so no false result follows, but the Cobb–Douglas benchmark (where Hulten is exact) cannot be expressed (`sanity_tests.lean`, `bf_logY_theta_one`).
The BF headline (2019, Prop. 2: d² log Y/d log A_i² = dλ_i/d log A_i with CES (θ−1)·Var term) is not stated. The model is one CES layer, with no input–output network.

### 8. Romer: equilibrium growth not derived
`rEq := η a L` is a definition. `freeEntry_iff` checks η·(π/r) = 1 at the monopoly profit, which assumes steady-state V = π/r. The household problem `AK.Plan (1+rEq) k₀` has **no labor income** (a_{t+1} = (1+r)a_t − c_t). No asset-market clearing (household assets = N·V = N/η) or goods-market clearing is imposed.
The growth rate β(1+r) follows from the Euler equation either way, so the number is right. But there is no `IsEquilibrium` predicate that is proved to imply growth `eulerGrowth`. It is "defined", not "derived".

### Minor
- StickyInformation: two information vintages, not MR's geometric distribution of vintages E_{t−j}p*_t. This is a documented simplification and the qualitative claims follow.
- PIH: finite horizon, and the PIH consumption function is not stated. `hall` allows γ<0 (convex u), but the theorem is still true because it assumes optimality.
- ProductionNetworks `hulten`: positivity hypotheses `_hz`, `_hz'` are unused. That is harmless.
