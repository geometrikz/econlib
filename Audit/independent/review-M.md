# Statement review M: econometrics (TWFE/Bacon, Gauss–Markov, extremum, GMM, BLP, SVAR) and finance (Lucas tree, sequential markets)

Scope: the 8 target files under `in/EconLean/`. I only read statement files and the definitions they depend on (TWFE.lean, OLS.lean, GMM.lean, SVAR.lean, AssetPricing.lean, MarkovChain.lean). Lean was not run; the semantics are worked out by hand.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `dm`, `pairNum`, `pairVar`, `pairCoef`, `baconWeight` | Causal/GoodmanBacon | Goodman-Bacon (2021) eq. (10)–(11) | faithful with documented deviation | Weights are per ordered pair of units, not per timing group. The definitions hold for any real-valued D, not only staggered binary D. `x/0=0` junk occurs only where the weight is 0. |
| `isTWFE_coef`, `eps_eq_dm`, `sum_centered_mul_eq_pairs`, `sum_eps_mul_eq_pairs` | GoodmanBacon | FWL | faithful | Checked by hand. |
| `baconWeight_nonneg` | GoodmanBacon | GB Thm 1 (weights ≥ 0) | faithful (junk-assisted) | Holds unconditionally only because `x/0 = 0`. |
| `sum_baconWeight` | GoodmanBacon | GB Thm 1 (weights sum to 1) | faithful | Needs `hv`. `hden` in `goodman_bacon` implies `hv` (sanity test 4). |
| `goodman_bacon` | GoodmanBacon | GB (2021) Theorem 1 | faithful with documented deviation | b = Σ_{g,h} s_gh β̂_gh, where β̂_gh is the 2-unit TWFE coefficient (`pairCoef_eq_twfe`). Correct identity. The timing-group form and the closed-form GB weights (n_k n_l (D̄_k−D̄_l)(1−(D̄_k−D̄_l)) etc.) are not stated. |
| `pairCoef_eq_twfe` | GoodmanBacon | GB §2 | faithful | |
| `pairCoef_indicator` | GoodmanBacon | GB eq. (3) treated vs untreated 2×2 | faithful | Checked: Σ(1_P−p)² = #P·#Pᶜ/T. |
| `pairCoef_split` | GoodmanBacon | GB eq. (6)–(8): β̂_kl = μ β̂^k_kl + (1−μ) β̂^l_kl | faithful | μ = #pre/(#pre+#post) = (1−D̄_k)/(1−(D̄_k−D̄_l)). Matches GB. |
| `Example.bacon_witness` | GoodmanBacon | – | faithful | Same −1/2 as `TWFE.Example.twfe_negative`. |
| `cov`, `secondMoments` | GaussMarkov | Hansen §4 | faithful | Integrals are junk (0) if not integrable, but every theorem assumes `hε`, `hεε`. |
| `unbiased_iff` | GaussMarkov | Hansen Thm 4.x (linear unbiased ⇔ AᵀX = I) | faithful | |
| `cov_linear`, `cov_ols` | GaussMarkov | Hansen Thm 4.2: Var(β̂)=σ²(XᵀX)⁻¹ | faithful with documented deviation | Fixed (non-random) design X instead of conditioning on X. |
| `gauss_markov` | GaussMarkov | Hansen Thm 4.4 / Hayashi Prop 1.1(c) | faithful with documented deviation | Fixed design. `hX` is redundant given `hC` (sanity test 5). Missing: unbiasedness of s², GLS/Aitken. |
| `gaussMarkov_witness` | GaussMarkov | – | faithful | Hypotheses are satisfiable. |
| `extremum_consistent` | Asymptotics/Extremum | Newey–McFadden Thm 2.1 | faithful | Identification, compact Θ, continuous Q₀, ULLN in (outer) probability, approximate maximizer with o_p(1) slack. Correct for any measure. |
| `klDiv_pos_of_identified` | Extremum | NM Lemma 2.2 (information inequality) | faithful | Uses Mathlib's KL for finite measures (=0 iff equal). |
| `mle_unique_max` | Extremum | NM Lemma 2.2 | WEAK | Q₀ is never defined as E ln f(z\|θ). The identity Q₀(θ₀)−Q₀(θ)=KL is assumed (`hgap`). That identity is the substance of the lemma. |
| `mle_consistent` | Extremum | NM Thm 2.5 | WEAK | This is Thm 2.1 with `hgap`. No sample likelihood, no iid, no dominance condition E sup\|ln f\|<∞. ULLN (`hulln`) and continuity of Q₀ are assumed, though Thm 2.5 derives them. |
| `tendstoInMeasure_comp_continuousAt`, `_prodMk`, `_sub_of_eq_near(_off)` | Extremum | CMT / Slutsky (constant limits) | faithful | |
| `tendstoInDistribution_mulVec` | Extremum | Slutsky | faithful | |
| `exists_ball_isUnit_det`, `continuousAt_inv_of`, `measurable_inv_of` | Extremum | – | faithful | |
| `z_estimator_asymptotic` | Extremum | NM Thm 3.1 | WEAK | The mean-value expansion (`hexp`) and H(θ̄)→p H₀ are assumed. No criterion, differentiability, interiority or consistency. It reduces to the CMT (sanity test 3). |
| `z_estimator_gaussian` | Extremum | – | faithful (minor gap) | The sandwich variance H⁻¹ΣH⁻¹ is never stated. Holds for singular H₀ through the junk inverse (degenerate Gaussian). |
| `gram`, `cross`, `gmmA`, lemmas | GMMAsymptotics | – | faithful | |
| `gmm_consistent` | GMMAsymptotics | Hansen Thm 13.x (linear GMM); Hayashi Prop 3.1 | faithful with documented deviation | Linear moments only (σ = Sθ₀ + g). Nonlinear GMM (NM Thm 2.6) is not covered. Needs only GᵀW₀G invertible, not W₀ ≻ 0, which is more general and fine. |
| `gmm_asymptotic_normal` | GMMAsymptotics | Hayashi Prop 3.5; Hansen Thm 13.x | faithful with documented deviation | Linear GMM. The limit is (GᵀW₀G)⁻¹GᵀW₀L. Nothing links Cov(L)=S to `avar`. |
| `gmm_limit_gaussian` | GMMAsymptotics | – | faithful (minor gap) | Says Gaussian but gives no covariance. |
| `avar_eq_sandwich` | GMMAsymptotics | Hansen eq. for V = (G'WG)⁻¹G'WΩWG(G'WG)⁻¹ | faithful | Holds since (Aᵀ)⁻¹=(A⁻¹)ᵀ always in Mathlib. |
| (efficient weighting) | GMM.lean (not target) | Hansen Thm 13.x | – | `avar_sub_posSemidef` is in the non-target file. The J-test is absent (coverage gap). |
| `share`, `outsideShare`, `berry_inversion`, `share_surjective`, `share_injective` | Structural/BLP | Berry (1994) logit inversion δ_j = ln s_j − ln s_0 | faithful | Log arguments are positive, so there is no junk. |
| `share_set_lt`, `exists_set_share_lt` | BLP | Berry–Gandhi–Haile (2013)-style connected-substitutes step | faithful | Checked: argmax set K, M>0, and the outside good gives strictness. |
| `mixedShare` | BLP | BLP (1995) random-coefficient shares | faithful with documented deviation | Finite types. Weights are not required to sum to 1 (sanity test 6b). |
| `mixedShare_injective` | BLP | Berry (1994) Thm / BLP (1995) App. I (uniqueness) | WEAK (coverage) | Only uniqueness is stated. The **contraction mapping** (BLP App. I) and **existence** of δ for every s in the open simplex are missing, though the file's headline is "contraction/inversion". |
| `mixedShare_unit`, `mixed_witness` | BLP | – | faithful | |
| `longRunMultiplier`, `IsLongRunRecursive` | TimeSeries/SVARRestrictions | Blanchard–Quah (1989) | faithful | C(1)=(I−ΣA_i)⁻¹; C(1)B lower-triangular with positive diagonal. |
| `posDef_congr`, `longRun_unique`, `longRun_existsUnique`, `blanchardQuah` | SVARRestrictions | BQ (1989); Kilian–Lütkepohl ch. 10 | faithful | Checked by hand via Cholesky uniqueness. |
| `obsEquiv_iff_orthogonal` | SVARRestrictions | Rubio-Ramírez–Waggoner–Zha (2010) | faithful | |
| `SignOK`, `identifiedSet`, `identifiedSet_eq`, `sign_restrictions_set_identify` | SVARRestrictions | Uhlig (2005) | faithful | Weak sign inequalities. A zero sign coefficient makes a restriction vacuous (harmless). |
| (order/rank counting) | SVARRestrictions | RWZ (2010) Thm 1; K–L ch. 8 | MISMATCH (coverage gap) | No statement of the n(n−1)/2 order condition or of a rank condition, which the headline expects. |
| `expect`, `cov`, `var`, `expect_mul_eq`, `cov_sq_le`, `expect_const`, `var_sub_const` | Finance/LucasTree | – | faithful | `cov_sq_le` holds for any w ≥ 0, not only probability weights. |
| `hj_bound`, `hansen_jagannathan` | LucasTree | Hansen–Jagannathan (1991); Cochrane ch. 5 | faithful | Squared form of \|E R − R_f\| ≤ σ(m)/E(m)·σ(R). |
| `Tree` | LucasTree | Lucas (1978); LS ch. 13 | faithful with documented deviation | u′ is an arbitrary positive function, not derived from a concave u (sanity test 8). Finite Markov states. Equilibrium is defined by the Euler equation; household problem and market clearing c=d are not modelled. |
| `IsPrice`, `isPrice_iff_sdf`, `existsUnique_price`, `price_pos` | LucasTree | LS eq. (13.2.x) | faithful | Unique because β<1 and Q is stochastic. The series formula p=Σβ^j E[u′d]/u′ is not stated (minor gap). |
| `isPrice_log` | LucasTree | LS §13.x (log utility: p = β/(1−β) d) | faithful | |
| `euler_return`, `bondPrice_pos`, `euler_riskFree`, `premium_eq` | LucasTree | Cochrane ch. 1 | faithful | |
| `adBudget`, `SeqBudget`, `seqBudget_adBudget`, `adBudget_seqBudget`, `seqBudget_iff_adBudget`, `complete_iff_budget_eq` | Finance/SequentialMarkets | MWG 19.E; LS ch. 8 (two-period version) | faithful with documented deviation | Two periods, general assets. LS's infinite-horizon Arrow-securities model with natural debt limits is not covered. Both directions of the iff are present. |
| `Economy`, `IsAD`, `IsRadner` | SequentialMarkets | LS §8.4/8.8; MWG 19.D–E | WEAK | Consumption set is all of ℝ×ℝ^σ (no x ≥ 0). With log or √ utility (junk on negatives) **no AD/Radner equilibrium exists** (sanity test 1). |
| `isRadner_of_isAD`, `isAD_of_isRadner`, `exists_isAD_of_isRadner` | SequentialMarkets | MWG Prop 19.E.2; LS §8.8 | faithful with documented deviation | Correct for any U. Asset market clearing ∑h=0 is handled correctly, including with redundant assets. |

## Details for the items that are not faithful

### 1. `Economy` / `IsAD` / `IsRadner` (SequentialMarkets): WEAK, consumption set ℝ^{1+S}

`Economy.U : A → Bundle σ → ℝ` is evaluated on every bundle, and the budget sets have no nonnegativity constraint. This repeats a defect found in earlier reviews ("quantifies over all ℝⁿ instead of the consumption set").

**Counterexample (sanity test 1).** Take one agent with e = (1,(1,1)) and textbook log utility U(y) = log y₀ + Σ_s log y_s. Then `¬ IsAD m x` for *every* m and x. Given any candidate x, the bundle y = (−(|x₀|+2), x₁) costs less than x, and its utility is higher because Mathlib defines `Real.log (−c) = Real.log c`. The same unboundedness argument works for Σ√y_s, because √ is 0 on negatives and a negative position frees up wealth.

**Effect.** The equivalence theorems remain true, since they hold for any U. Even so, every standard CRRA or log economy has an empty equilibrium set, so the theorems apply to such economies only vacuously.

**Fix.** Add a consumption set (x ≥ 0) to both budget notions. The equivalence still holds because the same constraint is imposed on both sides.

### 2. `mle_unique_max`, `mle_consistent` (Extremum): WEAK, they assume the step that makes them MLE results

NM Lemma 2.2 says that Q₀(θ) = E_{θ₀} ln f(z|θ) is uniquely maximized at θ₀ when the model is identified and E|ln f| < ∞. The content is the Jensen/Gibbs inequality applied to the *expected log-likelihood*.

In the Lean statements, Q₀ is an arbitrary function, and `hgap` *assumes* Q₀(θ₀)−Q₀(θ) = KL(P_θ₀‖P_θ). After that, `mle_unique_max` is a corollary of KL > 0 (sanity test 2, where Q₀ := −KL by definition).

`mle_consistent` is `extremum_consistent` plus `hgap`. It does not say that Q_n is the sample log-likelihood, and it assumes iid-free ULLN and continuity of Q₀ instead of deriving them from NM Thm 2.5's dominance condition. Its name overstates what it proves. It is better described as "Thm 2.1 under a KL-identified population objective".

### 3. `z_estimator_asymptotic` (Extremum): WEAK, the mean-value expansion and Hessian convergence are assumed

NM Thm 3.1 derives √n(θ̂−θ₀) →d N(0, H⁻¹ΣH⁻¹) from the following:
- consistency;
- θ₀ interior;
- twice differentiability;
- uniform convergence of the Hessian;
- CLT for the score.

In the Lean statement:
- `S` and `H` are arbitrary random objects.
- `hexp` (S_n + H_n(θ̂−θ₀) = 0 with probability → 1) *is* the FOC plus the mean-value step.
- `hH` assumes H_n →p H₀ directly, which is where consistency and uniform convergence would be used.

Sanity test 3 sets S := −H₀(θ̂−θ₀) and H := H₀. Then `hexp` holds trivially and the theorem is just the CMT. The statement is correct but has little econometric content. The variance formula is never stated (`z_estimator_gaussian` only gives Gaussianity, and it also holds for singular H₀ through the junk inverse 0).

### 4. SVAR counting (SVARRestrictions): MISMATCH / coverage gap

The file is expected to cover "identification counting: n(n−1)/2 restrictions, order vs rank". There is nothing of the kind. The file covers:
- recursive and long-run (Blanchard–Quah) exact identification, both correct;
- observational equivalence via orthogonal Q;
- sign-restriction set identification.

Two results are missing:
- **Order condition:** at least n(n−1)/2 restrictions are necessary.
- **Rank condition (RWZ 2010 Thm 1):** without it, the order condition is not sufficient.

Sanity test 7 gives the standard counterexample. For n = 3, three zero restrictions all placed in column 0 meet the count, yet no B with BBᵀ = I satisfies them, so the restrictions are inconsistent rather than identifying.

### 5. BLP contraction (BLP): WEAK, the contraction mapping and the existence half are missing

What is stated:
- the logit inversion (Berry 1994), including existence (`share_surjective`), uniqueness and the closed form;
- for random coefficients, only **injectivity** (`mixedShare_injective`).

What is missing:
- the BLP (1995, App. I) contraction T(δ) = δ + ln s − ln σ(δ), whose modulus is < 1 in sup norm;
- the existence of δ solving σ(δ) = s for every s in the open simplex.

The file's description ("contraction mapping/inversion") therefore overstates its coverage. A minor related point: `mixedShare` does not require Σw = 1, so it is a share vector only up to scale (sanity test 6b). This does not affect injectivity.

### 6. Goodman–Bacon: documented deviation, not an error

`goodman_bacon` is the *unit-pair* decomposition b = Σ_{g,h} (V_gh/ΣV) β̂_gh. It is valid for any D. I checked by hand:
- pairNum with dm Y equals pairNum with Y, because Σ_t (dm D_g − dm D_h) = 0;
- pairs with pairVar = 0 have pairNum = 0.

The GB-specific 2×2 structure only appears through `pairCoef_indicator` and `pairCoef_split`. Those two give, respectively:
- the treated-vs-never-treated 2×2;
- the early/late split with μ = |pre|/(|pre|+|post|), which matches GB's μ_kl.

Not stated:
- a theorem assembling these into the timing-group decomposition with GB's closed-form weights in terms of group shares n_k and treatment shares D̄_k;
- the VWATT/VWCT/ΔATT bias decomposition (GB Thm 2).

The nonnegativity of `baconWeight` is unconditional only because of `x/0 = 0` (sanity test 4). That is harmless, since `hden ⇒ hv`.

### 7. Gauss–Markov, GMM, Lucas: documented deviations only

- **Gauss–Markov:**
  - X is fixed rather than conditioned on. This is the standard textbook simplification.
  - `hX` is implied by `hC`.
- **GMM:**
  - Linear moment model only.
  - No link between Cov(L) and `GMM.avar`.
  - No J-test.
  - No nonlinear GMM (NM Thms 2.6/3.4).
- **Lucas:**
  - u′ is an arbitrary positive function, not derived from a concave u (sanity test 8). This is harmless for the stated results, which use only u′ > 0.
  - Equilibrium is taken to be the Euler equation; the household problem with c = d market clearing is not modelled.
  - The present-value series formula is missing.

## Checks for vacuity and satisfiability

- **Gauss–Markov:** `gaussMarkov_witness` shows the hypotheses are satisfiable, and n = k = Unit with X = 1 is non-degenerate.
- **Extremum consistency:** take Θ = Icc 0 1, Q₀(θ) = −(θ−½)², Q_n = Q₀ and θ̂ = ½. All hypotheses hold, so the statement is not vacuous.
- **GMM:** G = I and W = I with S_n, W_n constant gives a non-vacuous instance.
- **BLQ:** n = 2, A = 0, S = I gives the unique B = I.
- **Lucas:** the example in the file (log utility, β = ½) is non-degenerate.
- **SequentialMarkets:**
  - The example in the file uses linear utility. Linear utility admits equilibria precisely because consumption sets are unbounded and the marginal rate of substitution equals the price ratio.
  - Log utility admits none (§1).
