# Statement review E: Econometrics/Causal/*, Econometrics/OLS, Finance/AssetPricing

Reviewer stance: adversarial. Only the statement files under `/home/user/rv/in/` were read (proofs are `sorry`, comments stripped). Lean was not run; `sanity_tests.lean` is unchecked.

**Overall.** The causal-inference layer is mostly careful. It uses `IndepFun` on the correct joint tuples, adds explicit integrability and positivity hypotheses, and has nondegenerate witnesses (LATE = 2 with first stage 1/3; a DiD where the naive post-period gap of 3 differs from ATT = 2; a TWFE example where the coefficient is −1/2 with all effects positive). I found no statement that is false or vacuous. The problems are of two kinds:
- **(a) Restricted versions presented under general names.** Unconfoundedness and IPW are proved only for finitely many covariate values. RD is done for deterministic regression functions with no probability. The FTAP is one-period with finitely many states. OLS unbiasedness assumes a fixed design.
- **(b) Missing canonical results the file names suggest.** These include Goodman-Bacon, Gauss–Markov, the propensity-score theorem, the risk-neutral measure, and sharpness of the ATE bounds.

The weakest headline is sharp RD. It is a fact about limits of continuous functions, and its notion of "observed data" reads the regression function at the single point x = c. That value is exactly what is not identified when the running variable is continuous.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `ind`, `condMean` | Causal/Basic | E[Y \| s] = E[Y·1_s]/P(s) | faithful with documented deviation | Junk value 0 when P(s)=0 or μ(s)=∞; theorems that use it add positivity hypotheses |
| `condMean_add/sub/congr/const/ind` | Causal/Basic | — | faithful | Integrability or positivity assumed where needed |
| `setIntegral_eq_of_indepFun`, `condMean_eq_integral_of_indepFun` | Causal/Basic | E[F \| Z=b] = E[F] under F ⊥ Z | faithful (junk-tolerant) | True without integrability: by independence both sides are 0 when F is non-integrable |
| `observed`, `treated`, `untreated`, `ate`, `att`, `diffInMeans` | Causal/PotentialOutcomes | Imbens–Rubin ch. 1–3; Angrist–Pischke §2.1 | faithful with documented deviation | `ate` is a Bochner integral, so it is 0 when E\|Y₁−Y₀\| = ∞ (not ±∞) |
| `diffInMeans_eq_att_add_selectionBias` | Causal/PotentialOutcomes | Angrist–Pischke eq. (2.1.1) | faithful | Exact decomposition, integrability assumed |
| `diffInMeans_eq_ate` | Causal/PotentialOutcomes | Imbens–Rubin Thm 6.1 / A–P §2.2 | faithful | (Y₀,Y₁) ⊥ D jointly, both arms have positive probability, integrable |
| `att_eq_ate` | Causal/PotentialOutcomes | — | faithful with documented deviation | No integrability: when E\|Y₁−Y₀\|=∞ the equality is 0 = 0 by junk |
| `stratum`, `cell`, `armProb`, `propensity`, `Overlap`, `MeanUnconfounded` | Causal/Unconfoundedness | Rosenbaum–Rubin 1983; Imbens–Rubin ch. 12 | faithful with documented deviation | Covariate X takes finitely many values (`Fintype κ`); mean-independence rather than full conditional independence (acceptable, weaker) |
| `integral_potential_eq_adjustment`, `ate_eq_adjustment` | Causal/Unconfoundedness | Regression adjustment / g-formula (Imbens–Rubin §12.2, Hansen 2022 §(ATE)) | WEAK | Only discrete finite X; no general version with conditional expectation `μ[Y\|σ(X)]` |
| `ipw`, `ate_eq_ipw` | Causal/Unconfoundedness | Horvitz–Thompson / Hirano–Imbens–Ridder | WEAK | Same finite-X restriction; the propensity score is a ratio of cell masses, not a conditional probability |
| (absent) propensity-score theorem | Causal/Unconfoundedness | Rosenbaum–Rubin 1983 Thm 3 | coverage gap | The names (`propensity`) suggest it, but D ⊥ Y(d) \| e(X) is never stated |
| `manskiLower/Upper`, `manski_bounds` | Causal/Bounds | Manski 1990; Manski (2003) Ch. 2 | faithful with documented deviation | Support bounds required for every ω (∀ ω), not a.e. Strictly stronger than needed, harmless |
| `manski_sharp` | Causal/Bounds | Manski sharpness | faithful | Constant imputation on the untreated set gives every v; also correct when P(untreated)=0 |
| `manski_ate_bounds` | Causal/Bounds | Manski 1990 (width = hi − lo) | faithful; coverage gap | Bounds and width correct, but sharpness of the ATE bounds is not stated; Y₀ and Y₁ must share one support [lo,hi] |
| `DiD2x2`, `ParallelTrends`, `NoAnticipation` | Causal/DiD | A–P §5.2; Roth et al. 2023 §2 | faithful | Mean parallel trends, mean no-anticipation |
| `did_eq`, `did_eq_att` | Causal/DiD | Card–Krueger 2×2 identification | faithful | Exact algebra; no probability measure or positivity needed (degenerate cases are 0 = 0) |
| `IVModel`, `Independent`, `Monotone`, `wald`, `late` | Causal/LATE | Imbens–Angrist 1994 Thm 1; A–P Thm 4.4.1 | faithful with documented deviation | Exclusion is hard-coded (Y depends on Z only through D); independence of (Y₀,Y₁,D₀,D₁) from Z; monotonicity a.e. |
| `firstStage_eq`, `reducedForm_eq` | Causal/LATE | A–P §4.4 | faithful | — |
| `wald_eq_late` | Causal/LATE | Imbens–Angrist 1994 | faithful (minor) | The relevance hypothesis `hfs` is redundant: without it, both sides are junk 0 (sanity L1). Harmless, but the formal theorem does not depend on relevance |
| `sharpMean`, `tendsto_sharpMean_*`, `sharp_rd` | Causal/RD | Hahn–Todd–van der Klaauw 2001 Thm 1; Imbens–Lemieux 2008 | WEAK | Deterministic functions m₀, m₁; no random variables, conditional expectations, or support/density condition at c. The content is that a continuous function has a limit |
| `sharp_rd_identified` | Causal/RD | HTV 2001 | WEAK / MISMATCH | Observational equivalence = pointwise equality including at x=c. So m₁(c) is "observed" directly and `h₁`, `h₁'` are unused (sanity R1). The canonical notion is P_X-a.e. equality, under which identification really needs right-continuity (sanity R2) |
| `sharp_rd_not_identified_without_continuity` | Causal/RD | — | faithful (as a witness) | Valid counterexample in this model |
| `FuzzyRD`, `fuzzy_rd`, `fuzzy_rd_ratio`, `example₁_witness` | Causal/RD | HTV 2001 Thm 3 | WEAK | Principal-stratum shares and means are primitives, with monotonicity and exclusion built in; `IsProb` is defined but never assumed (sanity R3); no probability content |
| `IsTWFE`, `NormalEq`, `isTWFE_iff_normalEq` | Causal/TWFE | FWL / normal equations | faithful | — |
| `eps`, `weight`, `sum_weight`, `twfe_eq_weighted_sum` | Causal/TWFE | de Chaisemartin–D'Haultfœuille 2020 Thm 1 | faithful with documented deviation | Balanced panel, one observation per (g,t), no error term (exact additive Y(0) = α_g+λ_t, i.e. parallel trends at the population level of cell means); D may be real-valued (more general) |
| `Example.weight_negative`, `twfe_negative` | Causal/TWFE | dCDH 2020 / Goodman-Bacon 2021 example | faithful | Checked by hand: ε = (1/3, −1/6, 1/6), weights (1, −1/2, 1/2), b = −1/2 although every τ > 0. The residuals of the claimed minimizer satisfy all normal equations |
| (absent) Goodman-Bacon decomposition | Causal/TWFE | Goodman-Bacon 2021 Thm 1 | coverage gap | β̂ as a variance-weighted average of all 2×2 DiDs (including "forbidden" late-vs-early comparisons) is not stated |
| `ssr`, `IsLeastSquares`, `NormalEquations`, `ols` | OLS | Hansen *Econometrics* ch. 3 | faithful with documented deviation | `ols` = (XᵀX)⁻¹Xᵀy uses `Matrix.inv`, so it is 0 for singular XᵀX (sanity O1) |
| `isLeastSquares_iff_normalEquations`, `isUnit_det_gram_iff`, `isLeastSquares_iff_eq_ols` | OLS | Hansen §3.6 | faithful | — |
| `hat`, `annihilator`, `hat_*`, `annihilator_*`, `fitted_eq_hat`, `residual_eq_annihilator` | OLS | Hansen §3.11–3.12 | faithful | `hat_transpose`, `fitted_eq_hat`, `residual_eq_annihilator` hold without full rank only as junk identities |
| `fwl`, `ols_inr_eq`, `isUnit_det_gram_*` | OLS | Frisch–Waugh–Lovell (Hansen Thm 3.5) | faithful | Both coefficient and residual parts; `fwl` needs only X₁ to have full rank |
| `ols_omitted`, `ols_linear_model` | OLS | Omitted-variable formula (Hansen §2.24) | faithful | Algebraic |
| `integral_ols` | OLS | Unbiasedness (Hansen Thm 4.1) | faithful with documented deviation | Fixed (nonrandom) design X with E[ε]=0, not random X with E[ε\|X]=0 |
| (absent) Gauss–Markov; Var(β̂) = σ²(XᵀX)⁻¹ | OLS | Hansen Thm 4.4 / 4.2 | coverage gap | Not stated anywhere (sanity O2 sketches the statement) |
| `Market`, `IsArbitrage`, `NoArbitrage`, `IsStatePrice`, `Complete` | Finance/AssetPricing | Duffie *Dynamic Asset Pricing* §1.B–1.C; LeRoy–Werner | faithful | Arbitrage: (−q·h, Xh) > 0 |
| `cost_eq` | Finance/AssetPricing | — | faithful | — |
| `ftap` | Finance/AssetPricing | Duffie Thm 1.A (Dybvig–Ross); not Harrison–Kreps/Pliska | faithful with documented deviation | One period, finite states and assets |
| `ftap_sdf` | Finance/AssetPricing | Cochrane ch. 4 (p = E[mx], m > 0 ⟺ NA) | faithful with documented deviation | The weights π need not sum to 1 (more general); finite states |
| `complete_iff_unique` | Finance/AssetPricing | Duffie §1.C / LeRoy–Werner | faithful | Under NA: unique positive state prices ⟺ ker Xᵀ = 0 ⟺ X surjective. Proof sketch checked |
| (absent) risk-neutral measure, Riesz/law of one price, Hansen–Jagannathan | Finance/AssetPricing | Duffie §1.D; Cochrane ch. 4–5 | coverage gap | No riskless asset, so no Q with q = E^Q[x]/R_f |

## Details on non-faithful items

### 1. Sharp RD (`sharp_rd`, `sharp_rd_identified`) — WEAK / MISMATCH in the identification notion
- **Model.** The model has no random variables. `m₀` and `m₁` are arbitrary functions ℝ → ℝ, and "the data" is the function `sharpMean m₀ m₁ c` on all of ℝ, *including its value at x = c*.
- **Problem with `sharp_rd_identified`.** Its hypothesis `hobs` is equality of these functions everywhere. Evaluating at c gives `m₁ c = m₁' c` immediately (sanity R1), so `h₁` and `h₁'` are dead hypotheses. Only the m₀ half uses continuity.
- **Canonical result** (HTV 2001; Imbens–Lemieux 2008, eq. 2): the data identify E[Y | X = x] only P_X-a.e. With X continuous, the value at x = c is not identified. Identification therefore rests on both one-sided limits, so continuity of *both* m₀ and m₁ is needed.
- **Concrete case (sanity R2).** Take m₀ = 0 and m₁ = 1_{x=0}. This agrees with (0, 0) Lebesgue-a.e., yet the Lean model treats the two as different observed data.
- **Fix.** Replace `hobs` by equality on a punctured neighbourhood, or a.e. with respect to a measure with positive density near c. Then both continuity hypotheses become necessary.
- **What is missing more broadly.** Nothing connects m_d to E[Y(d) | X = x]: there is no regular conditional expectation, no density f_X(c) > 0, and no estimand written as a limit of `condMean` over shrinking windows.
- **Fuzzy RD.** `fuzzy_rd` is the same kind of algebra on primitive type-shares (sanity R3: `IsProb` is not even assumed).

### 2. Unconfoundedness / IPW (`ate_eq_adjustment`, `ipw`, `ate_eq_ipw`) — WEAK, finite-covariate version
- **Restriction.** All three require `[Fintype κ]` with `X : Ω → κ`, so the covariates take finitely many values. The "propensity score" is μ(cell)/μ(stratum).
- **What the textbook covers.** Rosenbaum–Rubin and Hirano–Imbens–Ridder cover general (continuous) X, with e(X) = P(D=1 | X) defined as a conditional expectation and only a.e. Writing that version is exactly where Mathlib's a.e. `condExp` and the junk 0 for non-integrable variables would bite, and it is avoided entirely.
- **Assessment.** The statements are correct for what they say (the integrand Y/e(X) is handled by cases, and null strata give 0/0 = 0 only on null sets). But the names suggest the general theorem. The propensity-score theorem itself (D ⊥ (Y₀,Y₁) | e(X)) is absent.

### 3. TWFE — Goodman-Bacon decomposition absent; dCDH is the balanced, no-noise version
- **What is covered.** `twfe_eq_weighted_sum` is dCDH 2020 Thm 1 for a balanced panel with equal cell sizes (one observation per (g,t)), where the untreated outcome is exactly additive, α_g + λ_t. This is the population cell-mean form of parallel trends, so it is faithful at that level. The proof route through ε = residual of D on the fixed effects is sound for any real D.
- **What is missing.** Goodman-Bacon's (2021) decomposition of β̂_TWFE into 2×2 DiDs with variance weights, which the review brief lists as a headline, is not stated. Neither is the dCDH result that negative weights arise only on treated cells with large ε, nor any general sign result; the file only gives an example.

### 4. LATE — relevance redundant (minor)
- `firstStage = μ.real compliers`, `wald = rf / fs`, `late = (μ.real C)⁻¹ * ∫_C …`.
- When P(C) = 0, both sides are 0 because x/0 = 0 and 0⁻¹ = 0 (sanity L1). So `wald_eq_late` holds without `hfs`.
- This does not make the theorem wrong. It does mean that a reader cannot rely on the formal statement to have checked that relevance is used.
- Exclusion is encoded structurally (`Y` reads `D` only) rather than stated as Y(d,z) = Y(d,z′). That is a documented modelling choice, and it is acceptable.

### 5. Measure-theoretic junk in the potential-outcomes layer (minor)
- `ate` is `∫ (Y₁ − Y₀)`, which is 0 if that difference is not integrable (sanity J2).
- `att_eq_ate` and the `condMean_*_of_indepFun` lemmas carry no integrability hypothesis. With E[Y₁] = +∞ under randomization, the textbook says ATT = ATE = +∞, and Lean proves 0 = 0.
- `condMean` on null or infinite-measure sets is 0 (sanity J1). Every headline theorem that relies on `condMean` adds the positivity it needs, so no false content follows.
- Recommendation: add `Integrable` hypotheses to `att_eq_ate` for uniformity.

### 6. OLS — fixed design, junk `ols`, missing Gauss–Markov
- **Fixed design.** `integral_ols` treats X as a deterministic matrix and assumes E[ε]=0. Hansen's Theorem 4.1 is E[β̂ | X] = β under E[e | X] = 0 with random X. That conditional version, where `condExp` would be a.e., is not attempted.
- **Junk `ols`.** For singular XᵀX, `Matrix.inv` returns 0, so `ols X y = 0` (sanity O1). Theorems that need full rank do assume it.
- **Missing results.** Gauss–Markov (BLUE), Var(β̂ | X) = σ²(XᵀX)⁻¹, and consistency/asymptotic normality are all absent. The task list names Gauss–Markov.

### 7. FTAP — one-period finite-state only
- `ftap` and `complete_iff_unique` are correct finite-dimensional theorems, checked by hand: Farkas/Stiemke and ker Xᵀ = 0.
- They are not the general FTAP (Harrison–Kreps 1979, Harrison–Pliska 1981, Dalang–Morton–Willinger, Delbaen–Schachermayer).
- No risk-neutral measure is stated, because there is no riskless asset or normalisation.
- `ftap_sdf` allows π with any positive mass, not just a probability vector. That is fine and slightly more general.

### 8. Manski bounds — minor
- The support bounds `hlo` and `hhi` are required for every ω rather than a.e. This is harmless and slightly stronger than needed.
- `manski_ate_bounds` proves validity and width hi − lo, but not sharpness of the ATE interval. The file proves sharpness only for E[Y₁].
