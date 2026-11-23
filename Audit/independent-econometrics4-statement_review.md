# Statement review, round 4 (MLE, GaussianLimits, JTest, BLPContraction, GLS, SVAR sign/zero restrictions)

I read only the files in `stmt4/`. Proofs are `sorry` and comments are stripped, so I judged statements and definitions only. Nothing was compiled.

Verdict key: OK = faithful. WEAK = true and on topic, but weaker than the textbook result, or something the textbook proves is assumed instead. MISMATCH = the name or scope promises a result that is not stated. VACUOUS-RISK = hypotheses that could be contradictory, or a conclusion that is true only because of junk values. SUSPICIOUS = possibly false.

Main result: I found **no false statement and no vacuous hypothesis set**. Every theorem I checked is true as stated, including the degenerate cases where a singular matrix inverts to 0 (checked one by one below). The problems are about coverage and strength. Several flagship textbook results are assumed as hypotheses or left out (the chi-square law of J, the information-matrix equality, the MLE sample criterion and its ULLN, BLP existence and modulus, consistency of HC0 and Newey-West).

## Table

| Declaration | File | Textbook reference | Verdict | Reason |
|---|---|---|---|---|
| densityMeasure | MLE | density P_θ = f_θ·ν | OK | Standard. `ofReal` clips negative values, but every use assumes `hpos`. |
| llr_densityMeasure | MLE | log(dP₀/dP₁) = log f₀ − log f₁ | OK | True: ν is σ-finite and the densities are positive and finite. |
| densityMeasure_ac | MLE | P₀ ≪ P₁ under common positive support | OK | True even when f₀ is not measurable. |
| integral_log_sub_eq_klDiv | MLE | KL = E₀[log f₀ − log f₁] (Newey–McFadden Lemma 2.2 ingredient) | OK | Matches Mathlib `klDiv` for probability measures. Gibbs gives ∫llr ≥ 0, so `toReal` is exact. |
| expectedLogLik | MLE | Q₀(θ) = E_{θ₀} log f(X,θ) | OK | |
| expectedLogLik_unique_max | MLE | Information inequality, NM Lemma 2.2 (Hayashi Ch. 7 Kullback–Leibler inequality) | OK | Strict maximum at θ₀ under identification of measures. Satisfiable: normal location family. |
| mle_consistent_of_density | MLE | NM Thm 2.1 + 2.5; Hayashi Prop 7.5 | WEAK | Q_n is an arbitrary random criterion, not the sample log-likelihood. There is no i.i.d. sample from P_θ₀. The ULLN and the continuity of Q₀ are assumed, not derived from dominance. `hpos` excludes families whose support depends on θ. |
| euclidCLM / euclidCLM_apply / adjoint_euclidCLM | GaussianLimits | linear map x ↦ Ax | OK | |
| map_multivariateGaussian | GaussianLimits | A·N(0,S) = N(0,ASAᵀ) | OK | |
| map_mulVec_of_gaussian | GaussianLimits | same, on `l → ℝ` | OK | |
| z_estimator_limit_law | GaussianLimits | NM Thm 3.1: N(0, H⁻¹ΣH⁻ᵀ) | OK | No invertibility is assumed, but it is still true when H₀ is singular: both sides are δ₀. The transpose is handled correctly for a nonsymmetric H₀. |
| mle_limit_law | GaussianLimits | NM Thm 3.3; Hayashi Prop 7.9: N(0, I⁻¹) | WEAK | Pure Gaussian algebra. The information-matrix equality (score variance = −Hessian = I) is hard-wired by choosing H₀ = −I. Nothing ties I to f. |
| gmm_limit_law | GaussianLimits | Hansen 1982 Thm 3.1; Hayashi Prop 3.1 | OK | Needs only Wᵀ = W. When the Gram matrix is singular, both sides are δ₀ (junk, but harmless). |
| gmm_limit_law_efficient | GaussianLimits | Hansen 1982 Thm 3.2; Hayashi Prop 3.5 | OK | |
| residMaker / jForm / projP | JTest | Hayashi §3.6 projection algebra | OK | |
| gram_unit, residMaker_eq, jForm_eq_projP, projP_mul_self, transpose_projP_mul, jForm_transpose, jForm_eq, jForm_mul_G, jForm_mul_S_mul, trace_jForm_mul | JTest | Hayashi proof of Prop 3.6 (idempotent quadratic forms) | OK | I checked each identity by hand. All hold under the stated hypotheses. |
| jStat | JTest | Hansen J = n ĝ′Ŵĝ | OK (naming) | Correct for linear GMM. The argument called `S` is the Jacobian S_xz, not the long-run variance. This clashes with `S` in `jForm` (see item 10). |
| residMakerFn, residMakerFn_eq, residMakerFn_mulVec, continuousAt_residMakerFn, measurable_residMakerFn, resid_eq | JTest | plumbing for the continuous-mapping theorem | OK | |
| jStat_tendsto | JTest | Hansen Lemma 4.2 / Hayashi Prop 3.6 (first half) | WEAK | The limit is (ML)′W₀(ML) for any W₀. W₀ = S⁻¹ is never required. There is no combined statement for the efficient case. |
| jLimit_efficient | JTest | Hayashi Prop 3.6 algebra | OK | |
| integral_mul_multivariateGaussian, integrable_mul_eval | JTest | E[xxᵀ] = S | OK | |
| integral_jLimit | JTest | E[χ²(l−k)] = l−k | MISMATCH (coverage) | Only the **mean** of the limit is established. **Hansen's J →d χ²(l−k) is never stated.** |
| denom, denom_bounds | BLPContraction | BLP App. I bounds | OK | Strictness comes from the outside good's "1". Still true when J is empty. |
| blpMap | BLPContraction | BLP (1995) eq. (6.8): T(δ) = δ + ln s − ln σ(δ) | OK | Finite mixture = simulated shares. The weights are not normalised, which is harmless. |
| mixedShare_pos, blpMap_fixed_iff | BLPContraction | fixed point ⇔ share inversion | OK | |
| share_ratio_bounds | BLPContraction | | OK | |
| blpMap_dist_lt | BLPContraction | BLP App. I contraction theorem | WEAK | States strict contractivity in sup-norm (Edelstein type), not a contraction modulus < 1. True globally; the global modulus really is 1. BLP's modulus-< 1 statement on a bounded region is not given. |
| continuous_blpMap | BLPContraction | | OK | |
| blpMap_iterate_tendsto | BLPContraction | BLP App. I; Berry 1994 Thm 1 | WEAK | **Assumes** a fixed point δ* exists (`hstar`). Berry's existence for the mixed model is not proved. No geometric rate. `hs` is redundant given `hstar`. |
| blp_contraction_witness | BLPContraction | example | OK | Logit with 2 products, s = (1/3, 1/3), δ* = 0. |
| glsMat, gls | GLS | Aitken 1935; Hayashi §1.6 | OK | |
| glsMat_mul, transpose_of_posDef, isUnit_det_of_posDef, glsMat_mul_mul_transpose | GLS | | OK | |
| aitken_matrix | GLS | Aitken theorem (matrix form) | OK | |
| cov_gls | GLS | Var(β̂_GLS) = (X′V⁻¹X)⁻¹ | OK | V is the full error covariance (σ² absorbed into V). This is faithful because GLS is invariant to scaling V. |
| aitken | GLS | GLS is BLUE | OK | Linear unbiased ⇔ CX = I, X fixed. `hA` is redundant (it follows from hV and hC). |
| ols_cov_sub_gls_posSemidef | GLS | corollary | OK | |
| gls_eq_ols_transformed | GLS | Hayashi §1.6 transformed regression | OK (junk-assisted) | No invertibility of L is assumed. Still true when L is singular: both sides are 0 because the inverses are junk. |
| sandwich, hc0 | GLS | White 1980 HC0 | OK | |
| sandwich_eq, sandwich_posSemidef, hc0_posSemidef, sandwich_apply | GLS | | OK | When XᵀX is singular, PSD holds trivially (0). |
| cov_ols_hetero | GLS | Var(b \| X) = (X′X)⁻¹X′ΩX(X′X)⁻¹ | OK | No rank hypothesis, but still true when the rank is deficient: both sides are 0. |
| integral_sandwich_sq | GLS | (none; infeasible HC0) | WEAK | Unbiasedness of the sandwich built from the **true errors ε**, not from the residuals. The feasible HC0 is biased (MacKinnon–White 1985). White's main theorem (consistency of HC0) is not stated. |
| secondMoments_resid, integral_resid_sq | GLS | E[ee′] = MΣM; E e_i² = σ²(1−h_ii) | OK | |
| hc2_unbiased | GLS | MacKinnon–White 1985 HC2 | OK (narrow) | Element-wise only. The full HC2 matrix unbiasedness under homoskedasticity is not stated (it follows by linearity). |
| nwWindow, bartlett, bartlett_eq, bartlett_posSemidef | GLS | Newey–West 1987 Bartlett weights 1 − j/(L+1) | OK | I checked the count of common windows: max(0, L+1−\|t−s\|). |
| neweyWest | GLS | NW 1987 Ŝ = Γ̂₀ + Σ w_j(Γ̂_j + Γ̂_j′) | WEAK | Equals T·Ŝ (missing the 1/T). No demeaning, and Γ̂_j is not exposed. Harmless for PSD. |
| neweyWest_posSemidef | GLS | NW 1987 Thm 1 (PSD) | OK | Consistency (NW Thm 2) is not covered. |
| truncated_not_posSemidef | GLS | motivation for Bartlett weights | OK | Kg = (0,1,0), so g′Kg = −1. |
| gls_witness | GLS | example | OK | Checked: (4/5)·[1, 1/4]. |
| SignOKH | SVARRestrictions | Uhlig 2005; RWZ 2010 IRF sign restrictions | WEAK | Φ is an arbitrary sequence, not tied to the VAR MA coefficients. The inequality is weak (≥ 0), so a zero response satisfies a "positive" restriction. RWZ use strict inequalities. |
| identifiedSetH | SVARRestrictions | identified set {B₀Q : Q ∈ O(n), signs hold} | OK | |
| identifiedSetH_eq | SVARRestrictions | RWZ / Uhlig parametrisation | OK | |
| identifiedSetH_anti | SVARRestrictions | monotonicity | OK (trivial) | |
| identifiedSetH_impact | SVARRestrictions | horizon-0 case | OK (trivial) | I checked the tuple projections: they line up with `SignOK`. |
| ZeroOK | SVARRestrictions | zero restrictions on the impact matrix | OK | |
| order_condition_not_sufficient_existence | SVARRestrictions | Rothenberg order condition / RWZ Thm 7 | WEAK | True, but the example puts all 3 zeros in one column. It shows the restrictions are inconsistent with a nonsingular B, not a failure of identification. It already violates RWZ's per-column counting rule q_j = n − j. |
| order_condition_not_sufficient_uniqueness | SVARRestrictions | RWZ 2010 (rank condition needed) | WEAK | True, but B₂ is just the identity with shocks 1 and 2 swapped and one sign flipped. B₂ fails positive-diagonal normalisation. A much stronger counterexample exists: a continuum of rotations. |

## Detail on non-OK items

### 1. JTest: the chi-square law is never stated (MISMATCH / coverage)
`integral_jLimit` proves E[y′ jForm y] = l − k for y ~ N(0, S). `jForm_mul_S_mul` (A S A = A) and `trace_jForm_mul` (tr(A S) = l − k) are exactly the ingredients of the classical lemma: z ~ N(0, Ω) and AΩA = A imply z′Az ~ χ²(rank). But no theorem concludes that the limit law is χ²(l − k), or even that it equals the law of a sum of l − k squared standard normals.

The first moment does not identify the law. For example, (l − k)·Z² has mean l − k but variance 2(l − k)², whereas χ²(l − k) has variance 2(l − k). A reader who sees a "JTest" module will assume Hansen (1982) Lemma 4.2 is stated. It is not.

Suggested fix: state `P'.map (fun ω => L ω ⬝ᵥ (jForm S G *ᵥ L ω)) = chiSquared (l − k)` (via `gammaMeasure`). Failing that, show it equals the law of ∑_{i<l−k} Zᵢ² for i.i.d. standard normal Zᵢ.

### 2. mle_consistent_of_density: not actually about the MLE (WEAK)
`Q : ℕ → Ω → Θ → ℝ` is unconstrained, and there is no data X_i ~ P_θ₀. The theorem is `extremum_consistent` with the identification hypothesis discharged by `expectedLogLik_unique_max`.

Both substantive steps of NM Thm 2.5 / Hayashi Prop 7.5 are **assumed**:
- `hulln`, the ULLN for (1/n)Σ log f(X_i, θ), which the textbook derives from i.i.d. sampling, continuity and dominance E sup_θ |log f| < ∞.
- `hcont`, continuity of Q₀.

`hpos : ∀ θ x, 0 < f θ x` also rules out families whose support depends on θ, such as Uniform(0, θ), where the textbook theorem (with the log 0 = −∞ convention) still applies.

Counter-reading: take Q n ω θ := expectedLogLik ν f θ₀ θ (deterministic) and θhat := θ₀. Every hypothesis holds without any likelihood or sample, which shows the statement carries no MLE-specific content beyond identification.

### 3. mle_limit_law: information equality hard-wired (WEAK)
The conclusion -((-I)⁻¹ L) ~ N(0, I⁻¹) is just I⁻¹ · N(0, I) = N(0, I⁻¹ I I⁻¹). The economic content of MLE asymptotic normality is the information-matrix equality: E[score·scoreᵀ] = −E[Hessian] = I, under differentiability and dominance. That equality is encoded by the user choosing H₀ = −I and score variance I. No theorem in scope relates I to `f` (no score, no Hessian, no differentiation under the integral). The result is a special case of `z_estimator_limit_law` with H₀ := −I.

### 4. order_condition_not_sufficient_uniqueness: witness is a relabelling (WEAK)
B₂ = [[1,0,0],[0,0,−1],[0,1,0]] has columns e₀, e₂, −e₁. It is the identity with shocks 1 and 2 relabelled and one sign flipped. Its diagonal is (1, 0, 0), so it fails the positive-diagonal normalisation used in `IsRecursive`. A skeptic would say "non-uniqueness up to labelling and sign", which every SVAR paper already normalises away.

A stronger, normalisation-proof counterexample: any B = diag(1, R_θ) with R_θ the 2×2 rotation and |θ| < π/2 satisfies B₀₁ = B₀₂ = B₁₀ = 0, BBᵀ = I, and has a positive diagonal. That gives a continuum of observationally equivalent, normalised B. The column counts are (1,1,1) rather than RWZ's (2,1,0), which is why the rank condition fails. Suggested fix: use θ = π/4 and add `∀ i, 0 < B₂ i i`.

### 5. blpMap_iterate_tendsto / blpMap_dist_lt: existence assumed, no modulus (WEAK)
- `hstar : mixedShare w μ δstar = s` assumes the inversion exists. Berry (1994) Thm 1 and BLP App. I prove existence for every s in the open simplex. In scope, existence is proved only for plain logit (`share_surjective`, in BLP.lean). So for random coefficients the theorem is "if an inverse exists, iteration finds it".
- `blpMap_dist_lt` is the Edelstein-type strict inequality d(Tδ, Tδ′) < d(δ, δ′). That is correct, and the global Lipschitz constant really is 1: row sums 1 − σ₀ → 1 as δ → +∞. BLP's theorem gives a modulus < 1 on a region bounded below, hence a geometric rate, and neither is stated.
- `hs` is implied by `hstar` + `mixedShare_pos`, so it is redundant.

### 6. integral_sandwich_sq: infeasible HC0 (WEAK)
The statement is E[sandwich X (ε²)] = sandwich X σ², using the true errors ε. The feasible White estimator `hc0 X e` uses OLS residuals e = Mε, and it is biased:
E[e_i²] = Σ_j M_ij² σ_j² ≠ σ_i².
The bias is exactly why MacKinnon–White (1985) introduced HC2/HC3. White (1980)'s actual theorem is consistency (n·HC0 → plim n·sandwich), and it is not stated. Any reading of "HC0 is unbiased" from this statement is wrong.

Counterexample to the feasible version: n = 2, X = (1, 1)ᵀ, homoskedastic σ² = 1. Then h_ii = 1/2 and E[e_i²] = 1/2. E[hc0] = (1/4)(1/2 + 1/2) = 1/4, while the true variance is 1/2.

### 7. neweyWest: unnormalised, consistency missing (WEAK)
gᵀ K g = Σ_{t,s} K_ts g_t g_sᵀ = T·(Γ̂₀ + Σ_j w_j(Γ̂_j + Γ̂_jᵀ)), with no 1/T and no demeaning. That is fine for `neweyWest_posSemidef` (NW 1987 Thm 1). NW Thm 2 (consistency for the long-run variance as L → ∞, L = o(T^{1/4})) is not covered.

### 8. SignOKH / identifiedSetH: Φ unlinked, weak inequality (WEAK)
Φ : ℕ → Matrix is any sequence. Nothing requires Φ₀ = I (except in `identifiedSetH_impact`), and nothing requires Φ_h to be the VAR(p) MA coefficients (VAR.lean has `ma`, but the two are not connected). The constraint 0 ≤ s·(Φ_h B)_ij is weak, so a zero response satisfies a "positive" restriction; RWZ (2010) and Arias–RWZ use strict signs. The statements remain true, but sets of measure zero in Q are admitted.

The `identifiedSetH_*` results are bookkeeping (parametrisation, monotonicity, the horizon-0 case). No substantive result from Uhlig/RWZ is stated: nonemptiness, a uniform-Haar draw, or RWZ Theorem 7 (rank condition ⇔ exact identification).

### 9. order_condition_not_sufficient_existence: illustrates inconsistency (WEAK)
All three zeros sit in column 0, which forces a singular B. The example meets Rothenberg's total count n(n−1)/2 = 3 but violates RWZ's per-column condition (q = (3,0,0) vs (2,1,0)). So it does not show that "the order condition holds but identification fails" in RWZ's sense. True as stated.

### 10. jStat_tendsto: generic weight, no assembled J theorem; naming clash (WEAK)
The theorem holds for any W₀. The χ² statement needs W_n →p S⁻¹ with S the variance of the limit L, and the module never puts these together. A user has to chain `jStat_tendsto`, `jLimit_efficient` (with hW₀ : W₀ = S⁻¹ and a separate S whose link to L's law is left to the user) and `integral_jLimit`. Also, in `jStat` and `jStat_tendsto` the name `S` means the sample Jacobian, while in `jForm` and `jLimit_efficient` it means the long-run variance. That invites misinstantiation.

### Minor notes (OK but worth knowing)
- `gls_eq_ols_transformed`, `cov_ols_hetero`, `z_estimator_limit_law`, `gmm_limit_law` and `sandwich_posSemidef` take no rank or invertibility hypotheses. They stay true in the degenerate case only because singular inverses are 0 and both sides collapse to 0 or δ₀. That is harmless, but the junk value is what keeps them true there.
- `aitken`: `hA` is derivable from `hV` and `hC`. In `ols_cov_sub_gls_posSemidef`, `hX` is likewise implied by `hA` (X injective).
- `hc2_unbiased`: only one coordinate. The matrix HC2 unbiasedness under homoskedasticity is not assembled.
