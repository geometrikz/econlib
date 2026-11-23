# Statement review (round 2): IV, GMM, Causal, Asymptotics, TimeSeries

Scope: statements and definitions only, from `review2/stmts/`. Mathlib definitions I checked: `TendstoInDistribution` (it bundles `AEMeasurable` of each X i and of the limit), `TendstoInMeasure` (it uses edist and outer measure), `Matrix.PosDef` (it includes `IsHermitian`, so it is symmetric over ℝ), `IsLowerTriangular` (= `BlockTriangular toDual`, so `i < j → M i j = 0`), and `strong_law_ae` (pairwise independence plus IdentDistrib).

**Overall verdict:** I found no statement that is false and no hypothesis set that is vacuous. The problems are weak coverage, modelling choices that hide unobservables or exclude the textbook case, and a few hypotheses that are redundant.

## Table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| momentZX, momentZY, momentSolutions | IV | Hayashi §3.2 (σ_xz, σ_xy) | OK | Bochner junk value 0 is neutralised by the integrability hypotheses in the theorems |
| mem_momentSolutions | IV | Hayashi (3.3.1) orthogonality ⇒ β solves the moment eq. | OK | Integrability of z·x and z·ε is enough |
| momentSolutions_eq_singleton_iff | IV | Hayashi Prop 3.1 (rank condition) | OK | Unique solution ↔ E[zx'] injective (full column rank); `l` may even be infinite |
| tsls | IV | Hayashi (3.8.3) | OK | Same formula as Hayashi (X'P_Z X)^{-1}X'P_Z y |
| tsls_eq_ols_fitted | IV | Hayashi §3.8 (2SLS as OLS on fitted X) | OK (redundant hyp.) | True without hZ, since both sides are 0 when Z'Z is singular |
| tsls_eq_iv | IV | Hayashi (3.8.4)/just identified | OK (redundant hyp.) | hZ follows from hZX |
| moment, criterion | GMM | Hayashi (3.4.1)–(3.4.3), J(b,W) | OK | Factor n dropped (harmless) |
| criterion_nonneg, criterion_of_exact | GMM | – | OK | Helpers |
| identified_iff | GMM | Hayashi §3.4 / Newey–McFadden Lemma 2.3 | OK | Left conjunct `criterion … β = 0` is always true; the content is "strict unique minimiser ↔ injective" |
| estimator | GMM | Hayashi (3.5.12) | OK | |
| posDef_gram, isUnit_det_gram, foc | GMM | – | OK | |
| criterion_eq_add | GMM | Hayashi §3.5 (quadratic decomposition) | OK | Needs Wᵀ=W, which is assumed |
| estimator_isMin | GMM | Hayashi Prop 3.? (ĝ minimises J) | OK | |
| estimator_of_exact | GMM | – | OK | |
| tsls_eq_estimator | GMM | Hayashi §3.8 (2SLS = GMM with W=(Z'Z)^{-1}) | OK | Holds unconditionally, junk consistent on both sides |
| avar | GMM | Hayashi Prop 3.1 (3.5.?) avar formula | WEAK | A bare formula, never tied to the asymptotic distribution of any estimator |
| avar_inv | GMM | Hayashi (3.5.13) | OK | |
| avar_sub_posSemidef | GMM | Hayashi Prop 3.5 | WEAK | Correct matrix inequality, but "efficient GMM" is only the algebraic core: no consistency, normality, feasible two-step or J-test (Hansen 1982) |
| bump, bump_apply | DeltaMethod | – | OK | Helper |
| tendstoInMeasure_of_tendstoInDistribution_const | DeltaMethod | vdV Thm 2.7(iii) | WEAK | Only the ⇒ direction of an iff |
| TendstoInMeasure.comp_continuousAt | DeltaMethod | vdV Thm 2.3 (CMT, constant limit) | OK | True for any measure (monotone outer measure) |
| tendstoInMeasure_const_seq, tendsto_inv_sqrt_nat | DeltaMethod | – | OK | |
| tendstoInMeasure_of_sqrt | DeltaMethod | vdV Lemma 2.12 / Prohorov | OK | |
| diffQuot, diffQuot_* , mul_diffQuot | DeltaMethod | – | OK | Helpers. The /0 junk value is avoided by the `if` |
| delta_method | DeltaMethod | vdV Thm 3.1 | WEAK | ℝ→ℝ only. vdV is ℝ^k→ℝ^m with Fréchet derivative. Hypotheses hT and hg are needed for the n = 0 and measurability edge cases |
| delta_method_clt | DeltaMethod | vdV Ex. 3.? / Wooldridge, Casella–Berger | OK | Law of g'Y also identified correctly |
| designMatrix, secondMoment, gram_designMatrix, transpose_designMatrix_mulVec | OLSConsistency | Hayashi (2.3.?) S_xx | OK | |
| ols_consistent | OLSConsistency | Hayashi Prop 2.1(a) | OK (special case) | iid (pairwise independent) instead of ergodic stationary, with an a.s. conclusion. Hypotheses match Assumptions 2.3–2.4. Junk OLS for small n does not matter for the limit |
| ols_consistent_witness | OLSConsistency | – | WEAK | Shows satisfiability only in a deterministic Dirac model, not a nondegenerate one |
| IsRecursive | SVAR | Sims 1980; Kilian–Lütkepohl §8.2 | OK | Lower triangular (checked Mathlib orientation) with diagonal > 0 |
| lower_apply | SVAR | – | OK | |
| observationallyEquivalent | SVAR | Kilian–Lütkepohl §8.1 (B vs BQ) | OK | |
| recursive_unique | SVAR | Cholesky uniqueness | OK | |
| recursive_exists, recursive_existsUnique | SVAR | Cholesky existence | OK | PosDef includes symmetry, so the statement is not false for an asymmetric S |
| not_identified | SVAR | K–L §8.1 | WEAK | Rotation witness does not show the diagonal sign normalisation is needed |
| IsPath | VAR | Hamilton (10.1.1)/(10.1.10), VAR(1) | WEAK | Only VAR(1) with deterministic shocks. VAR(p) companion form is not formalised |
| Stable | VAR | Hamilton Prop 10.1, Lütkepohl (2.1.9) | WEAK | Defined as Σ‖A^j‖ < ∞, which is equivalent to spectral radius < 1, but there is no bridge theorem to the eigenvalue / det(I−Az) condition |
| summable_of_norm_lt_one | VAR | – | OK | Sufficient only, and named as such |
| summable_pow_apply, tsum_pow_apply_eq | VAR | – | OK | |
| mean, mean_fixed, fixed_unique | VAR | μ = (I−A)^{-1}c | OK | tsum junk value excluded by Stable |
| ma | VAR | Hamilton (10.1.15), Lütkepohl (2.1.13) MA(∞) | WEAK | Junk value 0 if u is not summable along the path |
| ma_isPath | VAR | MA(∞) solves VAR | WEAK | Bounded-u hypothesis excludes iid Gaussian white noise (unbounded a.s.) |
| ma_bounded | VAR | – | WEAK | No CompleteSpace, so in incomplete E it can hold through the junk value tsum = 0 |
| tendsto_norm_pow, tendsto_irf_zero | VAR | IRF decays | OK | |
| isPath_unique | VAR | Unique stationary solution | WEAK | Bounded (not L²-stationary) solutions; same white-noise problem as ma_isPath |
| ma_impulse | VAR | Hamilton (11.4.1) IRF Ψ_h = A^h | WEAK | Correct, but the bounded-u restriction again applies |
| sharpMean, tendsto_sharpMean_*, sharp_rd | RD | HTV 2001 Thm 1 | OK | |
| sharp_rd_identified | RD | HTV 2001 Thm 1 (identification) | WEAK | Requires pointwise equality at every x≠c (a.e./local would suffice). Concludes only the difference, though both endpoints are identified |
| sharp_rd_not_identified_without_continuity | RD | – | OK | Valid counterexample |
| FuzzyRD, fuzzy_rd, fuzzy_rd_ratio, example₁_witness | RD | HTV 2001 Thm 3 | OK | IsProb unused (a generalisation). No defiers by construction (monotonicity) |
| bartik, exposure, shockAvg, ssiv, shockIV | ShiftShare | BHJ 2022 §2 | OK | No controls / residualisation (coverage gap) |
| sum_bartik_mul, ssiv_eq_shockIV | ShiftShare | BHJ Prop 1 | OK | hs needed only because signs are unrestricted |
| ssiv_sub | ShiftShare | – | OK | |
| integral_sum_bartik_mul(_eq_zero) | ShiftShare | BHJ Assumption 1 ⇒ E[Σ s_n g_n ε̄_n] = 0 | WEAK | ε deterministic (models conditioning by fixing ε). Only the numerator's mean, with no consistency (BHJ Prop 3 / Assumption 2) |
| shareIV, rotemberg, sum_rotemberg, bartik_eq_sum_rotemberg | ShiftShare | GPSS 2020 Prop 1 / eq. (5) | OK | Unweighted, no controls. If the first stage is 0, both sides are 0 by junk value, harmless |
| rotemberg_negative | ShiftShare | GPSS (negative weights) | OK | |
| FactorModel, y0, PreRank | SyntheticControl | ADH 2010 eq. (5), ξ(M) > 0 | OK | PreRank = Σ_{t∈pre} λ_tλ_t' nonsingular |
| sum_weight_y0, exact | SyntheticControl | ADH 2010 §2.3 (noise-free) | OK | Weights not restricted to the simplex: more general and still true |
| estimator_eq_effect | SyntheticControl | ADH 2010 (α̂_1t unbiased/consistent) | WEAK | Fit hypothesis stated on the latent Y^N of the treated unit, not on observed Y. No no-anticipation. Noise-free |
| not_exact_without_rank, exact_witness | SyntheticControl | – | OK | Both nondegenerate |

## Non-OK items

### VAR: bounded shocks exclude the textbook white-noise case (ma_isPath, ma_impulse, isPath_unique, ma)
Hamilton and Lütkepohl apply the MA(∞) to a white-noise u. If u_t is iid N(0,1), then sup_t |u_t| = ∞ almost surely. So no realised path satisfies `hu : ∀ t, ‖u t‖ ≤ M`, and none of these theorems applies to it. The series still converges pathwise: ‖A^j‖ decays geometrically once Σ‖A^j‖ < ∞, because ρ(A) < 1, and |u_{t−j}| = O(√log j) a.s. The bounded case is therefore a strict special case.
Fix: weaken to `hu : ∀ t, Summable (fun j : ℕ => ‖A ^ j‖ * ‖u (t - j)‖)`, or to polynomial growth `‖u t‖ ≤ M * (1 + |t|)^p`. For uniqueness, use the class of paths with that growth, or give an L²-process version.

### VAR: `Stable`
Defining stability as Σ‖A^j‖ < ∞ is equivalent to ρ(A) < 1 by Gelfand's formula. Hamilton Prop 10.1 and Lütkepohl (2.1.9) instead state the condition as all eigenvalues of the companion matrix |λ| < 1, or det(I_K − A_1 z − … − A_p z^p) ≠ 0 for |z| ≤ 1. Nothing in the files connects the two forms, and VAR(p) appears only through the abstract space E.
Fix: add `Stable A ↔ spectralRadius ℝ A < 1`, plus a matrix corollary over eigenvalues. Also add a companion-form lemma that turns a VAR(p) on ℝ^K into `IsPath` on (Fin p → ℝ^K).

### VAR: `ma_bounded` without CompleteSpace
In an incomplete E, `ma` can collapse to `mean c A`, which itself may be a junk 0. The bound then holds through the junk value. The statement stays true, but in that setting it carries no meaning. Fix: add `[CompleteSpace E]` or prove summability first.

### GMM: `avar`, `avar_sub_posSemidef`
The matrix inequality is the right one (Hayashi Prop 3.5). However, `avar` never appears in any distributional statement: there is no √n(ĝ−β) ⇝ N(0, avar W G S), no consistency (Hayashi Prop 3.1, Newey–McFadden Thm 2.6), no two-step feasible efficient GMM, and no Hansen J-test. Calling this "efficient GMM" overstates what is formalised.
Fix: add an iid version of asymptotic normality that uses the CLT and the delta-method infrastructure, or rename and document it as the algebraic efficiency bound.

### GMM: `identified_iff`
The conjunct `criterion W G (G *ᵥ β) β = 0` is always true. This is harmless but cosmetic. Fix: drop the conjunct.

### IV: redundant hypotheses
`tsls_eq_ols_fitted`: if Z'Z is singular, `hat Z = 0` and both sides are 0, so hZ is unnecessary. `tsls_eq_iv`: if Z'X is invertible, Z has full column rank, so hZ is implied. Neither issue makes a statement wrong.

### DeltaMethod: `delta_method`
This covers only g : ℝ → ℝ. vdV Thm 3.1 covers φ : ℝ^k → ℝ^m differentiable at θ, with limit φ'_θ(T). Econometric uses such as Wald tests of nonlinear restrictions need the multivariate version.
Fix: generalise to finite-dimensional normed spaces with `HasFDerivAt g g' θ` and limit `g' ∘ Z`.

### DeltaMethod: `tendstoInMeasure_of_tendstoInDistribution_const`
vdV Thm 2.7(iii) is an iff. Fix: add the converse, since convergence in probability implies convergence in distribution.

### OLSConsistency: `ols_consistent_witness`
The witness is a Dirac measure with x ≡ 1 and ε ≡ 0, so every random object is constant. That only shows the hypotheses are jointly satisfiable in a deterministic model. Fix: use Ω = Bool with the uniform measure, x ≡ 1 and ε = ±1. That is nondegenerate, with independent coordinates via the product space ℕ → Bool. Also note that `ols_consistent` is the iid special case of Hayashi Prop 2.1, which assumes ergodic stationarity.

### SVAR: `not_identified`
The witness is a 90° rotation. It shows non-identification, but it does not show why the diagonal > 0 normalisation is in `IsRecursive`. Fix: add B₂ = diag(−1, 1). It is lower triangular with B₂B₂ᵀ = I = B₁B₁ᵀ, and B₂ ≠ B₁. Also, SVAR is not linked to VAR. Suggested: Θ_h = A^h B as structural IRF, and Σ_u = BBᵀ from u = Bε with E[εεᵀ] = I.

### RD: `sharp_rd_identified`
This statement is true. An observable conditional mean is defined only almost everywhere, and the hypothesis `∀ x ≠ c` demands equality everywhere. A version with a.e. agreement on a neighbourhood is also true: continuity at c plus agreement on a set that accumulates at c from each side is enough. The conclusion gives only τ, even though m₁(c) and m₀(c) are each identified.
Fix: use `hobs : ∀ᶠ x in 𝓝[≠] c, …`, or a.e. on `Ioo (c-δ) (c+δ)`, and conclude `m₁ c = m₁' c ∧ m₀ c = m₀' c`.

### ShiftShare: `integral_sum_bartik_mul`, `integral_sum_bartik_mul_eq_zero`
ε is deterministic. This reads BHJ's conditional statement E[g_n | ε̄, s] = μ as fixed values of ε and s, which is acceptable. What is shown is only that the SSIV numerator has mean 0. BHJ's identification result is consistency (Prop 3), which needs Assumption 2 (Σ s_n² → 0, shocks mutually uncorrelated), and none of it is here. Controls (e.g. Σ_n s_ln for incomplete shares) are replaced by the hypotheses `hcomplete`/`hε`. Fix: add a variance bound Var(Σ_n s_n g_n ε̄_n) = Σ_n s_n² ε̄_n² σ² for uncorrelated shocks. From it, derive convergence in probability of the numerator under Σ s_n² → 0.

### SyntheticControl: `estimator_eq_effect`
`hfit` uses `M.y0 Z₁ μ₁ t` for the treated unit, which is a latent object. ADH's fit condition is on observed Y_1t for t ≤ T_0, together with no anticipation (α_t = 0 for t ≤ T_0). As stated, α on pre-periods is unrestricted, and the hypothesis cannot be checked from data. Fix: replace hfit with `(∀ t ∈ pre, Y₁ t = ∑ j, w j * Y j t)` and `(∀ t ∈ pre, α t = 0)`, then derive the current hfit. Further gaps: the model is noise-free, the ADH bias bound under T_0 → ∞ is absent, and weights are unrestricted (a harmless generalisation).

## Coverage gaps (summary)
- IV/GMM: no 2SLS/GMM consistency or asymptotic normality (Wooldridge Thm 5.1–5.2, Hayashi Props 3.1–3.3), no J-test, no estimation of S.
- OLS: no asymptotic normality or robust variance (Hayashi Prop 2.1(b), 2.4).
- Delta method: univariate; no Slutsky lemma or CMT in distribution.
- VAR/SVAR: no eigenvalue/companion bridge, no autocovariances, no SVAR–VAR link.
- Shift-share: no controls, no Prop 3. GPSS: unweighted, no controls.
- Synthetic control: noise-free; no V/W optimisation.
