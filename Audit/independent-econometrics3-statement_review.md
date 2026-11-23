# Adversarial statement review: round 3 (new files)

Scope: GaussMarkov.lean, Causal/GoodmanBacon.lean, Asymptotics/Extremum.lean,
Asymptotics/GMMAsymptotics.lean, TimeSeries/SVARRestrictions.lean, Structural/BLP.lean.
Only statements and definitions were judged (proofs are `sorry`). Mathlib checks I made:
`klDiv` (= `ofReal(∫ llr + ν univ − μ univ)` if `μ ≪ ν` and integrable, else `∞`;
`klDiv_eq_zero_iff` for finite measures), `TendstoInMeasure` (`μ {ε ≤ edist}`; this is the
outer measure on non-measurable sets), `TendstoInDistribution` (a structure that requires
AEMeasurable terms and limit plus weak convergence of the laws), `IsGaussian` (degenerate laws,
Dirac included, count as Gaussian), and `multivariateGaussian μ S` on `EuclideanSpace`.

**Headline: I found no statement that is false, and no theorem that is vacuous.** Every
theorem I checked by hand computation is true as stated. Several junk-value traps are guarded
correctly: `hX`, `hA`, `hfin` (which stops `toReal ⊤ = 0`), `hden` and `hrank`. The problems are
**fidelity gaps**: some conclusions are weaker than the cited result, and some theorem names
promise more than the statements deliver.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `cov` | GaussMarkov | Hayashi §1.1 | OK | Bochner covariance; the hypotheses guard integrability |
| `secondMoments` | GaussMarkov | Hayashi A1.4 | OK | E[εεᵀ]; equals Var(ε) under mean zero |
| `integral_mulVec`, `integral_mulVec_mul_mulVec`, `integral_linear` | GaussMarkov | helpers | OK | true linearity facts |
| `unbiased_iff` | GaussMarkov | Hayashi Prop 1.1 setup | OK | unbiased for every β ⇔ CX = I; needs a probability measure, which is supplied |
| `cov_linear` | GaussMarkov | Hayashi (1.3.x) | WEAK | hypothesis `hC : C*X = 1` is unnecessary (Var(Cy) = CΣCᵀ for any C) |
| `ols_eq_mulVec` | GaussMarkov | def | OK | |
| `cov_ols` | GaussMarkov | Hayashi Prop 1.1(b) | OK | σ²(XᵀX)⁻¹; `hX` prevents the junk inverse |
| `gauss_markov` | GaussMarkov | Hayashi Prop 1.1(c) | WEAK | correct, but for fixed (non-random) X only; Hayashi conditions on X. σ² ≥ 0 is implicit (diagonal of E[εεᵀ]), and the case n = ∅ forces k = ∅, which is fine |
| `gaussMarkov_witness` | GaussMarkov | sanity check | WEAK | n = Unit, so no X with k ≥ 2 has invertible XᵀX; the witness never exhibits X, hX and C together |
| `dm`, `pairNum`, `pairVar`, `pairCoef`, `baconWeight` | GoodmanBacon | GB (2021) §2 | WEAK | **unit-pair** objects, not GB timing-group 2×2s; `pairCoef = 0/0 = 0` junk is harmless (weight 0) |
| `isTWFE_coef` | GoodmanBacon | FWL for TWFE | OK | b = Σε̃Y/Σε̃D |
| `eps_eq_dm`, `sum_centered_mul_eq_pairs`, `sum_eps_mul_eq_pairs` | GoodmanBacon | algebra | OK | checked by hand |
| `pairNum_self`, `pairVar_nonneg`, `pairNum_eq_zero_of_pairVar` | GoodmanBacon | algebra | OK | |
| `baconWeight_nonneg`, `sum_baconWeight` | GoodmanBacon | GB Thm 1 (weights ≥ 0, Σ = 1) | OK | ordered pairs, so each unordered pair is split into two halves (cosmetic) |
| `goodman_bacon` | GoodmanBacon | GB (2021) Thm 1 | MISMATCH (true but coarser) | decomposes into all-period two-unit TWFE coefficients over unit pairs; GB Thm 1 decomposes into timing-group 2×2 DDs on **restricted windows** (β^k_kl on PRE+MID, β^l_kl on MID+POST); the "already-treated as control" term is never isolated |
| `pairCoef_eq_twfe` | GoodmanBacon | GB eq. (3)/(6) | OK | two-unit TWFE coefficient = pairCoef (checked) |
| `pairCoef_indicator` | GoodmanBacon | GB eq. (6)–(8) | WEAK | gives mean_P Δ − mean_{Pᶜ} Δ; for an early/late pair, Pᶜ = PRE ∪ POST pools the clean and forbidden comparisons; the split is not stated |
| `Example.bacon_witness` | GoodmanBacon | illustration | OK | value −1/2 checked: ΔY = (0,1,3), so 1 − 3/2 |
| `extremum_consistent` | Extremum | N-M Thm 2.1; Hayashi Prop 7.1 | OK | approximate maximiser with o_p(1) slack; ULLN stated in outer probability (N-M convention); no probability-measure assumption is needed |
| `klDiv_pos_of_identified` | Extremum | N-M Lemma 2.2 (core) | OK | follows from Mathlib `klDiv_eq_zero_iff` for finite measures |
| `mle_unique_max` | Extremum | N-M Lemma 2.2 | WEAK | the bridge Q₀(θ₀) − Q₀(θ) = KL is **assumed** (`hgap`), not derived from E ln f; `hfin` correctly blocks the `toReal ⊤ = 0` junk |
| `mle_consistent` | Extremum | N-M Thm 2.5 | WEAK | `Q` is arbitrary (no likelihood, no data, no iid, no dominance); this is just `extremum_consistent` plus `mle_unique_max`, so the name overclaims |
| `tendstoInMeasure_comp_continuousAt`, `_prodMk`, `_sub_of_eq_near` | Extremum | CMT / helpers | OK | outer-measure monotonicity makes them true without measurability |
| `tendstoInDistribution_mulVec` | Extremum | Slutsky | OK | constant limit A₀; measurability supplied |
| `exists_ball_isUnit_det`, `continuousAt_inv_of`, `measurable_inv_of` | Extremum | helpers | OK | |
| `z_estimator_asymptotic` | Extremum | N-M Thm 3.1; Hayashi Prop 7.8 | WEAK | correct sign (−H₀⁻¹L); but the exact expansion `hexp` must hold for **every** n, ω (N-M only needs w.p.→1), and the conclusion never gives the variance H⁻¹ΣH⁻¹ᵀ |
| `z_estimator_gaussian` | Extremum | N-M Thm 3.1 (normality) | WEAK | only "a linear image of a Gaussian is Gaussian"; no mean 0, no covariance; true even for singular H₀ (junk inverse 0 gives Dirac, which is Gaussian) |
| `gram`, `cross`, `gmmA`, `continuous_*`, `continuousAt_gmmA`, `measurable_gmmA`, `exists_ball_rank` | GMMAsymptotics | helpers | OK | `gmmA` is junk 0 off rank; all uses are guarded or harmless |
| `estimator_eq_gmmA`, `estimator_sub` | GMMAsymptotics | Hayashi (3.5.x) | OK | sampling-error identity |
| `gmm_consistent` | GMMAsymptotics | Hayashi Prop 3.1 | OK | the rank condition GᵀW₀G invertible is weaker than (W₀ ≻ 0 and full column rank), so the statement is more general |
| `gmm_asymptotic_normal` | GMMAsymptotics | Hayashi Prop 3.3(a) | WEAK | limit given as A·L with A = (GᵀW₀G)⁻¹GᵀW₀; never says Avar = sandwich when Var(L) = S |
| `gmm_limit_gaussian` | GMMAsymptotics | Prop 3.3 | WEAK | same as `z_estimator_gaussian`; no covariance |
| `avar_eq_sandwich` | GMMAsymptotics | Hayashi (3.5.1) | OK as algebra | but it is not linked to the law of the limit |
| `longRunMultiplier` | SVARRestrictions | K-L ch. 10; BQ (1989) | OK | A(1)⁻¹; junk 0 when singular, guarded by `hA` |
| `IsLongRunRecursive` | SVARRestrictions | BQ (1989) | OK | Ψ(1)B lower triangular with positive diagonal |
| `posDef_congr`, `longRun_unique`, `longRun_existsUnique`, `blanchardQuah` | SVARRestrictions | BQ / K-L Prop 10.x | OK | Cholesky of Ψ S Ψᵀ, then Ψ⁻¹ |
| `obsEquiv_iff_orthogonal` | SVARRestrictions | RWZ (2010) Thm 1-ish; Uhlig | OK | |
| `SignOK` | SVARRestrictions | Uhlig (2005); K-L ch. 13 | WEAK | **impact** (h = 0) only; Uhlig restricts responses at horizons 0..K |
| `identifiedSet`, `identifiedSet_eq` | SVARRestrictions | K-L §13.x | OK (given SignOK) | |
| `sign_restrictions_set_identify` | SVARRestrictions | illustration | OK | B₂B₂ᵀ = 2c²I = I checked |
| RWZ (2010) identification theory | SVARRestrictions | RWZ Thms 1, 7 | COVERAGE GAP | no rank condition and no QR/Haar draw |
| `share`, `outsideShare`, `denom_pos`, `share_pos`, `outsideShare_pos`, `sum_share_add_outside` | BLP | logit with δ₀ = 0 | OK | |
| `berry_inversion` | BLP | Berry (1994) eq. (9)/(13) | OK | |
| `share_surjective`, `share_injective` | BLP | Berry (1994) | OK | logit is a bijection onto the open simplex |
| `share_set_lt` | BLP | helper (BGH-style) | OK | needs e^M > 1; checked |
| `mixedShare` | BLP | BLP (1995) RC logit | WEAK | finitely many consumer types only; weights not required to sum to 1 |
| `exists_set_share_lt`, `mixedShare_injective` | BLP | BGH (2013) Thm 1; Berry (1994) uniqueness | WEAK | uniqueness only; **existence** (onto the simplex) and the BLP contraction are missing |
| `mixedShare_unit`, `mixed_witness` | BLP | sanity check | OK | witness shows type heterogeneity but not an IIA violation |

## Details for non-OK items

### 1. `goodman_bacon`: true, but it is not Goodman-Bacon's Theorem 1 (MISMATCH)
Statement: `b = ∑ g, ∑ h, baconWeight D g h * pairCoef D Y g h`, where `pairCoef` is the
two-**unit** TWFE coefficient over **all** T periods (`pairCoef_eq_twfe`). I verified it by hand:
ε̃_gt = dm_gt − mean_h dm_ht, then Σ_g(a_g − ā)b_g = ΣΣ(a_g − a_h)(b_g − b_h)/(2N), then
substitute. GB Theorem 1 is stated over timing groups k, l and uses 2×2 DDs on restricted windows:
β̂^k_kl (early k vs not-yet-treated l, on PRE+MID) and β̂^l_kl (late l vs already-treated k, on
MID+POST). The weights are s_kU ∝ n_k n_U D̄_k(1−D̄_k) and so on. The formal statement:
- never splits the early/late pair. `pairCoef_indicator` with P = MID gives
  mean_MID Δ − mean_{PRE∪POST} Δ. That equals s·β^k + (1−s)·β^l with s = |PRE|/(|PRE|+|POST|),
  but the identity is not stated. This split is the result's main point (the "forbidden
  comparison");
- never aggregates units into timing groups, and never states the group-level weight formula in
  terms of n_k and D̄_k(1−D̄_k).

The example confirms the gap. In `bacon_witness`, ΔY = (0,1,3) and P = {1}:
pairCoef = 1 − (0+3)/2 = −1/2. The split is s = 1/2: β^k = 1 − 0 = 1 and β^l = 1 − 3 = −2, giving
(1 + (−2))/2 = −1/2. The negative "late vs already-treated" term is exactly what GB highlights, and
the library cannot state it.

Fix: add a lemma
`pairCoef_split (hD : ∀ t, D g t − D h t = if t ∈ MID then 1 else 0) (hpart : PRE ∪ POST = MIDᶜ, Disjoint PRE POST, …) : pairCoef D Y g h = s * (meanMID − meanPRE) + (1−s) * (meanMID − meanPOST)`.
Then add a group-level corollary for staggered binary D (D g t = 1[t ≥ e g]) that sums over
cohorts with weights ∝ n_k n_l · pairVar.

### 2. `z_estimator_asymptotic` / `z_estimator_gaussian`: no covariance (WEAK)
N-M Thm 3.1 concludes √n(θ̂−θ₀) →d N(0, H⁻¹ΣH⁻¹). Here the limit is only "−H₀⁻¹L", and
Gaussianity is the bare fact that a linear image of a Gaussian is Gaussian. That fact is true even
for singular H₀ (Mathlib's inverse is 0, which gives δ₀, and a Dirac is `IsGaussian`), and true even
when L has a non-zero mean.
Fix: add `(hL : P'.map L = (multivariateGaussian 0 Σ).map WithLp.ofLp)` and conclude
`P'.map (fun ω => -(H₀⁻¹ *ᵥ L ω)) = (multivariateGaussian 0 (H₀⁻¹ * Σ * H₀⁻¹ᵀ)).map WithLp.ofLp`,
or at least state the mean (0) and `covarianceBilin`.

### 3. `z_estimator_asymptotic` `hexp` must hold for every n, ω (WEAK)
The first-order condition holds only when θ̂ is interior, which N-M get with probability → 1.
A user must re-define S_n on the bad event, and then re-prove the CLT for the modified S_n.
Fix: weaken to `TendstoInMeasure P (fun n ω => √n • (S n ω + H n ω *ᵥ (θhat n ω − θ₀))) atTop 0`,
or to `Tendsto (fun n => P {ω | S n ω + … ≠ 0}) atTop (𝓝 0)`.

### 4. GMM: the sandwich is never tied to the limit law (WEAK)
`gmm_asymptotic_normal` gives A·L, and `avar_eq_sandwich` is a matrix identity, but nothing says
Var(A L) = A S Aᵀ = `avar W₀ G S` when Var(L) = S. As a result, Hayashi Prop 3.3(a)'s variance and
Prop 3.5 (efficiency, in GMM.lean) do not connect to any distributional statement.
Fix: as in item 2, add `gmm_asymptotic_normal'` with the hypothesis `L ∼ N(0,S)` and conclusion
`law = N(0, GMM.avar W₀ G S)` (requires `W₀ᵀ = W₀`).

### 5. `mle_consistent` / `mle_unique_max`: the likelihood is absent (WEAK)
`Q : ℕ → Ω → Θ → ℝ` is arbitrary, and the information-inequality bridge (`hgap`) is a hypothesis.
N-M Thm 2.5's content lies in two steps: (a) Q₀(θ) = E_{θ₀} ln f(z|θ), so that
Q₀(θ₀) − Q₀(θ) = KL; (b) the dominance condition E sup|ln f| < ∞, which delivers the ULLN and
continuity. Step (a) is assumed and step (b) is replaced. The name overclaims; the theorem equals
`extremum_consistent` with `hid` discharged by `mle_unique_max`.
Fix: define `Q₀ θ := ∫ x, Real.log (f θ x) ∂(Pθ θ₀)` for densities f with `Pθ θ = (Pθ θ₀).withDensity …`,
and prove `hgap` from `integral_llr`; or rename it `extremum_consistent_of_klDiv`.

### 6. BLP: uniqueness without existence (WEAK)
`mixedShare_injective` matches BGH (2013) Thm 1 and Berry (1994) uniqueness, restricted to a
**finite** type distribution. The canonical result also asserts existence (every s in the open
simplex is attained) and the contraction δ ↦ δ + ln S − ln s(δ) (BLP 1995, App. I). Existence is
proved only for plain logit (`share_surjective`).
Fix: `theorem mixedShare_surjective (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) {s} (hs : ∀ j, 0 < s j) (h1 : ∑ j, s j < 1) : ∃ δ, mixedShare w μ δ = s`.
Optionally add a `Measure`-mixture version: `∫ share (δ + μ) dF(μ)`.

### 7. `SignOK` covers impact only (WEAK) and RWZ is not covered (gap)
Uhlig (2005) restricts the responses Θ_h = Φ_h B for h = 0..K. With impact-only restrictions,
the identified set is larger than Uhlig's whenever K > 0. RWZ (2010) is cited, but its theorems
(the rank condition for exact identification under zero restrictions; the QR/Haar algorithm) are
absent. `obsEquiv_iff_orthogonal` is only the common starting point.
Fix: `def SignOKh (Φ : ℕ → Matrix n n ℝ) (K : ℕ) (R : Set (ℕ × n × n × ℝ)) B := ∀ r ∈ R, r.1 ≤ K → 0 ≤ r.2.2.2 * (Φ r.1 * B) r.2.1 r.2.2.1`.
Then restate `identifiedSet_eq`, and either add the RWZ rank condition or drop the citation.

### 8. Gauss–Markov fixed design and witness (WEAK)
Hayashi Prop 1.1 is conditional on X; here X is deterministic, which is acceptable for a
fixed-regressor version but should be labelled as such. `cov_linear` carries a superfluous `hC`.
`gaussMarkov_witness` does not show that `hX` and `hC` are satisfiable together with the error
assumptions for k ≥ 2. Prop 1.1(d) (Cov(b, e) = 0) and Prop 1.2 (E s² = σ²) are not stated.
Fix: drop `hC` from `cov_linear`. Extend the witness with n = Fin 2, k = Unit, X = ![1,1] and
C = ![1,0] (CX = 1), using an iid ±1 sign on Fin 2 → Bool. Add `E[s²] = σ²`.

### 9. GMM coverage gaps
Not covered: Hayashi Prop 3.4 (consistent estimation of Avar / S), Prop 3.6 / Hansen (1982)
Thm 3.1 (J statistic →d χ²(l − k)), two-step efficient GMM with Ŵ = Ŝ⁻¹ →p S⁻¹, and nonlinear GMM
(N-M Thm 3.2). Nonlinear GMM could be derived from `z_estimator_asymptotic` with
S_n = Ĝᵀ Ŵ ĝ(θ₀) and H_n = Ĝ(θ̂)ᵀ Ŵ Ĝ(θ̄); this is not stated.

### 10. Minor
- `baconWeight` sums over ordered pairs, including g = h. The diagonal is 0 and each unordered
  pair gets two halves. This is harmless, but readers comparing with GB's s_kl should know.
- `mixedShare` does not require Σw = 1, so it is a share only when normalised. Injectivity does not
  need the normalisation; the definition's name suggests it.
- `extremum_consistent` uses P of a possibly non-measurable set, which is an outer measure. That
  matches N-M's outer-probability convention and only strengthens the hypothesis. OK.
