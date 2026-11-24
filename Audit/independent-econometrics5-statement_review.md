# Statement review, batch 5: ARMA.lean, Kalman.lean, DeltaMethodVec.lean

Scope: statements and definitions only (proofs are `sorry`). Context definitions come from VAR.lean (`IsPath`, `Stable`, `mean`, `ma`) and GaussMarkov.lean (`secondMoments`).

Overall: I found **no statement that is false** and **no hypothesis set that cannot be satisfied**. Every theorem has a nondegenerate instance; the witnesses, or the examples below, show this. The index conventions all check out: companion matrix, characteristic equation, lag polynomial and the AR recursion. Every problem is about **coverage or strength**. The file names promise ARMA, Kalman filtering and the full delta method. What is actually formalized is: a deterministic AR(p+1) with bounded forcing; the one-step Kalman measurement update and prediction algebra; and the √n-rate delta method without its asymptotic-linearity part.

## Table

| Declaration | File | Textbook reference | Verdict | Reason |
|---|---|---|---|---|
| `summable_norm_pow_iff` | ARMA | Root test + Fekete; Gelfand formula setup | OK | Holds in any seminormed ring because the norm is submultiplicative: summability gives some ‖a^N‖<1, and then ρ ≤ ‖a^N‖^{1/N} < 1. The trivial ring and the zero seminorm are both fine. |
| `spectralRadius_lt_one_iff` | ARMA | Gelfand formula (Rudin FA 10.13) | OK | Complex Banach algebra, nontrivial, complete. Strict inequality is fine because the spectrum is compact. |
| `companion` | ARMA | Hamilton (1.2.3) matrix **F** | OK | Row 0 is φ and the subdiagonal is 1s. With the state (x_t,…,x_{t-p}), φ_0 multiplies x_{t-1}. |
| `charEq` | ARMA | Hamilton Prop 1.1, eq. (1.2.21) | OK | λ^{p+1} − Σ_j φ_j λ^{p−j}, so φ_j matches Hamilton's φ_{j+1}. |
| `lagPoly` | ARMA | Hamilton (2.4), B&D φ(z) | OK | 1 − Σ φ_j z^{j+1}. |
| `companion_mulVec_zero/succ`, `eigvec_eq` | ARMA | Hamilton Prop 1.1 proof | OK | Correct algebra. |
| `exists_eigvec_iff`, `mem_spectrum_companion_iff` | ARMA | Hamilton Prop 1.1 | OK | Eigenvalues of F are the roots of charEq, over any field. |
| `charEq_eq_mul_lagPoly`, `lagPoly_zero` | ARMA | Hamilton §1.2 / §2.4 (reciprocal roots) | OK | r^{p+1}·φ(1/r) = charEq(r) for r ≠ 0. |
| `spectrum_lt_one_iff_roots` | ARMA | Hamilton Prop 1.1 + §2.4 / B&D 3.1.1 condition | OK | Degenerate φ_p = 0 (eigenvalue 0) and φ ≡ 0 (lagPoly = 1, no roots) both still hold. |
| `compCLM`, `compCLM_apply`, `compCLM_pow_apply`, `norm_compCLM_pow`, `companion_map`, `norm_map_pow` | ARMA | infrastructure | OK | The sup-norm operator norm equals the ℓ∞ matrix norm, and the ℝ→ℂ map preserves entrywise norms. |
| `stable_iff_roots_outside` | ARMA | Hamilton Prop 1.1 + (3.4.x) stationarity; B&D 3.1.1 condition | OK (see W6) | Both directions are stated. The other half of B&D 3.1.1 (causal solution ⇒ roots outside) is missing, but this theorem itself is fine. |
| `IsARMA` | ARMA | B&D Def 3.1.1 / Hamilton (3.5.1) | **MISMATCH** (naming/coverage) | This is an AR(p+1) with intercept and an arbitrary deterministic forcing w. There is no MA polynomial θ and no white-noise structure. |
| `state`, `e0`, `isPath_state`, `path_first` | ARMA | Hamilton (1.2.5) state-space form of AR(p) | OK | Index check passes: row 0 gives c + Σ φ_j x_{t−1−j} + w_t, and row i+1 gives x_{t−1−i}. |
| `norm_e0`, `norm_state_le` | ARMA | infrastructure | OK | |
| `arma_ma_solves` | ARMA | Hamilton (3.4.x) MA(∞) form; B&D Thm 3.1.1 (ψ-weights) | **WEAK** | Needs sup_t |w_t| < ∞. The conclusion is `VAR.ma … t 0` with no ψ_j = (F^j)_{00}, no ψ(z)=1/φ(z) or θ(z)/φ(z), and no μ = c/(1−Σφ). |
| `arma_unique` | ARMA | B&D Thm 3.1.1 ("unique stationary solution") | **WEAK** | Uniqueness only among bounded paths. Stationary Gaussian ARMA paths are a.s. unbounded, so the textbook's stationary-solution uniqueness is not what is stated. |
| `ar1_witness` | ARMA | sanity | OK | Shows Stable is non-vacuous and not trivially true. |
| `innovCov` | Kalman | Hamilton (13.2.12) / A–M §3.1: H P Hᵀ + R | OK | |
| `gain` | Kalman | Hamilton (13.2.19) / A–M: P Hᵀ S⁻¹ | OK (junk-guarded) | When S is singular, gain = 0. Every theorem that uses `gain` assumes `IsUnit det S`. |
| `joseph` | Kalman | Joseph stabilized form (Bucy–Joseph 1968; standard in A–M) | OK | |
| `joseph_expand` | Kalman | algebra | OK | Holds without symmetry, as stated. |
| `gain_mul_innovCov`, `innovCov_transpose`, `innovCov_mul_gain_transpose` | Kalman | algebra | OK | |
| `joseph_sub_gain` | Kalman | completion of squares | OK | Checked by hand: both sides equal KSKᵀ − KHP − PHᵀKᵀ + PHᵀS⁻¹HP. |
| `joseph_gain` | Kalman | Hamilton (13.2.16) P_{t|t} | OK | |
| `innovCov_posSemidef` | Kalman | | OK | |
| `kalman_gain_optimal` | Kalman | Kalman 1960 / A–M §3.1 / Hamilton §13.2 optimality | **WEAK** | Loewner-minimal only among gains K in the fixed "prior + K·innovation" form. There is no uniqueness (S ≻ 0 ⇒ K = gain), no optimality among all affine estimators, and no conditional-expectation optimality. |
| `update_error` | Kalman | algebra | OK | The prior mean is a deterministic vector. |
| `secondMoments_update_error` | Kalman | A–M (3.1.x) / Hamilton (13.2.16) | OK | It uses the second-moment (MSE) matrix, not the covariance. That is right for MSE. Uncorrelatedness of e and v is encoded as the 0 off-diagonal blocks. |
| `secondMoments_predict` | Kalman | Hamilton (13.2.21) P_{t+1|t} = F P Fᵀ + Q | OK | |
| `kalman_witness` | Kalman | sanity | OK | 1×1 case with P = H = R = 1: S = 2, K = ½, P⁺ = ½. Hypotheses are satisfiable. |
| (file as a whole) | Kalman | Hamilton ch. 13, A–M ch. 3–4 | **COVERAGE GAP** | No state-space model, no filter recursion over t, no Riccati iteration, no x̂_{t|t} = E[x_t \| y_{1:t}], no steady state. |
| `tendstoInMeasure_of_tendstoInDistribution_const_pi` | DMV | vdV Thm 2.7(iii) | OK | |
| `tendstoInMeasure_of_sqrt_pi` | DMV | vdV Thm 2.7 / Lemma 2.12 (tightness) | OK | No measurability is needed on T_0. TendstoInDistribution provides it for √n(T_n−θ). |
| `remQuot`, `remQuot_continuousAt`, `remQuot_measurable`, `smul_sub_eq_remQuot` | DMV | proof infrastructure (o(‖h‖) remainder) | OK | Checked for t = θ and for t ≠ θ with s ≥ 0. |
| `delta_method_vec` | DMV | vdV Thm 3.1; Hayashi Lemma 2.5(c) | **WEAK** | Rate is fixed at √n (vdV allows r_n → ∞). The second assertion of vdV 3.1 (r_n(φ(T_n)−φ(θ)) − φ'(r_n(T_n−θ)) →_p 0) is missing. It adds `Measurable g`, which vdV does not need. Otherwise faithful, and it uses HasFDerivAt, which is weaker than Hayashi's C¹. |
| `delta_method_gaussian` | DMV | Hayashi Lemma 2.5 "in particular" clause; vdV Example 3.2-type | OK (naming) | Just the law of a linear map of a Gaussian, J S Jᵀ. Not a delta method by itself, and there is no combined theorem. Correct as stated. `IsProbabilityMeasure P'` is omitted, but hlaw forces it. |

## Non-OK items in detail

### M1. `IsARMA` is an AR(p+1), not an ARMA(p, q)
Definition: `∀ t, x t = c + ∑ j, φ j * x (t-1-j) + w t`. There are no MA coefficients θ_1..θ_q and no innovation sequence ε. ARMA can be recovered only by setting `w t := ε t + Σ θ_i ε (t-i)` by hand, and the file never does this.

So B&D Thm 3.1.1 is **not** stated. That theorem says: an ARMA(p,q) with φ, θ having no common zeros is causal iff φ(z) ≠ 0 for |z| ≤ 1, and then ψ(z) = θ(z)/φ(z). The name `IsARMA` and the section names suggest it is covered.

The minimum order is also AR(1), because of `Fin (p+1)`. A pure MA(q) or white noise (p = 0 lags) cannot be expressed. Not a soundness issue, but a downstream user who writes `IsARMA` expecting θ will be misled.

Example: ARMA(1,1) x_t = 0.5 x_{t-1} + ε_t + 0.4 ε_{t-1}. In this file the only encoding is `IsARMA 0 (fun _ => 0.5) (fun t => ε t + 0.4*ε (t-1)) x`. The ψ-weights ψ_0 = 1 and ψ_j = 0.9·0.5^{j-1} appear in no statement.

### W1. `arma_ma_solves` / `arma_unique`: deterministic bounded paths, not stationary processes
Both theorems quantify over all t ∈ ℤ with `|w t| ≤ M` (respectively `|x t| ≤ K`).

Example: let ε_t be iid N(0,1). Then sup_{t∈ℤ} |ε_t| = ∞ almost surely, so `hw` fails for almost every sample path. The theorems therefore say nothing about almost every realization of the canonical Gaussian AR(1) x_t = 0.5 x_{t-1} + ε_t.

Likewise, the stationary solution x_t = Σ 0.5^j ε_{t-j} is a.s. unbounded, so `arma_unique` does not apply to it.

The textbook uniqueness (B&D 3.1.1: "the unique stationary solution") is about L² / strictly stationary solutions. That is a different statement: for example, B&D prove it via the L²-convergent series for φ(B)^{-1}. The bounded-sequence version is a correct and useful deterministic analogue, but it is not the canonical theorem.

A faithful version would use pathwise solutions with sup_t E|w_t| < ∞ (or L²), or a.s. statements for stationary w.

### W2. `arma_ma_solves` does not state the MA(∞) coefficients or the mean
The conclusion is `IsARMA c φ w (fun t => VAR.ma (e0 c) (compCLM φ) (fun s => e0 (w s)) t 0)` plus boundedness. Unfolding gives x_t = (mean)_0 + Σ_j (F^j)_{00} w_{t-j}.

None of the textbook content is stated about this:
- ψ_j = (F^j)_{11} (Hamilton Prop 1.2 / (1.2.28));
- Σ|ψ_j| < ∞ (Hamilton (3.3.x)) as a statement about ψ;
- ψ(z)·φ(z) = 1;
- μ = c / (1 − φ_0 − … − φ_p) (Hamilton (3.4.24)).

All of these are coverage gaps for Hamilton ch. 3. Similarly, there are no autocovariances and no Yule–Walker equations, which is the bulk of ch. 3.

### W6 (from the `stable_iff_roots_outside` row). Missing converse and the non-causal case
`stable_iff_roots_outside` gives Stable ⇔ roots outside the unit circle. Nothing states the B&D direction "if a bounded/stationary causal solution exists for all admissible w, then the roots are outside". Nothing treats the case of roots strictly inside the circle, where B&D Example 3.1.2 / Thm 3.1.3 give a non-causal stationary solution. Nothing treats the unit-root case (no stationary solution).

`ar1_witness` only shows ¬Stable for φ = 1. It does not show that no bounded solution exists. Counter-check: for φ = 1, c = 0, w ≡ 0, the constant path x ≡ 5 is a bounded solution, as is any constant. So uniqueness fails, consistent with ¬Stable. No such statement is present, though.

### W3. `kalman_gain_optimal`: optimality class is narrow
Statement: for symmetric PSD P and R with S invertible, joseph(K) − joseph(gain) ⪰ 0 for every K. Combined with `secondMoments_update_error`, this gives Loewner-minimal MSE among estimators of the form `mean + K (y − H mean)` with a deterministic `mean`. Missing:
1. **Uniqueness.** If S ≻ 0, joseph(K) = joseph(gain) ⇒ K = gain. Not stated; only ⪰ is given.
2. **Optimality among all affine estimators a + B y.** For such an estimator the error is (1−BH)e − Bv + ((1−BH)mean − a). If e and v are not mean-zero, the second moment includes a bias term and a cross term. The file never assumes E e = E v = 0, so it cannot even state this.
3. **Kalman 1960 / A–M §3.1 Gaussian result:** the update equals E[x | y] and is optimal among all measurable estimators. Not stated.

### C1. Kalman.lean is not a Kalman filter
There is no `structure` for the state-space model x_{t+1} = F x_t + w_t, y_t = H x_t + v_t. There is no recursive definition of (x̂_{t|t}, P_{t|t}, x̂_{t+1|t}, P_{t+1|t}) and no Riccati map P ↦ F(P − PHᵀS⁻¹HP)Fᵀ + Q. There is no statement that the filtered mean is the (linear) projection of x_t on y_1..y_t (Hamilton §13.2). There is no convergence to a steady-state P (Hamilton Prop 13.1, A–M ch. 4).

The file proves the single-step measurement update (`joseph_*`, `secondMoments_update_error`) and the single-step time update (`secondMoments_predict`) separately. Gluing them across t, which requires the new error and the new noise to be uncorrelated, is never stated.

Junk check: `gain` = 0 when S is singular, so joseph(0) = P. No theorem exploits this, because every `gain` theorem carries `hS`. There is also no lemma `R.PosDef → IsUnit (innovCov P H R).det`, which is the textbook's actual hypothesis. Users must discharge `hS` by hand.

### W4. `delta_method_vec`: √n only; asymptotic-linearity part missing
van der Vaart Thm 3.1 states it for arbitrary r_n → ∞ and has two conclusions. (i) r_n(φ(T_n)−φ(θ)) ⇝ φ'_θ(T). (ii) r_n(φ(T_n)−φ(θ)) − φ'_θ(r_n(T_n−θ)) → 0 in probability. Only (i) is stated, and only for r_n = √n. Part (ii) is the form used in practice to stack delta-method results with other estimators (joint convergence / Slutsky). Its absence is a coverage gap.

The extra hypothesis `Measurable g` is harmless for Borel g. It is a strengthening relative to vdV, who works with outer expectations.

Hayashi Lemma 2.5's "in particular N(0, A Σ Aᵀ)" is obtained only by composing `delta_method_vec` with `delta_method_gaussian`. No single theorem states √n(g(T_n) − g(θ)) →_d N(0, J Σ Jᵀ). The `delta_method_clt` analogue that exists for the scalar case has no vector counterpart.

### Naming: `delta_method_gaussian`
This is purely the law of a linear transform of N(0,S). It is a duplicate of `map_mulVec_of_gaussian` with the Jacobian in place of A. It is correct, but the name overstates it.

## Satisfiability examples (nondegeneracy)
- ARMA: p = 0, φ = ½, c = 1, w_t = (−1)^t. Then Stable holds (`ar1_witness`), w is bounded with M = 1, and the bounded solution is x_t = 2 + Σ_j ½^j (−1)^{t−j} = 2 + (2/3)(−1)^t. Check: 2 + (2/3)(−1)^t = 1 + ½(2 + (2/3)(−1)^{t−1}) + (−1)^t holds, since ½·(2/3)(−1)^{t−1} = −(1/3)(−1)^t. All hypotheses of `arma_ma_solves` and `arma_unique` are non-vacuous.
- Kalman: `kalman_witness` (P = H = R = 1). For `secondMoments_update_error`, take Ω = Bool × Bool with the uniform measure, e = ±1 and v = ±1 independent. The second moments are fromBlocks 1 0 0 1. Hypotheses are satisfiable.
- Delta method: T_n = sample mean of iid N(θ,1), Z ~ N(0,1), g(t) = t². All hypotheses hold, and the conclusion gives N(0, 4θ²). The case θ = 0 gives a degenerate N(0,0) limit, consistent with the statement (a point mass).
