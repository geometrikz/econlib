# Statement review: FirstStepGMM, KalmanRecursion, YuleWalkerPD, WhiteNoise

Scope: statements only (proofs are `sorry`). The dependencies TwoStepGMM, GMMAsymptotics, JTest, GMM, GaussianLimits, Kalman, GaussMarkov and YuleWalker were read for context.

Verdict scale: **defect** means the statement fails its stated purpose. **concern** means the statement is correct but weaker than, or different from, the canonical result. **OK** means it matches the textbook.

---

## 1. Defects

### D1. `two_step_feasible_witness` (Asymptotics/FirstStepGMM.lean, l.162) is degenerate and does not exercise the theorem
- **Verdict: defect.**
- The witness uses `l = k = Fin 1`, which is **just-identified**. With l = k, `GMM.estimator W G s = G⁻¹ s` for every weight W. So:
  - `twoStep = firstStep`. The second step, the residual-based Ŝ(θ̃) and `secondWeight` have no effect on the estimator.
  - `jStat ≡ 0`, `jForm S G = 0` and l − k = 0. The J-test conjuncts of `two_step_feasible` are trivial in this case, and the witness does not even state them.
  - Efficient weighting cannot be told apart from any other weighting.
- The "data" are not a sample in any meaningful sense:
  - `y_i = ω/√n + wEps n i`. A **single** N(0,1) draw ω is shared by every observation.
  - The "errors" `wEps` are **deterministic** spikes ±√(n/2) at i = 0 and i = 1, and zero elsewhere.
  - Hence `√n · ḡ(0) = ω` exactly for every n, so the CLT hypothesis `hg` is an identity rather than a limit.
  - `Ŝ(0) = 1 + ω²/n` converges only because of the deterministic spikes. This is a triangular array that fails Lindeberg, not an i.i.d./ergodic GMM sample.
- The first-step weight is the constant `fun _ _ => 1`. Instruments and regressors are constant (`z = x = 1`).
- Net effect: the witness shows only that the hypotheses are jointly satisfiable in a trivial just-identified location model. It does **not** witness the feasible two-step or J-test content.
- **Fix:** take l = 2 and k = 1, for example `z_i = (1, w_i)` and `x_i = 1`, with genuinely random errors. The i.i.d. Rademacher `rad` from `WhiteNoise.lean` is enough for an LLN/CLT-free construction if the moments are arranged to be exact. Also state the J conjunct, which has mean l − k = 1.
- Ref: Hansen (1982) Thm 3.1 and Lemma 4.2; Hayashi Prop 3.5–3.6.

No other outright defects were found.

---

## 2. Concerns

### C1. `two_step_feasible` (and `two_step_jtest`, `integral_jLimit`): the J limit is characterised only by its mean
- **Verdict: concern** (the conclusion is weaker than the canonical result).
- The J conjunct proves `J_n ⇒ L'·jForm·L` and, if L ~ N(0,S), that `E[L'·jForm·L] = l − k`.
- Hansen's theorem is `J_n ⇒ χ²(l − k)`. A mean of l − k is far weaker; for example, it does not give test size.
- The algebra needed is already proved:
  - `jForm_mul_S_mul` gives J S J = J, so S^{1/2} J S^{1/2} is an idempotent projection.
  - `trace_jForm_mul` gives its rank, l − k.
- What remains is the law of a Gaussian quadratic form with an idempotent matrix, or equality of the characteristic function / moment generating function with χ².
- Ref: Hansen (1982) Lemma 4.2; Hayashi Prop 3.6; Newey–McFadden §9.5.

### C2. `riccati_steady_state` (TimeSeries/KalmanRecursion.lean, l.197) assumes the boundedness it should derive
- **Verdict: concern** (a hypothesis assumes what should be derived, and the conclusion is weaker than the textbook's).
- `hM : ∀ t, M − P_t ⪰ 0` (uniform upper bound) is the substantive part of the canonical theorem. Monotone bounded PSD sequences converge, so the rest follows by continuity.
- The canonical theorems derive boundedness from structural conditions:
  - Hamilton Prop 13.1: eigenvalues of F inside the unit circle.
  - Anderson & Moore §4.4: (F, H) detectable.
- They also deliver more than this statement does:
  - convergence from **any** P₀ ⪰ 0, not just P₀ = 0;
  - **uniqueness** of the PSD stabilising solution of the algebraic Riccati equation (ARE) under stabilisability of (F, Q^{1/2});
  - stability of the closed loop F(I − K∞H).
- None of these is stated. As written, the theorem is just the monotone convergence theorem plus continuity.
- Cheap partial fix for |λ(F)| < 1:
  - `kalman_gain_optimal` with K = 0 gives `riccati P ⪯ F P Fᵀ + Q`.
  - By induction, P_t ⪯ Σ_{j<t} F^j Q F'^j ⪯ Σ_j F^j Q F'^j, which supplies M.
- Ref: Hamilton §13.5 Prop 13.1–13.2; Anderson & Moore §4.4.

### C3. `kalman_filter_mse` (l.224): correct MSE recursion, but no optimality statement
- **Verdict: OK as stated, concern relative to its name or purpose.**
- The model matches Hamilton (13.1.1–13.1.4), with Hamilton's H′ written here as H. The predictor `x̂_{t+1|t} = F(x̂ + K_t(y − Hx̂))` matches.
- The noise hypotheses are complete and canonical:
  - white v and w;
  - v ⟂ w at all leads and lags;
  - initial error ⟂ all v and w.
- Because `riccati` is defined through the Joseph form, the identity holds even where `innovCov` is singular. That is harmless.
- `IsProbabilityMeasure` is not required. This is harmless, because only second moments are used.
- Missing (Kalman 1960): for **any** gain sequence (K_t), MSE_t ⪰ covSeq t. This follows cheaply by induction from `joseph_sub_gain` / `kalman_gain_optimal` and `riccati_mono`, and it is the actual optimality claim of the filter.
- Ref: Kalman (1960); Hamilton §13.2 eqs. 13.2.15–13.2.22; Anderson & Moore §3.1.

### C4. `toeplitz_posDef` (TimeSeries/YuleWalkerPD.lean, l.98): non-standard sufficient condition
- **Verdict: concern** (the statement is correct).
- The hypothesis is that there exists ε with E[ε_t x_s] = 0 for s < t and E[ε_t x_t] = σ² > 0. ε is not tied to x by any model equation.
- I checked that this does imply positive definiteness:
  - If a′Γa = 0, then the latest x with a nonzero coefficient is a.s. a linear combination of earlier x's.
  - Pairing that x with its ε gives σ² = 0, which is a contradiction.
- So the statement is right; it is a "not linearly deterministic" condition.
- It is not Brockwell & Davis Prop 5.1.1, whose hypothesis is purely on γ: γ(0) > 0 and γ(h) → 0 ⇒ Γ_n nonsingular for all n. A docstring citing B&D 5.1.1 would be inaccurate.
- B&D 5.1.1 itself is missing. It is cheap given `toeplitz_quadForm`, with the γ(h) → 0 argument done on Γ only.

### C5. `white_noise_witness` (YuleWalkerPD.lean, l.114) is degenerate
- **Verdict: concern.**
- With x = ε = Rademacher and φ = 0, Γ_q = I. Positive definiteness of the identity is trivial, and no off-diagonal autocovariance is exercised.
- The witness does establish that the hypotheses of `toeplitz_posDef` are jointly satisfiable, so the theorem is not vacuous.
- Cheap non-degenerate alternative: an MA(1) process `x_t = rad t + ½·rad (t−1)` with ε_t = rad t.
  - Then γ(0) = 5/4 and γ(±1) = 1/2.
  - `Innovation` holds with σ² = 1.
  - Γ is a genuine tridiagonal Toeplitz matrix.

### C6. `sHat_consistent` (FirstStepGMM.lean, l.52): high-level, somewhat stronger-than-needed hypotheses
- **Verdict: OK, minor concern.**
- `sHat` is the uncentred residual-based estimator (1/N) Σ ε̂_i² z_i z_iᵀ, as in Hayashi 3.5.10 (HC0 / White meat). The z/x roles are swapped relative to Hayashi, which is fine.
- `expandS` correctly encodes ε̂² = ε² − 2ε·xᵀd + (xᵀd)².
- `h1` and `h2` require the cross terms (1/N) Σ ε x z z and (1/N) Σ x x z z to converge to constants. Hayashi instead derives them from a finite-fourth-moment assumption, E[(x_ik z_i)²] < ∞, plus the ergodic LLN. Only O_p(1) is actually needed.
- The constants A1 and A2 are not required to have any particular value, which is good: no spurious E[εxzz] = 0 condition.
- Ref: Hayashi Prop 3.4; White (1980) Thm 1.

### C7. `riccati` / `gain` when `innovCov` is singular
- **Verdict: minor concern.**
- Mathlib's `⁻¹` returns 0 on singular matrices. In that case `gain = 0` and `riccati P = F P Fᵀ + Q`, which is junk.
- Theorems that allow `R.PosSemidef` (`riccati_posSemidef`, `covSeq_posSemidef`) cover this junk region. They remain true, but they speak about a non-textbook map there.
- The substantive theorems (`riccati_mono`, `covSeq_mono_zero`, `riccati_steady_state`) correctly require R ≻ 0.

### C8. `kalman_mse_witness`: the second conjunct is trivial
- **Verdict: minor concern.**
- The setup is non-degenerate and good: a random walk with independent Rademacher noise, P₀ = 0 and x̂₀ = x₀ = 0.
- But its second conjunct (MSE at t = 1 equals 1) is a single trivial value.
- Linking the witness to `riccati_scalar_witness` would actually exercise the steady state: MSE_t → (1+√5)/2.

### C9. `Innovation` definition (YuleWalker.lean): uses E[ε_t x_t] = σ² rather than E[ε_t²] = σ²
- **Verdict: OK.**
- Under `IsAR` plus orthogonality to the past, E[ε_t x_t] = E[ε_t²], so `yule_walker_zero` matches Hamilton (3.4.36) and B&D (8.1.4).
- Note that ε is not required to be white, only orthogonal to past x. That is the correct, weaker Wold-innovation notion.

### C10. `two_step_witness` (TwoStepGMM.lean, dependency, l.260)
- **Verdict: concern.** It is out of the main scope but built upon.
- Ĝ and Ŝ are constant sequences, and √n · (ω/√n) = ω, so every convergence is an identity.
- The `∃ _ : IsProbabilityMeasure P` conjunct duplicates the first conjunct.

---

## 3. Items judged OK

| Item | Verdict | Note / reference |
|---|---|---|
| `sHat`, `sCross`, `sQuad`, `expandS`, `sHat_eq_expandS`, `expandS_zero` | OK | Correct algebraic expansion of the residual-based Ŝ(θ). Hayashi (3.5.10); White (1980). |
| `sampleG`, `sampleZY`, `sampleMoment`, `sampleZY_eq` | OK | S_zx, s_zy, ḡ(θ) = s_zy − S_zx θ. Hayashi §3.4. |
| `firstStep`, `secondWeight`, `twoStep` | OK | θ̃ = θ̂(W₁); Ŵ = Ŝ(θ̃)⁻¹; θ̂(Ŝ⁻¹). Hayashi §3.5 two-step efficient GMM; Hansen (1982). |
| `two_step_feasible`, part 1 (asymptotic normality) and part 2 (efficient variance) | OK | The hypotheses are sufficient and not superfluous: full column rank of G, S ≻ 0, first-step rank, CLT for √n ḡ, LLN for Ŝ-components. First-step consistency is correctly derived from `hg`, not assumed. The limit law (G′S⁻¹G)⁻¹ is correct. Hayashi Prop 3.5; Newey–McFadden Thm 3.4 / §5. |
| `two_step_feasible`, J-statistic definition | OK | J = n ḡ(θ̂)′ Ŝ⁻¹ ḡ(θ̂), using the same Ŝ(θ̃) in the weight and the J statistic. Hayashi (3.6.x). (Limit law: see C1.) |
| `measurable_firstStep`, continuity lemmas | OK | Routine. |
| `riccati`, `riccati_eq` | OK | Predictor-form Riccati P_{t+1\|t} = F(P − P Hᵀ(HPHᵀ+R)⁻¹HP)Fᵀ + Q. Hamilton (13.2.22); Anderson & Moore §3.1. |
| `riccati_posSemidef`, `joseph_posSemidef` | OK | |
| `riccati_mono` | OK | P ⪯ P′ ⇒ Ric(P) ⪯ Ric(P′) with R ≻ 0. Anderson & Moore §4.4. |
| `covSeq`, `covSeq_posSemidef`, `covSeq_mono_zero` | OK | Monotone increasing from P₀ = 0. Anderson & Moore §4.4. |
| `continuousAt_riccati` | OK | Correct invertibility proviso. |
| `riccati_scalar`, `riccati_scalar_witness` | OK | c/(c+1) + 1; the fixed point P² − P − 1 = 0 gives the golden ratio. Checked. |
| `wnV`, `wnW`, `wnX`, `wnY`, `wnXh` | OK | Independent Rademacher noises (even and odd indices), random walk, filter with gains from covSeq at P₀ = 0, consistent with x̂₀ = x₀ = 0. |
| `toeplitz` | OK | Γ_{ij} = γ(i − j), (p+1)×(p+1). B&D (5.1.2), Hamilton (3.4.x). |
| `toeplitz_transpose`, `toeplitz_quadForm` | OK | a′Γa = E[(Σ a_i x_{−i})²]. |
| `yule_walker_unique` | OK | φ = Γ⁻¹γ under σ² > 0. B&D §8.1; Hamilton §3.4. |
| `coin`, `coins`, `rad`, `integral_rad`, `integral_rad_mul`, `memLp_rad` | OK | A fair-coin infinite product, so `rad` is i.i.d. ±1 with E[rad_i rad_j] = δ_ij, i.e. strict white noise. Only second-moment facts are stated (see suggestions). |

---

## 4. Missing canonical results that would be cheap to add

1. **χ²(l − k) limit of J** (Hansen 1982 Lemma 4.2; Hayashi Prop 3.6). This upgrades C1. The idempotency and trace lemmas already exist.
2. **Consistency of the Avar estimator** (Ĝ′Ŝ(θ̃)⁻¹Ĝ)⁻¹ → (G′S⁻¹G)⁻¹. This is one continuous-mapping step from `sHat_consistent`, `tendstoInMeasure_invFn` and `hGhat`. Hayashi Prop 3.5(b).
3. **White (1980) HC0 sandwich consistency for OLS.** Specialise z = x and W = (X′X)⁻¹: (S_xx)⁻¹ Ŝ (S_xx)⁻¹ → Avar(b). All ingredients are present.
4. **Wald / t statistic** with the feasible Avar, ⇒ χ²(r) / N(0,1). Hayashi Prop 3.3.
5. **C (difference-in-Sargan) statistic** (Hayashi Prop 3.7). This is moderate effort.
6. **Kalman optimality over all gain sequences:** for any (K_t), MSE_t ⪰ covSeq t. By induction from `joseph_sub_gain` and `riccati_mono` (Kalman 1960).
7. **Stability bound:** if F is Schur-stable, then covSeq from 0 is bounded by Σ F^j Q F′^j, which discharges `hM` (Hamilton Prop 13.1). Also: **uniqueness of the PSD ARE solution** and convergence from arbitrary P₀ (Anderson & Moore §4.4), which is moderate effort.
8. **Innovations covariance:** E[(y_t − H x̂_t)(y_t − H x̂_t)′] = H P_t H′ + R, and innovations are serially uncorrelated (Hamilton §13.2; Anderson & Moore §5.3). Cheap given `kalman_filter_mse`.
9. **B&D Prop 5.1.1:** γ(0) > 0 ∧ γ(h) → 0 ⇒ Γ_n ≻ 0 for all n.
10. **Independence of `rad`** (`iIndepFun`, i.e. i.i.d. white noise) and E[rad_i⁴] = 1. Both are one-liners from `infinitePi`, and both are useful for building non-degenerate witnesses (D1, C5).
11. **Non-degenerate GMM witness** (l = 2, k = 1) and **MA(1) Toeplitz witness**, as described in D1 and C5.
