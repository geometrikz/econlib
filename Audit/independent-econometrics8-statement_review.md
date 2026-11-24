# Statement review: ChiSquared.lean, ChiSquaredTests.lean

Scope: statements only (proofs are `sorry`). Upstream defs checked: `jForm`, `jStat`, `invFn`,
`GMM.estimator`, `sHat`/`sCross`/`sQuad`/`sampleG`/`sampleZY`/`sampleMoment`/`secondWeight`,
`gram`, `two_step_jtest`, `two_step_feasible`, `two_step_witness`, `two_step_feasible_witness`,
Mathlib `multivariateGaussian` (= `dirac μ` when `S` is not PSD, because `CFC.sqrt S = 0`) and
`TendstoInDistribution` (bundles a.e.-measurability of every `X n` and of the limit).

No outright false or vacuous main statement was found. There are no defects of the
"the theorem says something different from the textbook result" kind. The issues are about
witnesses that do not exercise much, a missing overidentified witness for the feasible J test,
a few wording and attribution overclaims, and missing canonical companion results.

## Verdict per declaration

### ChiSquared.lean
| Declaration | Verdict |
|---|---|
| `chiSq` | OK. This is the textbook definition: the law of the sum of `r` iid squared N(0,1). `chiSq 0 = dirac 0`, the usual degenerate convention, which gives the right answer for J in the just-identified case. Not linked to the Gamma(r/2, 1/2) law or to a density (see Missing). |
| `IsProbabilityMeasure (chiSq r)` | OK |
| `map_sum_sq_eq_chiSq` | OK |
| `map_sum_sq_finset_eq_chiSq` | OK |
| `integral_chiSq` | OK. The mean is r. The variance 2r is missing. |
| `chiSq_singleton` | OK. No atoms for r ≥ 1. `hr` is necessary, since `chiSq 0 = dirac 0`. |
| `eigenvalues_idempotent` | OK |
| `quadForm_eigenbasis` | OK |
| `map_quadForm_idempotent` | OK. With M symmetric idempotent of trace r, z'Mz ~ χ²(r). For an idempotent matrix the trace equals the rank, so this is the standard result. |
| `map_multivariateGaussian_eq` | OK. It needs no PSD hypothesis: when S is not PSD, both sides are `dirac 0`. |
| `map_quadForm_gaussian` | ISSUE, nit (#6). The statement is correct, but `ASA = A` is only sufficient. The canonical necessary and sufficient condition (Rao 3b.4; Ogasawara–Takahashi) is `SASAS = SAS`, with df = tr(AS). The original docstring calls it "Cochran", but this is not Cochran's theorem. |

### ChiSquaredTests.lean
| Declaration | Verdict |
|---|---|
| `tendsto_prob_gt_of_chiSq` | OK, with a caveat (#4). Portmanteau at a continuity point; `hr` is needed. The conclusion is the pointwise null rejection probability, not an econometric "size", and no critical value is defined (#5). |
| `card_le_of_injective` | OK |
| `jLimit_chiSq` | OK. With S ≻ 0 and G of full column rank, L'QL ~ χ²(l−k) (Hayashi Prop. 3.6). Truncated ℕ subtraction is harmless because l ≥ k follows from `hG`. For l = k the limit is χ²(0) = δ₀, which is correct. |
| `map_jLimit_chiSq` | OK |
| `two_step_jtest_chiSq` | OK, with a nit (#7). The null E g(θ₀) = 0 is encoded by `s = Ĝθ₀ + g`, `√n g →d L ~ N(0,S)` and `Ŝ →p S`, which is correct. The same `Ŝ` is used in the weight and in the estimator, as Hansen and Hayashi require. Conjunct 1 just restates `two_step_jtest`. The `k < l` guard on conjunct 3 is stronger than needed. |
| `two_step_feasible_jtest_chiSq` | ISSUE, caveat (#2). The statement is fine and the hypotheses match `two_step_feasible`, but no overidentified witness exists anywhere. `two_step_feasible_witness` is just-identified (`Fin 1`, `Fin 1`), so `hkl : 1 < 1` fails there and this theorem has never been shown non-vacuous. |
| `two_step_jtest_chiSq_witness` | ISSUE, caveat (#1). It is degenerate: Ĝ and Ŝ are constant and equal to the truth, and √n ĝ = ω ~ N(0,S) exactly. So Jₙ ~ χ²(1) exactly for every n ≥ 1 and the limit is a constant sequence. The statement exposes only the conclusion, not that the hypotheses hold. The upstream proof does go through `two_step_jtest_chiSq` via `two_step_witness`, which mitigates this. |
| `waldStat` | OK, with a caveat (#3). It is the standard Hayashi (2.6.4)-style Wald statistic, with V the Avar of √n(θ̂−θ₀). If R V̂ R' is singular, Mathlib's `⁻¹ = 0` makes Wₙ = 0 (the test never rejects). |
| `waldWeight`, `of_waldWeight`, `continuous_waldArg`, `continuousAt_waldWeight`, `measurable_waldWeight` | OK. These are helper lemmas. |
| `wald_tendsto` | OK. `hR` (R V R' invertible) implies that R has full row rank q, so the "full row rank" assumption is implied, not missing. No PSD or Gaussian assumption is needed for this generic limit. The null `hnull` is present. |
| `wald_chiSq` | OK. `hVpsd` is genuinely needed: without it, `multivariateGaussian 0 V = dirac 0`, the limit is δ₀, and the χ²(q) claim would be false for q > 0. Since `card q = 0` gives W ≡ 0 and χ²(0) = δ₀, the guard `0 < card q` on the tail conjunct is the right one. |
| `wald_witness` | ISSUE, caveat (#1). Same degeneracy: V̂ = V = I is constant, √n θ̂ₙ = ω exactly, and Wₙ = (ω₁−ω₂)²/2 ~ χ²(1) exactly for n ≥ 1. The statement exposes only `hR` and the conclusion. On the positive side, q = 1 < k = 2, so R is not square and the reduction is non-trivial. |

## Issues and suggested fixes

1. **Witnesses are statistically degenerate and state conclusions only** (caveat).
   `two_step_jtest_chiSq_witness` and `wald_witness` both have an exact finite-n χ² law and no
   estimation error in Ŝ, Ĝ or V̂. Their statements could be proved by direct computation
   without the main theorem, so the statement alone does not certify that the hypotheses are
   jointly satisfiable. (The proofs do route through the theorems, but proofs are not the
   statement.)
   *Fix:* restate each witness, like `two_step_witness`, as a conjunction of every hypothesis
   of the target theorem plus the conclusion. Also use a non-trivial sequence that only
   converges, for example `V̂ₙ ω = (1 + ‖ω‖²/n) • I` or `Ŝₙ ω = S + n^{-1/2}·diag(ω₁², 0)`, and
   `θ̂ₙ` with a vanishing bias term such as `θ̂ₙ = n^{-1/2} ω + n^{-1} v`. The aim is that
   convergence in distribution, not an exact equality in law, carries the result.

2. **No non-vacuity witness for `two_step_feasible_jtest_chiSq` in the overidentified case** (caveat, the most important gap).
   The only feasible witness, `two_step_feasible_witness`, has l = k = 1. That contradicts
   `hkl`, so `two_step_feasible_jtest_chiSq` has no witness at all.
   *Fix:* add `two_step_feasible_jtest_chiSq_witness` with l = 2, k = 1. For example
   `zᵢ = (1, wᵢ)` with a deterministic design such as `wᵢ = ±1` alternating, `xᵢ = 1`, θ₀ = 0,
   and `yᵢ = n^{-1/2}·(ω-term) + εᵢ`, using the `wEps` trick. Exhibit `h0`, `h1`, `h2`, `hW1`
   and `hrank1` explicitly, with S ≠ I if possible, so that the second step actually reweights.

3. **Singular-matrix convention in `waldStat` (and in `jStat` through `invFn`)** (caveat).
   With `Matrix.inv` of a singular matrix equal to 0, a singular R V̂ₙ R' gives Wₙ = 0, so the
   test does not reject. This does not affect the asymptotic statements, because invertibility
   holds w.p.→1 under `hR` and `hV`. It is a hidden finite-sample convention, though, and the
   definition carries no comment about it.
   *Fix:* document it. Optionally add the lemma
   `P(IsUnit (R V̂ₙ Rᵀ).det) → 1` (and its J analogue), so that users can see the convention is
   asymptotically irrelevant.

4. **"Asymptotic size" wording** (caveat or nit; this concerns docstrings and naming).
   The theorems give the pointwise limit of the null rejection probability for one fixed
   null DGP. In modern econometrics (Andrews–Cheng–Guggenberger), "asymptotic size" means
   `limsup_n sup_{P ∈ H₀} P(reject)`. The theorems also fix one probability space `P` for all
   n, so drifting or local DGPs cannot be expressed.
   *Fix:* call it "asymptotic null rejection probability". Optionally generalise the measures
   to `μ : ℕ → Measure Ω` (`TendstoInDistribution` already allows this) so that local
   alternatives can be stated later.

5. **No critical value or quantile** (nit). "Test of asymptotic level α" is implied but never
   stated.
   *Fix:* define `chiSqQuantile r α` (for example via `sInf {c | chiSq r (Ioi c) ≤ α}`) and
   prove `chiSq r (Ioi (chiSqQuantile r α)) = α` for r ≥ 1 and α ∈ (0,1). This needs
   continuity of the CDF (from `chiSq_singleton`) and strict monotonicity on [0,∞). Then
   corollaries such as `P(Jₙ > χ²_{1−α}(l−k)) → α`.

6. **`map_quadForm_gaussian` hypotheses stronger than canonical, and the docstring misattributes the result** (nit).
   `A S A = A` is sufficient but not necessary. The canonical iff is `S A S A S = S A S`
   (with `tr(AS) = r`). Calling this "Cochran" is a misattribution: Cochran's theorem is the
   decomposition `Σ zᵢ² = Σ z'A_j z` into independent χ² pieces iff Σ rank A_j = n.
   *Fix:* either weaken to `S*A*S*A*S = S*A*S`, or rename and re-attribute the result
   (Rao 3b.4, "quadratic forms in normal vectors").

7. **`two_step_jtest_chiSq` conjunct 3 guarded by `k < l` unnecessarily** (nit).
   For l = k, Ĝ is square and invertible w.p.→1, so Jₙ = 0 w.p.→1, and
   `P(Jₙ > c) → δ₀(Ioi c)` holds for every c, including c = 0. The guard is harmless but loses
   the just-identified case.
   *Fix:* drop it and handle l = k separately, or keep it and note why. Also, conjunct 1
   duplicates `two_step_jtest.1` and could be dropped.

8. **Minor:** in `tendsto_prob_gt_of_chiSq` and all tail conjuncts, `{ω | c < T n ω}` is only
   null-measurable, because `T n` is only AE-measurable, so `P` here is an outer measure. This
   is acceptable, but a version for `P {ω | c ≤ T n ω}` (same limit, since there are no atoms)
   would be handy (nit).

## Missing results worth adding

- **χ² identification:** `chiSq r = gammaMeasure (r/2) (1/2)` for r ≥ 1 (Mathlib has
  `gammaMeasure`), plus a density. Also the variance `Var = 2r`, the convolution
  `chiSq a ∗ chiSq b = chiSq (a+b)`, and CDF continuity and strict monotonicity on [0,∞).
- **Cochran's theorem proper** (independence of `z'Az` and `z'Bz` iff `AB = 0`; the
  decomposition theorem), if the Cochran 1934 citation is to be earned.
- **Consistency (power) of the tests:** under a fixed alternative (`Rθ₀ ≠ c`, or for J,
  `E g(θ) ≠ 0` for all θ), `P(Wₙ > c) → 1` and `P(Jₙ > c) → 1` for every c.
- **Local power:** under `θₙ = θ₀ + h/√n`, `Wₙ →d` noncentral χ²(q, λ) with
  `λ = (Rh)'(RVR')⁻¹(Rh)`. This needs a noncentral χ² definition and a triangular-array
  version (see #4).
- **Wald test for the two-step GMM estimator:** an end-to-end corollary combining
  `two_step_feasible` with `wald_chiSq`, using `V̂ = (Ĝ'Ŝ⁻¹Ĝ)⁻¹`. That `V̂ →p (G'S⁻¹G)⁻¹`
  needs to be stated. This is the main canonical application (Hayashi Prop. 3.3 / 3.5) and
  currently exists only implicitly.
- **t-test:** for q = 1, `√n(rθ̂ − c)/√(r V̂ r') →d N(0,1)`, and the two-sided t² equals W.
- **Nonlinear restrictions** `a(θ₀) = 0` via the delta method, with `A(θ) = ∂a/∂θ'` of full
  row rank (Newey–McFadden §9.1; Hayashi Prop. 7.? / 2.3(c)).
- **The trinity and the C statistic:** the GMM distance or LR-type statistic
  `n[J(restricted) − J(unrestricted)] →d χ²(q)` (Newey–West 1987; Hayashi Prop. 3.7), the
  LM/score test, and the asymptotic equivalence of W, LM and DD under H₀. Also the C
  statistic for testing a subset of moment conditions (Hayashi Prop. 3.7).
- **Equivalence of J with the Sargan statistic** under conditional homoskedasticity
  (Hayashi 3.8).
