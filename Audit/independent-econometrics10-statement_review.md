# Statement review: FeasibleJWitness.lean and `two_step_wald_rect_witness`

Both files elaborate cleanly against the built library with `lake env lean` (Lean 4.36.0).
The only warnings are `declaration uses sorry`.

No statement is false. I found no defects. All issues are caveats or nits.

## Verdicts

### FeasibleJWitness.lean

| Declaration | Verdict | Notes |
|---|---|---|
| `spike`, `zJ`, `wJ`, `uJ` (defs) | OK (caveat, see I3, I4) | |
| `sum_spike_mul` | OK | True for n ≥ 4. For n < 4 it is false (the sum is truncated), so `hn` is required and correct. |
| `sum_spike_sq_mul` | OK | (√n/2)² = n/4 on i < 4. Needs n ≥ 4, which `hn` gives. |
| `sum_range_neg_one_pow` | OK | |
| `abs_sum_neg_one_pow` | OK | |
| `tendsto_avg_neg_one_pow` | OK | |
| `tendsto_scaled_sum` | OK | The bound is \|c n · Σ f\| ≤ \|c n\|·n·K → 0. If K < 0, `hf` is false and the lemma holds vacuously, which is harmless. |
| `sum_spike_mul_eq_zero` | OK | |
| `zJ_zero_two`, `zJ_one_three`, `wJ_zero_two`, `wJ_one_three` | OK | Parity: (−1)^0 = (−1)^2 and (−1)^1 = (−1)^3. |
| `abs_zJ_le`, `abs_wJ_le`, `abs_wJ_sq_zz_le`, `abs_wJ_zz_le` | OK | |
| `sqrt_inv_sq` | OK | It also holds at n = 0 (0 = 0). |
| `sHat_eq` | OK | Checked by hand. The spike² term gives (1/n)(n/4)Σ_{i<4} z_ia z_ib = I, because z_0..z_3 = (1,1),(1,−1),(1,1),(1,−1). The cross term vanishes because w·zz has period 2. The remaining term is n⁻² Σ w² zz. |
| `sCross_eq` | OK | The spike term vanishes. The remainder is (n√n)⁻¹ Σ w zz. |
| `sqrt_sampleMoment_eq` | OK | Σ z·spike = 0, and √n·n⁻¹·n^{-1/2} = n⁻¹ needs n ≥ 1, which n ≥ 4 covers. |
| `sum_zJ_zero`, `sum_zJ_one`, `zJ_one_sq` | OK | |
| `tendsto_avg_const`, `tendsto_avg_zJ`, `tendsto_avg_zJ_mul`, `tendsto_avg_zJ_wJ` | OK | Limits: 1; (1, 0); I₂; (ω0, ω1). All correct. |
| `tendsto_sq_inv_mul`, `tendsto_sqrt_inv_mul` | OK | |
| `measurable_uJ` | OK | |
| `feasible_jtest_witness` | OK with caveats (I1, I3, I4, I5) | |

### GMMWald.lean

| Declaration | Verdict | Notes |
|---|---|---|
| `two_step_wald_rect_witness` | OK with caveats (I2, I6) | |

## Checking the design of `feasible_jtest_witness`

- **Dimensions and data.** l = 2, k = 1, θ₀ = 0, x_i = 1, z_i = (1, (−1)^i), and y_i = u_i = spike_i + n^{-1/2}(ω0 + (−1)^i ω1) with ω ~ N(0, I₂). The model is linear and the y, x, z objects are the ones the theorem consumes, so it is a legitimate linear GMM model. It is overidentified, since `card k = 1 < 2 = card l`.
- **First step.** W₁ = I₂. Ĝ = (1, n⁻¹Σ(−1)^i)ᵀ is not constant in n. sampleZY depends on ω, so θ̃ is a non-constant random variable. Ŝ(θ̃) is an estimated matrix that depends on ω, both through θ̃ and through the n⁻² Σ w² term.
- **J statistic.** √n ĝ(0) = n⁻¹ Σ z_i w_i → ω exactly for every ω, so L = id and S = I. The J form is Q = I − e₁e₁ᵀ, so J_n → ω1² ~ χ²(1). The statistic is not trivial.
- **Conclusion.** The limit `chiSq (card l − card k) = chiSq 1` matches. `secondWeight I2` matches `W1 n ω = I2`, and θ₀ = 0 is used consistently in `hg`, `h0` and `h1`.

## Comparing hypotheses with `two_step_feasible_jtest_chiSq`

The instantiation is: P' = P, L = id, S = 1, W1 n ω = W₁ = I2, A1 = 0, and A2 = fun a b _ _ => I2 a b.

| Hypothesis | Stated in the witness? |
|---|---|
| `IsProbabilityMeasure P` / `P'` | yes |
| `hS : S.PosDef` | **no** |
| `hG`, `hrank1` | yes |
| `hGhat`, `hg`, `h0`, `h1`, `h2` | yes |
| `hW1` (constant sequence) | **no** |
| `hz`, `hx`, `hW1m` | **no** (all constant in ω) |
| `hy` | yes, in the stronger form `Measurable` |
| `hL : Measurable id` | **no** |
| `hlaw` | yes |
| `hkl : 1 < 2` | **no** |

Every omitted hypothesis holds trivially in this instance. Even so, the witness does not literally list every hypothesis of the target theorem (I1).

## Comparing hypotheses with `two_step_wald`

The instantiation is: Ghat = const G, P' = P, L = id, θ₀ = 0, c = 0, q = Fin 1.

| Hypothesis | Stated in the witness? |
|---|---|
| `hS`, `hG`, `hGhat`, `hShat`, `hg`, `hL`, `hlaw`, `hnull`, `hR` | yes |
| `hGm`, `hSm`, `hgm` | **no** |
| `0 < card q` (premise of the third conjunct) | **no** |

The conclusion matches the third conjunct of `two_step_wald`, with `Ghat n ω = G`. The first two conjuncts (convergence in distribution, and the law being χ²(q)) are not restated.

**Is the restriction nontrivial?** Yes.
- R = (1, −1) has rank 1 with q = 1 < k = 2, so R is genuinely rectangular.
- R V Rᵀ = 2 with V = (GᵀG)⁻¹ = (1/3)[[2, −1], [−1, 2]], which is not diagonal.
- l = 3 > k = 2, so the model is overidentified.
- G = [[1, 0], [0, 1], [1, 1]] is injective.
- The null R·0 = 0 holds.

## Issues

**I1 (nit/caveat). `feasible_jtest_witness` omits trivially true hypotheses.** The omitted ones are `hS` (`(1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef`), `hW1` (constant), `hz`, `hx`, `hW1m`, `hL` (`Measurable id`) and `hkl`. Of these, `hS` is the one with mathematical content, and the sibling `two_step_wald_rect_witness` does list `S.PosDef`, so the two witnesses are inconsistent.
- *Fix:* add the conjuncts `(1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧ Measurable (id : (Fin 2 → ℝ) → _) ∧ Fintype.card (Fin 1) < Fintype.card (Fin 2)`.
- Optionally also add `(∀ n, AEMeasurable (z n) P) ∧ (∀ n, AEMeasurable (x n) P)`.
- Alternatively, add a docstring saying that constant or measurability hypotheses are discharged in the proof.

**I2 (nit). `two_step_wald_rect_witness` omits `hGm`, `hSm`, `hgm` and `0 < Fintype.card (Fin 1)`.** It does list `Measurable id` and the constant `TendstoInMeasure`, so its choice of what to list is inconsistent.
- *Fix:* add `(∀ n, AEMeasurable (Shat n) P) ∧ (∀ n, AEMeasurable (g n) P)`, or drop the trivial conjuncts consistently.

**I3 (caveat). The deterministic spike is a device, not a standard DGP.** The spike adds ±√n/2 to four observations (i = 0, 1, 2, 3).
- *Consequence 1: per-observation moments are not zero.* E_ω[z_i u_i] = z_i·spike_i ≠ 0 for i < 4. For example, at i = 0 it equals (√n/2, √n/2). Observation-wise moment validity fails, and the summands are not uniformly asymptotically negligible: four observations each carry O(√n), so a Lindeberg-type condition fails. Their contributions cancel exactly in Σ z_i u_i, because z has period 2 and the spike pattern is (+, +, −, −).
- *Consequence 2: Ŝ and the moment variance are matched by tuning, not by mechanism.* The limit of Ŝ (I₂) comes entirely from the spike, while the Gaussian moment limit comes entirely from ω, whose contribution to Ŝ is O(1/n). The two agree (S = I) only because Cov(ω) = I was chosen to match the spike's Ŝ-limit. If Cov(ω) were changed to Σ ≠ I, Ŝ would still converge to I and `hlaw` would fail. In a genuine DGP, Ŝ estimates the variance of the √n-moment.
- *Does it matter?* Not for non-vacuity. The theorem's hypotheses are high level (`h0` and `hlaw` share S), and the witness meets them honestly: S really is the law of L, and Ŝ really converges to S.
- *Precedent.* The existing `two_step_feasible_witness` in FirstStepGMM.lean uses the same device (`wEps`), so this witness follows established project style.
- *Fix (documentation):* add a docstring stating that this is a deterministic-design triangular array whose spike reproduces the HC variance, and that it is not an i.i.d. DGP. If a multivariate CLT on ℝ^ℕ with a product measure becomes available, an i.i.d. witness would be more representative.

**I4 (caveat). Triangular-array, deterministic-design, single-Gaussian Ω.** The probability space is just ℝ², and every statistic converges for every ω (pointwise in ω, which is stronger than in probability). This is acceptable as a non-vacuity witness: it shows the hypotheses are jointly satisfiable in a non-degenerate overidentified model and that the conclusion is non-trivial (a χ²(1) limit, not degenerate). It is not evidence that the hypotheses hold for i.i.d. sampling. The docstring should say so.

**I5 (nit). Minimal overidentification.**
- G = (1, 0)ᵀ, so the second instrument (−1)^i has zero asymptotic first-stage strength. It is valid but irrelevant.
- x_i = 1 is an exogenous intercept, not an endogenous regressor.
- S = W₁ = I, so the efficient weight equals the first-step weight. The second step has no asymptotic effect on θ̂; it matters only through Ŝ in J.
- This is legitimate (rank condition holds and l > k), but the example does not exercise G with a nonzero second row, or S ≠ W₁.
- *Optional strengthening:* use z_i = (1, 1 + (−1)^i) so that G = (1, 1)ᵀ. Using a spike of unequal magnitudes would make S ≠ I.

**I6 (nit). In `two_step_wald_rect_witness`, Ŝ and Ĝ are not random, and Ŝ affects the statistic only through a scalar.**
- Ghat is the constant G.
- Shat_n = (1 + 1/(n+1))·I is deterministic. As a scalar multiple of I, it cancels in θ̂ and enters avarHat only as the factor c_n, so W_n = (Rθ̂√n)²/(2c_n).
- Shat_n ≠ S at every n, so the consistency hypothesis is used, but the witness does not exercise a random or non-scalar Ŝ.
- This is acceptable for non-vacuity.
- *Optional fix:* use `Shat n ω = S + (√n)⁻¹ • diagonal (ω²)` or similar, and/or a non-identity S such as `diagonal ![1, 2, 3]` so that S ≠ c·I.

## Missing results (optional)

- `feasible_jtest_witness` does not restate the intermediate conclusion of `two_step_feasible`, the convergence in distribution J_n →d ω1². That is the content, and it would make the χ²(1) limit concrete (Q = I − e₁e₁ᵀ). This is optional.
- For the Wald witness, the first two conjuncts of `two_step_wald` (the distributional limit and its law) are not stated. This is optional, since the rejection-probability conjunct implies the test is non-degenerate.
