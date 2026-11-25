# Independent statement review: `EconLean/Econometrics/Asymptotics/OneSidedT.lean`

Reviewer scope: theorem statements only (proofs are machine-checked). I checked them against Hayashi (2000) §2.4,
Davidson–MacKinnon (2004) §4.4–4.5, Wooldridge (2010) §4.2 and Newey–McFadden (1994) §9.
Definitions used: `tStat`, `seInv`, `t_tendsto`, `t_normal`, `test_power_witness`, `tendsto_prob_lt_mul_of_pos`
(TestPower.lean), and `waldStat` (ChiSquaredTests.lean).

Relevant definitions:
- `tStat n r c θ V = √n · (rᵀθ − c) · (√(rᵀ V r))⁻¹`. By Lean's conventions it is 0 when `rᵀVr ≤ 0`, because `Real.sqrt` of a non-positive number is 0 and `0⁻¹ = 0`.
- `waldStat n R c θ V = n · (Rθ − c)ᵀ (R V Rᵀ)⁻¹ (Rθ − c)`. It is 0 when `R V Rᵀ` is singular, because the matrix inverse of a singular matrix is 0.

## Per-declaration verdicts

### `rowMat` — OK
`R = rᵀ` as a `Fin 1 × k` matrix, which is the standard way to write one restriction in Wald form.

### `rowMat_mul_mul_transpose`, `inv_fin_one_const` — OK
These are algebraic helpers. `inv_fin_one_const` is right for every `s`, including `s = 0`, because both sides are then 0 by Lean's conventions.

### `tStat_sq_eq_waldStat` — OK
The statement is `0 ≤ rᵀV̂r → t² = W` with `R = rᵀ` and `c` written as a constant vector.
- **Is the hypothesis necessary?** Yes. If `rᵀV̂r < 0`, then `t = 0` (sqrt convention) but `W = n(rᵀθ − c)² / (rᵀV̂r) ≤ 0`, and the two disagree whenever `rᵀθ ≠ c`. Without the hypothesis the identity is false, so this is the right minimal condition. It is not vacuous, since it holds whenever `V̂` is PSD.
- **Degenerate case.** If `rᵀV̂r = 0`, both sides are 0 by convention. The identity still holds, but it says nothing in that case. The docstring ("whenever `rᵀV̂r ≥ 0`") is accurate, and the module header states the conventions. This matches the textbook fact (Hayashi §2.4; Davidson–MacKinnon §4.5) that for one restriction W = t².

### `tStat_neg` — OK
`t(−r, −c) = −t(r, c)`. Since `(−r)ᵀV(−r) = rᵀVr`, the null `(−r)ᵀθ₀ = −c` is the same as `rᵀθ₀ = c`, and `{a < t(−r,−c)} = {t < −a}`. So the lower-tailed test really is the upper-tailed theorem applied to `(−r, −c)`, as the module doc says. One caveat: the lower-tailed results are not stated explicitly. The reader has to make the substitution themselves.

### `tendsto_prob_lt_mul_of_neg` — OK
If `Xₙ →p x < 0`, `bₙ ≥ 0` and `bₙ → ∞`, then `P(a < bₙXₙ) → 0` for every `a`. This is correct and mirrors the existing `_of_pos` lemma. It needs no measurability assumption: `P` is applied as an outer measure, and an upper bound by measure monotonicity is sound.

### `t_one_sided` — OK
Hypotheses:
- `H₀: rᵀθ₀ = c`;
- `√n(θ̂ₙ − θ₀) →d L` with `Law(L) = N(0, V)`, `V ⪰ 0`;
- `V̂ₙ →p V`, with the same `V` as the asymptotic variance;
- `V̂ₙ` is a.e.-measurable;
- `rᵀVr > 0`.

Conclusion: `P(tₙ > a) → P(N(0,1) > a)` for every real `a`.
- The limit is the correct standard-normal upper tail, and at `a = z_{1−α}` the asymptotic size is α (Hayashi Prop. 2.3 / §2.4; Wooldridge §4.2.3).
- `rᵀVr > 0` is needed. If it equals 0, the statistic is 0 by convention and the limit fails. The PSD assumption only makes `multivariateGaussian 0 V` meaningful. None of the hypotheses contradict each other, and the witness shows they can all hold together.
- `V` appears in both the Gaussian law and the plim of `V̂`, so the variance estimator has to be consistent for the true asymptotic variance. This is the correct requirement; a misspecified `V̂` is excluded.
- The quantifiers are right: the result is pointwise in `a`, and the boundary `{a}` has N(0,1)-measure 0, so no continuity-point restriction is needed.

### `t_scaled_tendstoInMeasure`, `tStat_eq_scaled` — OK
These are helpers. `tStat_eq_scaled` is an unconditional identity. `t_scaled_tendstoInMeasure` is the continuous-mapping step: `(rᵀθ̂ − c)/√(rᵀV̂r) →p (rᵀθ₀ − c)/√(rᵀVr)`, using continuity of `seInv` at `V`, which holds because `rᵀVr > 0`.

### `t_one_sided_consistent` — OK
If `rᵀθ₀ > c`, `θ̂ₙ →p θ₀`, `V̂ₙ →p V` and `rᵀVr > 0`, then `P(tₙ > a) → 1` for every `a`.
- This is the standard consistency of the one-sided test against a fixed alternative (Davidson–MacKinnon §4.5 on test consistency; Hayashi §2.4). It needs only consistency of `θ̂`, not √n-normality, which is a weaker and therefore better assumption.
- `V` here is the plim of `V̂` under the alternative. It does not have to equal the null-variance, and it does not have to be PSD; `rᵀVr > 0` is enough. That is correct, because a probability limit under the alternative is what matters.
- Since this holds for all `a`, it covers every critical value, including `z_{1−α}`.

### `t_one_sided_wrong_side` — OK (minor naming/docstring concern)
If `rᵀθ₀ < c` (with the same assumptions), then `P(tₙ > a) → 0` for every `a`. The mathematics is correct.
- **Concern (wording only):** the module header lists this under "Behaviour under fixed alternatives", and the docstring calls it "an alternative on the wrong side". The witness docstring, however, frames the problem as testing `θ₁ ≤ θ₂` against `θ₁ > θ₂`, i.e. `H₀: rᵀθ ≤ c` vs `H₁: rᵀθ > c`, which is the usual reading of a one-sided test. Under that reading, `rᵀθ₀ < c` lies in the interior of the composite null, not in an alternative. There the result shows that the rejection probability vanishes, which is the "size is attained only at the boundary" half of the composite-null size argument. The statement is right under either reading, but "alternative" only fits the point-null reading (`H₀: rᵀθ = c` vs two-sided alternatives, where this says the upper-tailed test is inconsistent against `rᵀθ₀ < c`). I suggest a docstring note.

### `one_sided_t_witness` — OK (the non-vacuity check holds)
Setup:
- `k = Fin 2`, `r = (1, −1)`, `c = 0`, `V = I₂`;
- `P = N(0, I₂)` on `ℝ²`;
- `θ̂ₙ(ω) = θ₀ + n^{-1/2}ω`;
- `V̂ₙ = (1 + 1/(n+1)) I₂`, which is deterministic and converges to `I₂`.

I checked each hypothesis of each main theorem against the conjuncts and the proof term:
- `t_one_sided` with `θ₀ = 0`:
  - `hnull` holds because `r·0 = 0 = c`.
  - `hpos` holds because `rᵀIr = 2 > 0`.
  - `hVpsd` is given by `PosSemidef.one`.
  - `hT` holds because `√n(n^{-1/2}ω − 0) = ω` for `n ≥ 1` (it is `0` at `n = 0`, which does not affect the limit), so convergence in distribution to `L = id` holds.
  - `hV` and `hVm` hold.
  - `hL = measurable_id`.
  - `hlaw = Measure.map_id`, which is legitimate because `P` is by definition the pushforward of `multivariateGaussian 0 I`.
  - `IsProbabilityMeasure` holds for `P` and for `P' = P`.

  Every hypothesis is instantiated, and the conclusion appears as a conjunct.
- `t_one_sided_consistent` at `θ₁ = (1, 0)`: `c = 0 < r·θ₁ = 1`, and `hT1` is convergence in measure to `θ₁`. Instantiated.
- `t_one_sided_wrong_side` at `θ₂ = (0, 1)`: `r·θ₂ = −1 < 0 = c`, and `hT2` holds. Instantiated.
- `tStat_sq_eq_waldStat`: `rᵀV̂ₙr = 2(1 + 1/(n+1)) ≥ 0` for all `n, ω`, so `hnn` holds. Here the identity is the non-degenerate case (`rᵀV̂r > 0`), not the convention case. Instantiated.

The witness is weak in one respect only (see caveats): `V̂ₙ` is deterministic and `θ̂ₙ` is exactly Gaussian. So the witness does not exercise a random variance estimator or a non-Gaussian finite-sample distribution. That does not make it vacuous, because the hypotheses are genuinely satisfied.

## Defects

None found.

## Concerns (non-blocking)

1. **"Wrong side" framing** (`t_one_sided_wrong_side` and the module header). For the composite null `H₀: rᵀθ ≤ c`, which the witness docstring uses, `rᵀθ₀ < c` is a null point, not an alternative. I recommend rewording to something like "at interior null points (or, under a point null, alternatives on the wrong side)".
2. **Degenerate case of `t² = W`.** When `rᵀV̂r = 0`, the equality is `0 = 0` by convention, not a substantive identity. The module header documents the conventions, so this is acceptable.
3. **Lower-tailed test only implicit.** It is reached through `tStat_neg`; no theorem states it directly.

## Caveats and missing results

- **Pointwise, not uniform, size over the composite null.** Combining `t_one_sided` (boundary) with `t_one_sided_wrong_side` (interior) gives `lim P_θ(tₙ > a) ≤ P(N(0,1) > a)` at each fixed null point θ. It does not give `limsup_n sup_{θ ∈ H₀} P_θ(reject) ≤ α` (uniform asymptotic size). Near-boundary drifting sequences are not covered.
- **No local power.** Under Pitman drifts `rᵀθₙ = c + δ/√n`, the one-sided power is `P(N(δ/√(rᵀVr), 1) > a)` (Davidson–MacKinnon §4.5; Newey–McFadden §9). This is not formalized, and neither is the comparison that the one-sided test has more local power than the two-sided test on the correct side.
- **No random-`V̂` witness**, e.g. a sample-variance-based `V̂ₙ`. The witness uses deterministic `V̂ₙ`.
- **No equivalence result for the one-sided case.** `t² = W` relates the two-sided t-test to the Wald test. The one-sided test has no Wald-type counterpart here, and that is expected: the signed root of W is the t statistic.
- **Critical value not named.** Results are stated for arbitrary `a`. No lemma names `a = z_{1−α}` or gives size = α explicitly. This is a presentational gap only.
