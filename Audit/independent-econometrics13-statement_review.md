# Independent statement review: `Econometrics/Asymptotics/LocalPower.lean`

Reviewer: context-isolated adversarial statement reviewer (round 13). Scope: theorem statements only,
not proofs. References: Hayashi (2000) §2.4; Newey–McFadden (1994) §9; van der Vaart (1998) ch. 14–15;
Davidson–MacKinnon (2004) §4.8.

Definitions checked: `tStat n r c θ V = √n (rᵀθ − c) / √(rᵀVr)`, `seInv`, `waldStat n R c θ V =
n (Rθ − c)ᵀ (R V Rᵀ)⁻¹ (Rθ − c)`, `waldWeight`, `rowMat r` (1×k row), `inv_fin_one_const`,
`chiSq r` (law of a sum of r squared iid N(0,1)), `t_normal`, `test_power_witness`.

## Per-declaration verdicts

### `tendstoInMeasure_of_tendsto_const`: OK (minor naming point)
A deterministic sequence `d n → h` converges in probability to the constant `h`. This is correct. The
name says "const", but `d` is a deterministic sequence that need not be constant. The name is a little
misleading, but the statement is right.

### `t_local_tendsto`: OK
The algebra is `tₙ = [rᵀ√n(θ̂ₙ − θₙ) + √n(rᵀθₙ − c)] · seInv(V̂ₙ)`. With the hypotheses
`√n(θ̂ₙ − θₙ) →d L`, the deterministic drift `√n(rᵀθₙ − c) → h`, `V̂ₙ →p V` and `rᵀVr > 0`, the limit
`(rᵀL + h)/√(rᵀVr)` is the standard Pitman-drift result (Slutsky plus the CMT). `hpos` is needed for
continuity of `seInv` at `V`, so it is not superfluous. The `√·` and `x⁻¹` conventions only matter
where `rᵀV̂r ≤ 0`, which has vanishing probability, so they cannot make the statement trivially true.
Note that `hT` is centred at the drifting `θₙ`, not at `θ₀`. This is the right hypothesis, and in
applications it has to be checked under the drifting DGP (Le Cam's third lemma or a direct argument).
The theorem assumes it and does not derive it.

### `t_local_normal`: OK
The limit law is `N(h/σ, 1)` with `σ = √(rᵀVr)`. Given `L ∼ N(0, V)`, `rᵀL/σ ∼ N(0, 1)` and the shift is
`h/σ`, so this is correct. The one-sided rejection event `{a < tₙ}` and the two-sided event
`{a < |tₙ|}` converge to `P(N(h/σ,1) > a)` and `P(|N(h/σ,1)| > a)`, which matches Davidson–MacKinnon
§4.8 and van der Vaart §14.1. The statement holds for every real `a`, which is valid because the
normal law has no atoms. The quantifiers are correct. `hVpsd` is needed for `multivariateGaussian 0 V`
to have its intended meaning.

### `gaussianReal_Ioi_mono`: OK
`P(N(μ,1) > a)` is nondecreasing in `μ`. This is correct. The true property is strict monotonicity
(listed under missing results).

### `t_local_power_mono`: OK (docstring nuance)
The statement is general monotonicity in `h` for any `σ > 0`. "Power ≥ size for h ≥ 0" is the special
case `h = 0 ≤ h'`, and the witness uses it that way. `σ` is a free positive parameter and is not tied to
`rᵀVr`. That is harmless because the statement only gets more general. The docstring says "for a
nonnegative drift h ≥ 0", but the theorem is stated with `h ≤ h'`. The two are consistent but phrased
differently.

### `wald_local_tendsto`: OK
`Wₙ = [R√n(θ̂ₙ − θₙ) + √n(Rθₙ − c)]ᵀ (R V̂ₙ Rᵀ)⁻¹ [·]`, and the limit is
`(RL + h)ᵀ (RVRᵀ)⁻¹ (RL + h)`. This is correct. `hR : IsUnit det(RVRᵀ)` makes the limit use the true
inverse, so the convention `M⁻¹ = 0` for singular `M` never applies at the limit. `hR` is also needed
for continuity of the inverse at `V`. No PSD or PD condition is needed at this stage, so leaving it out
is correct.

### `ncChiSq`: OK
`ncChiSq μ` is the law of `∑ᵢ (Zᵢ + μᵢ)²` with `Zᵢ` iid `N(0,1)`. This is the standard noncentral
χ²(|ι|, λ = ‖μ‖²) (Davidson–MacKinnon §4.8, which uses λ = ‖μ‖² and not λ/2). The family is
parameterized by the mean vector, not by (q, λ). The docstring says the law depends only on ‖μ‖²
("which we do not need") but never proves it. So `ncChiSq μ` is not formally identified with the scalar
family χ²_q(λ). For q = 1 that question does not arise. The `IsProbabilityMeasure` instance is correct.

### `ncChiSq_zero`: OK
At μ = 0 the law is `chiSq (card ι)`, which is correct.

### `ncChiSq_reindex` / `ncChiSq_fin_singleton`: OK
These are auxiliary lemmas. The statements are correct: the law is invariant under reindexing, and
with at least one coordinate there are no atoms.

### `ncChiSq_singleton`: OK
The law has no atoms when `[Nonempty ι]`. The hypothesis is necessary: for empty ι the law is the
point mass at 0. The module header says "has no atoms" without mentioning this hypothesis. The
docstring states it correctly.

### `noncentrality_eq`: OK
`‖M^{-1/2} h‖² = hᵀ M⁻¹ h` for positive definite `M`, with `CFC.sqrt` the PSD square root, which is
symmetric and invertible when M ≻ 0. This is correct, and since `hM` holds, neither the
`CFC.sqrt`-of-non-PSD convention nor the `⁻¹ = 0` convention applies.

### `map_wald_local_limit`: OK
If L ∼ N(0,V) and M = RVRᵀ ≻ 0, then RL + h ∼ N(h, M) and the quadratic form is χ²_q(hᵀM⁻¹h). The
statement writes this as `ncChiSq (M^{-1/2} h)`, which is correct. Any square root S with SSᵀ = M gives
the same law, so the choice of the PSD root does not matter.

### `wald_local_power`: OK
The rejection probability of `{Wₙ > a}` tends to `ncChiSq(M^{-1/2}h)(a, ∞)` for every a.
`[Nonempty q]` is needed so the limit has no atom at a (the boundary condition). Together with
`noncentrality_eq`, this is the textbook result: local power is `P(χ²_q(λ) > a)` with
`λ = hᵀ(RVRᵀ)⁻¹h` (Newey–McFadden §9.2, Davidson–MacKinnon §4.8). The hypotheses are consistent and
none is vacuous. Positive definiteness of M requires R to have full row rank and V to be positive
definite on the range of Rᵀ, which are the standard conditions.

### `local_power_witness`: OK (genuine, nontrivial drift)
The witness uses r = (1, −1), R = rowMat r, V = I₂, P = N(0, I₂) on ℝ², and
V̂ₙ = (1 + 1/(n+1)) I₂, which is not constant but converges to I₂. It also sets θₙ = δ/√n with
δ = (1, 0), and T̂ₙ = θₙ + ω/√n.
- Under the null c = 0, rᵀθₙ = 1/√n ≠ 0 for every n ≥ 1. So every θₙ is a genuine alternative, and the
  sequence converges to the null value. The drift is h = rᵀδ = 1 ≠ 0.
- At n = 0, √0⁻¹ = 0 (Lean convention), so θ₀ = 0 and T̂₀ = 0. A single index does not affect any limit.
- √n(T̂ₙ − θₙ) = ω for n ≥ 1, so L = id ∼ N(0, I₂), and the `hlaw` hypothesis holds.
- The witness gives σ² = 2, the t limit N(1/√2, 1), power ≥ size, the two-sided limit
  P(|N(1/√2,1)| > a), the Wald limit P(ncChiSq(μ) > a), and λ = ‖μ‖² = 1/2 = h²/σ². This is
  consistent with t² = W for a single restriction.
- All hypotheses of `t_local_normal` and `wald_local_power` are stated in the witness, and the
  conclusions are the instantiated main-theorem conclusions. The noncentrality is nonzero, so the
  witness does not reduce to the size result.
- Limitations: q = 1, so the vector parameterization of `ncChiSq` is not exercised with q ≥ 2. Also,
  √n(T̂ₙ − θₙ) is exactly N(0, I) for each n and not merely asymptotically. Neither is a defect.

## Defects

No defects found. Every statement matches the canonical results, the hypotheses are satisfiable and
not superfluous, the limits and noncentrality parameters are correct, and the conventions are not used
in a way that makes any claim trivial.

## Caveats (non-blocking)

1. **Common probability space.** The data live on a fixed `(Ω, P)` for all n (`fun _ => P`), and the
   drift enters through `T n` and `θ n`. Under Pitman alternatives the DGP changes with n. This is fine
   because the statements only involve laws and convergence in probability to constants, and any
   triangular array can be realized on a product space. Still, it is a modeling choice and not the
   P_{θₙ}^n formulation of van der Vaart ch. 14.
2. **`hT` under drifting parameters is assumed, not derived.** It has to be verified for each estimator
   under the local DGP, usually through contiguity and Le Cam's third lemma (van der Vaart §6.7, §7).
   The file does not provide this link.
3. **`ncChiSq` is parameterized by the vector μ.** The claim that the law depends on μ only through
   ‖μ‖² is in a docstring but not proved. Results are stated as `ncChiSq (M^{-1/2} h)` and not as
   χ²_q(λ) with λ = hᵀM⁻¹h.
4. **Minor wording.** The helper is named `tendstoInMeasure_of_tendsto_const` but takes a deterministic
   non-constant sequence. The module header's "has no atoms" leaves out the `Nonempty ι` hypothesis.
   The `t_local_power_mono` docstring talks about h ≥ 0 while the statement uses h ≤ h'.
5. **The critical value `a` is free.** Nothing ties `a` to a χ² or normal quantile. This is general and
   correct, but the "power at nominal level α" reading needs a separate instantiation.

## Missing results (would strengthen coverage)

- Strict monotonicity of one-sided local power in h (and in μ), and power tending to 1 as h → ∞.
- Monotonicity of two-sided t-test power in |h| (symmetry and unimodality of the normal).
- Wald local power ≥ size, monotone in λ (Anderson's lemma or the stochastic ordering of noncentral
  χ² in λ). There is currently no power-vs-size comparison for the Wald test.
- `ncChiSq` depends only on (q, ‖μ‖²): invariance under orthogonal transformations of μ.
- Mean of the noncentral χ²: E = q + λ.
- A derivation of `hT` under θₙ = θ₀ + δ/√n for a concrete estimator (for example OLS), or via
  contiguity, so that the drift hypothesis follows from primitive conditions.
- Explicit t² = W consistency at the level of local limits (q = 1): ncChiSq(μ) = law of N(μ,1)².
