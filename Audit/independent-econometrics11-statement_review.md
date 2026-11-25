# Statement review: TestPower.lean (Wald and t-test consistency, t-statistic, witness)

Reference points: Hayashi (2000) Prop. 2.3 and §2.4 (t_k = √n(b_k − β̄_k)/√Avar̂_kk, W = n(Rb−r)ᵀ(R Avar̂ Rᵀ)⁻¹(Rb−r));
Newey & McFadden (1994) §9; Davidson & MacKinnon (2004) §4.5 (a test is consistent if, for a fixed
critical value, rejection probability → 1 under every fixed alternative).

## Overall verdict

No defects found. All statements are true as written (given the sorry'd proofs). Hypotheses are
satisfiable, none is contradictory, and the conclusions match the textbook notions. The issues
below are caveats and nits, mostly about the witness and missing companion results.

## Verdict per declaration

| Declaration | Verdict |
|---|---|
| `tendsto_prob_lt_mul_of_pos` | OK |
| `waldForm` | OK |
| `waldStat_eq_waldForm` | OK |
| `continuousAt_waldForm` | OK |
| `wald_consistent` | OK (nit 3) |
| `tStat` | OK (caveat 1, documentation only) |
| `seInv` | OK (nit 6) |
| `continuous_quad` | OK |
| `continuousAt_seInv` | OK |
| `measurable_seInv` | OK |
| `t_tendsto` | OK |
| `gaussianReal_frontier_abs` | OK |
| `t_normal` | OK (nit 4) |
| `t_consistent` | OK |
| `test_power_witness` | ISSUE, caveat (issue 2), plus nit 5 |

## Checks per declaration

**`tendsto_prob_lt_mul_of_pos`.** If b_n ≥ 0, b_n → ∞ and X_n →p x > 0, then P(a < b_n X_n) → 1
for every a. This is true: on {|X_n − x| < x/2} we have b_n X_n ≥ b_n x/2 → ∞. It needs no
measurability, because `P` is an outer measure and P(A) ≥ 1 − P(Aᶜ) holds by subadditivity. The
hypothesis `hb0` could be replaced by "eventually ≥ 0", but it is harmless.

**`waldForm` / `waldStat_eq_waldForm`.** Through `of_waldWeight`, `waldForm R c (θ,V)` equals
(Rθ−c)ᵀ(R V Rᵀ)⁻¹(Rθ−c), so W_n = n·waldForm. This is correct, and the identity holds for every n
including n = 0.

**`continuousAt_waldForm`.** It assumes the determinant is a unit, which is the right condition for
continuity of the inverse (`continuousAt_invFn`). OK.

**`wald_consistent`.** The hypotheses are: Rθ₀ ≠ c (fixed alternative), R V Rᵀ positive definite,
θ̂_n →p θ₀ and V̂_n →p V. The conclusion is that P(a < W_n) → 1 for every a, which is exactly
"consistent against fixed alternatives" for any critical value, including the χ²(q) critical value
from `wald_chiSq`. The statement is true: waldForm is continuous at (θ₀,V) and its value there is
(Rθ₀−c)ᵀ(RVRᵀ)⁻¹(Rθ₀−c), which is positive because the inverse of a PD matrix is PD. Apply the
continuous-mapping lemma to the pair, then `tendsto_prob_lt_mul_of_pos` with b_n = n.
- It correctly needs only consistency of θ̂ under the alternative, not √n-normality, which is the
  right (weak) assumption as in D&M §4.5.
- Positive definiteness of RVRᵀ is the canonical assumption (the plim of V̂ is PD under H1). It is
  mildly stronger than needed (see nit 3) but not over-restrictive. V itself is not required to be
  symmetric or PSD, which is fine.
- It is vacuous only when q is empty, where Rθ₀ ≠ c is impossible. That is an acceptable degenerate
  case.
- Mathlib edge cases: a singular R V̂_n Rᵀ makes `⁻¹` return 0 and W_n = 0. This only happens on
  events whose probability → 0, so the conclusion is unaffected.

**`tStat`.** The definition is √n(rᵀθ − c)/√(rᵀ V r) with V the estimated asymptotic variance of
√n θ̂. This equals (rᵀθ̂ − c)/√(rᵀ V̂ r / n) = (rᵀθ̂−c)/SE, the standard t statistic (Hayashi
(2.4.x), with r = e_k giving t_k). `Matrix.of V *ᵥ r` gives (Vr)_i = Σ_j V_ij r_j, so the
denominator is rᵀVr. Junk values:
- If rᵀV̂r ≤ 0, then `Real.sqrt` returns 0, `⁻¹` returns 0 and t = 0, so the test never rejects for
  a ≥ 0.
- If n = 0, then t = 0.

Both are asymptotically irrelevant because `hpos` holds and V̂ →p V. Nothing is wrong here, but the
docstring should record these conventions (caveat 1).

**`seInv`, `continuous_quad`, `continuousAt_seInv`, `measurable_seInv`.** All are true.
`continuousAt_seInv` correctly requires the quadratic form to be strictly positive. Without that,
x ↦ (√x)⁻¹ is discontinuous at 0 (it jumps to the junk value 0).

**`t_tendsto`.** The hypotheses are: H0 rᵀθ₀ = c, rᵀVr > 0, √n(θ̂−θ₀) →d L, V̂ →p V, and V̂_n
AE-measurable. The conclusion is t_n →d rᵀL/√(rᵀVr). This is the right Slutsky/CMT statement, and
it parallels `wald_tendsto`.

Measurability is consistent with the definition. Mathlib's `TendstoInDistribution` requires
`AEMeasurable` of every term and of the limit. For n ≥ 1, AE-measurability of θ̂_n follows from
that of √n(θ̂_n−θ₀). For n = 0, tStat is identically 0. AE-measurability of L comes from `hT`.
`hVm` is genuinely needed, because convergence in measure does not imply measurability.

**`gaussianReal_frontier_abs`.** True for every a:
- If a ≥ 0, the frontier is {−a, a}, a null set. When a = 0 it is {0}.
- If a < 0, the set is ℝ and its frontier is empty.

**`t_normal`.** The extra hypotheses are: V PSD, L measurable, and Law(L) = N(0,V) via
`(multivariateGaussian 0 V).map ofLp` (the same encoding as `wald_chiSq`). The conclusions are:
- (i) the limit rᵀL/√(rᵀVr) has law N(0,1);
- (ii) for every a, P(|t_n| > a) → N(0,1){|x| > a}.

Together these say "asymptotically N(0,1), with two-sided size P(|N(0,1)| > a)", as Hayashi
Prop. 2.3(a) does. For a < 0 both sides equal 1, which is consistent.
- `hVpsd` is not redundant: `multivariateGaussian` is defined for non-PSD S through `CFC.sqrt`
  junk, so the law identification needs it.
- `DecidableEq k` is needed for `multivariateGaussian`. OK.

**`t_consistent`.** The hypotheses are: rᵀθ₀ ≠ c, rᵀVr > 0, θ̂ →p θ₀ and V̂ →p V. The conclusion is
P(|t_n| > a) → 1 for every a. This is true: t_n = √n · g(θ̂_n, V̂_n) where
g → (rᵀθ₀−c)/√(rᵀVr) ≠ 0. It is the correct notion of consistency for the two-sided t-test, and the
assumptions are minimal (no rate is needed).

**`test_power_witness`.** The setup is Ω = ℝ², P = N(0, I₂), r = (1,−1), R = [1 −1], V = I,
V̂_n = (1 + 1/(n+1)) I, θ₁ = (1,0), c = 0.
- The listed facts are true. rᵀVr = 2 > 0. RVRᵀ = [2] is PD. rᵀθ₁ = 1 ≠ 0 and Rθ₁ = 1 ≠ 0. V̂ →p V
  (deterministically). θ₁ + ω/√n →p θ₁.
- Null case (θ₀ = 0, T_n = ω/√n). For n ≥ 1, t_n = rᵀω/√(2(1+1/(n+1))), with rᵀω ∼ N(0,2), so
  t_n ⇒ N(0,1) and the size limit is right. For n = 0, T_0 = 0 (since (√0)⁻¹ = 0) and t = 0, which
  is irrelevant.
- Alternative case: t-test and Wald powers → 1. All conjuncts hold, and both the null and the
  alternative regimes are exercised, so the witness is not vacuous.

## Numbered issues

1. **caveat (docs) — `tStat` / `seInv` junk conventions.** When rᵀV̂r ≤ 0, √· is 0 and ⁻¹ is 0, so
   t = 0. When n = 0, t = 0. Similarly, `waldStat` is 0 when R V̂ Rᵀ is singular. These are harmless
   asymptotically, but the docstrings should say so, together with the convention that V̂ estimates
   Avar(√n θ̂), not Var(θ̂). (If V̂ estimated Var(θ̂), the √n would be wrong.)
   *Fix:* add a docstring such as "`V` is the estimated asymptotic variance of `√n θ̂`; with
   Mathlib's conventions `tStat = 0` when `rᵀVr ≤ 0` or `n = 0`."

2. **caveat — the witness does not list all hypotheses of the theorems it illustrates.**
   - It lists `hpos`, PosDef, the alternatives, the consistency `hV`, and the consistency
     `hT`(alt).
   - It omits the null-case hypotheses of `t_tendsto`/`t_normal`:
     `TendstoInDistribution (√n • (T n − 0)) atTop id P P`, `Measurable L`,
     `P.map L = (multivariateGaussian 0 V).map ofLp` (true by construction with L = id, Ω' = Ω), and
     `V.PosSemidef`. It also omits the measurability facts `hVm`.
   - So the null-case conjunct is only asserted as a conclusion, and it is not shown that
     `t_normal` itself is instantiable. In this example the conclusion follows by an exact
     computation, without the theorem.
   - V̂ is deterministic (it does not depend on ω), so the V̂ →p V hypothesis is exercised only
     trivially.

   *Fix:* add the conjuncts
   `TendstoInDistribution (fun n ω => √n • ((√n)⁻¹ • ω - 0)) atTop id (fun _ => P) P`,
   `V.PosSemidef`, `(∀ n, AEMeasurable (Vhat n) P)`, `Measurable (id : (Fin 2 → ℝ) → _)`,
   `P.map id = (multivariateGaussian 0 V).map ofLp`.
   Optionally make V̂ data dependent, for example V̂_n(ω) = (1 + ‖ω‖²/(n+1)) I, which still
   →p I, so that `hV` is non-trivial. Also consider a Wald null-case conjunct (χ²(1) limit) for
   symmetry, unless the existing `ChiSquaredTests` witness is meant to cover it.

3. **nit — `wald_consistent` uses `(R*V*Rᵀ).PosDef`.** Invertibility plus positivity of
   (Rθ₀−c)ᵀ(RVRᵀ)⁻¹(Rθ₀−c) would suffice, and so would `V.PosSemidef ∧ IsUnit (RVRᵀ).det`, which
   matches `wald_chiSq`'s hypotheses so that one hypothesis set serves both size and power. PosDef
   is canonical, so this is acceptable as is.
   *Optional fix:* state a variant with `hVpsd : V.PosSemidef` and `hR : IsUnit (R*V*Rᵀ).det`
   (these imply RVRᵀ PD).

4. **nit — `t_normal` size is given as `gaussianReal 0 1 {x | a < |x|}`, not as 2(1 − Φ(a)).** The
   statement is fine. A lemma `gaussianReal 0 1 {x | a < |x|} = 2 * gaussianReal 0 1 (Set.Ioi a)`
   for a ≥ 0 would tie it to the textbook formula. Also, t_normal's (ii) duplicates t_tendsto plus
   the portmanteau theorem, which is fine.

5. **nit — witness alternatives.** `r ⬝ᵥ θ₁ ≠ 0` and `R *ᵥ θ₁ ≠ 0` are stated with c = 0 written
   implicitly as `0`. That is fine. The witness never instantiates c ≠ 0 or q ≥ 2, so it is a
   minimal, low-dimensional example.

6. **nit — `seInv` is defined but not used in any theorem statement.** It is a proof helper. It
   could be made private, or `tStat` could be defined as `√n * (rᵀθ − c) * seInv r V` for
   definitional transparency.

## Missing results (suggested)

- **t² = Wald for one restriction.** For R = the row matrix of r, `tStat n r c θ V ^ 2 =
  waldStat n R (fun _ => c) θ V` whenever rᵀVr > 0 (or under the junk conventions, with care). This
  is the standard link between §2.4's t and Wald tests.
- **Local (Pitman) alternatives** (N&M §9, D&M §4.5). Under θ_n = θ₀ + δ/√n:
  - t_n →d N(rᵀδ/√(rᵀVr), 1);
  - W_n →d noncentral χ²(q, λ) with λ = (Rδ)ᵀ(RVRᵀ)⁻¹(Rδ).

  This is the asymptotic-power statement that complements consistency.
- **One-sided t-test.** Size P(N(0,1) > a), and consistency against rᵀθ₀ > c only (with the power
  going to 0 against the other side).
- **Uniformity caveat.** Consistency is pointwise in the fixed alternative, as is standard. Nothing
  to add unless uniform power is wanted.
