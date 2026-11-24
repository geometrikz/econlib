# Statement review: chiSq_add, GMMWald.lean

## Verdicts

| Declaration | Verdict |
|---|---|
| `chiSq_add` | OK |
| `avarHat` | OK |
| `measurable_avarHat` | OK |
| `avarHat_eq` | OK |
| `continuousAt_avarHat` | OK (nit 5) |
| `two_step_wald` | OK (caveats 1, 2; nit 6) |
| `two_step_wald_witness` | ISSUE, caveat (issues 3, 4) |

No defects found. Every statement is true as written and matches the textbook result.

## Checks performed

- **chiSq_add.** `chiSq r` is the law of `∑_{i<r} Z_i²` with `Z` iid N(0,1). `(μ.prod ν).map (+)` is the law of
  X+Y with X ~ μ and Y ~ ν independent, so the statement says χ²(a) * χ²(b) = χ²(a+b). That is the standard
  convolution fact. Edge cases a=0 or b=0: `chiSq 0 = dirac 0`, so the statement reduces to `map id`. Correct.
- **avarHat.** `avarHat (Ĝ, Ŝ) = invFn (gram (Ĝ, invFn Ŝ)) = (ĜᵀŜ⁻¹Ĝ)⁻¹`. This is Hayashi (3.5.13) /
  Hansen (1982) Thm 3.2, the efficient-GMM Avar estimator. It inverts Ŝ itself, so the same Ŝ serves as the
  weight W = Ŝ⁻¹ and in the variance. This is the right pairing for the efficient estimator.
  `avarHat_eq` states exactly this, with the matrix↔function coercions placed consistently.
  If Ŝ is singular, or ĜᵀŜ⁻¹Ĝ is singular, Mathlib's `⁻¹ = 0` gives `avarHat = 0`. The Wald weight
  `(R·0·Rᵀ)⁻¹ = 0` then makes Wₙ = 0. This happens only on events whose probability → 0, so it does not
  affect the asymptotic statement.
- **continuousAt_avarHat.** S PD together with G of full column rank (injective `G *ᵥ ·`) gives
  GᵀS⁻¹G PD and so invertible. Continuity of matrix inversion at an invertible point then gives the result.
  Correct, and these are exactly the hypotheses `two_step_wald` needs.
- **Linear-GMM parametrisation in two_step_wald.** The estimator is `(ĜᵀŴĜ)⁻¹ĜᵀŴσ` with
  `σ = Ĝθ₀ + ĝ` and `Ŵ = Ŝ⁻¹`. Linear GMM (Hayashi §3.4–3.5) uses g_n(δ) = s_xy − S_xz δ. Take
  Ĝ = S_xz, σ = s_xy and ĝ = ḡ = (1/n)Σ x_i ε_i. Since s_xy = S_xz δ₀ + ḡ identically, g_n(θ₀) = ĝ.
  This loses no generality: for any s_xy one can define ĝ := s_xy − Ĝθ₀. The estimator is therefore the
  two-step efficient GMM estimator evaluated at the data. Ŝ is abstract: any Ŝ →p S. That is Hayashi's
  Assumption/Prop 3.5 abstraction of the first-step Ŝ. Using the same S for plim Ŝ and for the limit law
  N(0,S) of √n ĝ is the efficiency assumption. Correct.
- **Wald statistic.** `waldStat n R c θ̂ V̂ = n (Rθ̂−c)ᵀ (R V̂ Rᵀ)⁻¹ (Rθ̂−c)` with V̂ = avarHat. This matches
  Hayashi Prop 3.3(b)/3.5 and Newey–McFadden §9.1. Limit χ²(#rows of R). Correct.
- **hR.** `Function.Injective (Rᵀ *ᵥ ·)` with Rᵀ : k×q is equivalent to Rᵀ having full column rank q,
  i.e. R having full row rank. This is the standard (not too strong) condition. It is also exactly what
  makes R V Rᵀ PD for V PD. Together with hG it forces q ≤ k ≤ l. Correct.
- **Hypotheses jointly satisfiable / not contradictory.** Yes. `two_step_witness` (upstream) discharges all
  hypotheses of `two_step_gmm`, and hR / hnull hold trivially with R = 1, c = 0, θ₀ = 0.
- **∃ Z.** `TendstoInDistribution` contains `aemeasurable_limit`, and convergence depends on Z only through
  its law. So `∃ Z, Wₙ →d Z ∧ law Z = χ²(q)` is equivalent to "Wₙ ⇒ χ²(q)", provided Ω' carries some
  χ²(q) variable. It does, because a function of L works. Z cannot be degenerate for q > 0, since χ²(q) is
  non-atomic there. For q = 0, Wₙ ≡ 0 (empty dot product) and `chiSq 0 = dirac 0`, so the statement is
  correct and the conclusion degenerates appropriately.
- **Witness computation.** S = diag(1,2), G = (1,1)ᵀ (l=2, k=1, one overidentifying restriction),
  θ₀ = 0, R = 1, c = 0, ĝ = ω/√n with ω ~ N(0,S). Then GᵀS⁻¹G = 3/2, Avar = 2/3, and
  √n θ̂ = (2/3)(ω₁ + ω₂/2) ~ N(0, (4/9)(1 + 1/2)) = N(0, 2/3). So Wₙ = (3/2)(√n θ̂)² ~ χ²(1)
  exactly for every n ≥ 1. At n=0, √0⁻¹ = 0 gives W₀ = 0, which is irrelevant to the limit. The statement
  is true and non-degenerate: q = 1 > 0, the model is overidentified, and the null is genuinely tested.

## Issues

1. **(caveat) `two_step_wald`: limit given only through the existential.** The ∃ Z form is
   mathematically fine (see above). However, it hides the explicit limit
   Z = (R A L)ᵀ (R Avar Rᵀ)⁻¹ (R A L) with A = gmmA(G, S⁻¹), and the companion `wald_chiSq` makes that
   limit explicit. *Fix (optional):* state `TendstoInDistribution … (fun ω => (R *ᵥ (A *ᵥ L ω)) ⬝ᵥ
   ((R * V * Rᵀ)⁻¹ *ᵥ (R *ᵥ (A *ᵥ L ω))))` with V = (GᵀS⁻¹G)⁻¹, plus a separate law equation. That form
   is stronger, because it fixes a specific coupling, and it is easier to reuse.
2. **(caveat) `two_step_wald`: Ŝ is not tied to first-step residuals.** "Two-step" is modelled as "any
   consistent Ŝ". That is the standard textbook abstraction (Hayashi Prop 3.5 takes Ŝ →p S as given), but
   the statement does not prove consistency of the residual-based Ŝ built from a first-step estimator. The
   docstring should say this. No change is needed in the statement.
3. **(caveat) `two_step_wald_witness` re-proves the conclusion on an example but does not instantiate
   `two_step_wald`.** Its claim is just "for this concrete DGP, P(Wₙ > a) → χ²₁(a,∞)". That holds by direct
   computation, whatever the hypotheses of `two_step_wald` say. So it does not certify that hR and hnull,
   together with the rest, are satisfiable. (They are, but via `two_step_witness` plus trivial facts.) It
   also covers only the second conjunct, not the ∃ Z part. *Fix:* mirror `two_step_witness`: bundle
   `S.PosDef ∧ Injective (G*ᵥ·) ∧ … ∧ R *ᵥ θ₀ = c ∧ Injective (Rᵀ *ᵥ ·)` (or literally
   `two_step_witness ∧ hnull ∧ hR`), so the witness shows that the theorem's hypotheses are consistent and
   non-vacuous. Alternatively, prove it as a corollary `by exact (two_step_wald … ).2 one_pos a`.
4. **(caveat/nit) Witness uses a square R = 1 with k = 1.** This exercises the full-row-rank condition only
   trivially (q = k) and never the rectangular R V Rᵀ. *Fix:* use k = 2, l = 3 (still overidentified) and
   R = [1, −1] (q = 1 < k), e.g. testing θ₁ = θ₂. That instance is a genuine linear restriction and makes
   hR non-trivial.
5. **(nit) `continuousAt_avarHat`.** The hypotheses could be weakened to `IsUnit (Gᵀ S⁻¹ G).det` and
   `IsUnit S.det`. The PD form is fine and matches the downstream use.
6. **(nit) `two_step_wald`: guard `0 < Fintype.card q →` is unnecessary.** For q = 0, Wₙ ≡ 0 and
   χ²₀ = δ₀, so P(Wₙ > a) = δ₀(a,∞) holds for every n. The guard is harmless. It is inherited from
   `tendsto_prob_gt_of_chiSq`, which needs atomlessness. The second conjunct also follows from the first
   via that lemma, so it is redundant but convenient.

## Missing results (suggestions)

- Consistency of the Wald test under fixed alternatives (Rθ₀ ≠ c ⇒ P(Wₙ > a) → 1), and/or local power
  (noncentral χ²). This is standard alongside the null result (Newey–McFadden §9.2, Hayashi §3.7 remarks).
- Distance-metric / LR-type statistic (Hayashi Prop 3.8, Newey–McFadden §9.3): n(J(θ̃) − J(θ̂)) →d χ²(q)
  and its asymptotic equivalence with the Wald statistic. Also the C (difference-in-J) test.
- Joint statement: W ⇒ χ²(q) and J ⇒ χ²(l−k) with the limits independent. `chiSq_add` would then give
  J(restricted) ⇒ χ²(l−k+q). `chiSq_add` is currently not used for this.
- Consistency of avarHat itself (avarHat(Ĝₙ, Ŝₙ) →p (GᵀS⁻¹G)⁻¹) as a stand-alone lemma. It is an easy
  corollary of `continuousAt_avarHat`, and other inference results (t-tests, confidence regions) would reuse it.
