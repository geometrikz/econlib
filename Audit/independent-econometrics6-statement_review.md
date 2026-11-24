# Statement review: PropensityScore, YuleWalker, TwoStepGMM

Scope: theorem statements only (proofs are `sorry`). References: Rosenbaum & Rubin (1983, "RR"),
Imbens & Rubin (2015, "IR"), Hamilton (1994) §3.4, Brockwell & Davis (1991, "BD") §3.3/§5.1,
Hansen (1982), Hayashi (2000) §3.5–3.6, Newey & McFadden (1994, "NM").

No outright false or contradictory statements found. Findings are ranked by severity.

## Defects (conclusion weaker than the name or textbook claim)

### D1. `two_step_jtest`: no chi-squared conclusion
- **Textbook claim** (Hansen 1982, Lemma 4.2; Hayashi Prop. 3.6; NM §9.5): J →d χ²(l−k).
- **What is stated:** (i) J →d L'·jForm(S,G)·L, and (ii) if L ~ N(0,S), then E[L'·jForm·L] = l − k.
- **Problem:** Part (ii) only matches the *first moment* of χ²(l−k). Many laws have mean l−k, so this does not give the reference distribution, the critical values or the test's size. The pieces needed are in JTest.lean: `jForm_mul_S_mul` (jForm·S is idempotent), `trace_jForm_mul` and `jForm_transpose`. The distributional statement is still missing.
- **Fix:** Mathlib has no `chiSquared`; grep finds none. Either define χ²(r) as the law of ‖Z‖² with Z ~ N(0, I_r), or as `gammaMeasure (r/2) (1/2)`. Then state `P'.map (fun ω => L ω ⬝ᵥ (jForm S G *ᵥ L ω)) = chiSquared (card l − card k)`. A cheaper middle step: there is A with A·Aᵀ = I_{l−k} and L'·jForm·L = ‖A·S^{-1/2}·L‖², so the quadratic form equals in law the sum of l−k squared iid N(0,1). Until then, the docstring and name should say "mean of the J limit", not "J-test".

### D2. `two_step_gmm` / `two_step_jtest`: "two-step" is not modelled (naming/scope)
- **Textbook procedure** (Hansen 1982; Hayashi §3.5, Prop. 3.5): step 1 uses some W to get θ̃, builds Ŝ from residuals at θ̃, then step 2 uses Ŵ = Ŝ⁻¹.
- **What is stated:** Ŝ is any sequence with Ŝ →p S, supplied as a hypothesis. The first-step estimator and the construction of Ŝ from its residuals do not appear.
- **Assessment:** As "efficient GMM with a consistently estimated optimal weight" (Hayashi Prop. 3.5 with Assumption 3.6 given), the statement is fine. The name oversells it.
- **Fix:** Rename (e.g. `efficient_gmm_feasible`), or add a lemma that discharges `hShat` from a first step. For linear GMM with Ŝ = (1/n)Σ ε̂ᵢ² zᵢzᵢ', the abstract version is: `hShat` follows from consistency of the first step (`gmm_consistent`) plus a continuity / ULLN hypothesis.

## Concerns

### C1. `two_step_witness` does not exercise efficient weighting
- **Setup:** S = I₂, G = (1,1)', Ŝ ≡ S constant, Ĝ ≡ G constant.
- **Problem:** With S = I the efficient weight S⁻¹ = I. So the "two-step" estimator is the identity-weighted one-step estimator, and the efficient-vs-arbitrary distinction is never tested. Constant Ŝ and Ĝ also make both `TendstoInMeasure` hypotheses trivial.
- **What it does show:** the hypotheses are jointly satisfiable, with l = 2 > k = 1 so the J degrees of freedom are 1. That is good.
- **What it does not do:** it does not apply `two_step_gmm` / `two_step_jtest`. It only lists satisfied hypotheses, and it omits `hGm`, `hSm`, `hgm`.
- **Suggestion:** use a non-scalar S, e.g. diag(1,4), and make Ŝₙ = S + (1/n)·noise, so that S⁻¹ actually changes the estimator.

### C2. Redundant hypotheses in `two_step_gmm` / `two_step_jtest`
- `hgm` is almost implied by `hg.forall_aemeasurable`. Mathlib's `TendstoInDistribution` carries AEMeasurable of √n·gₙ, which gives AEMeasurable gₙ for n ≥ 1.
- `Measurable L` in the second conjuncts could be weakened to the `AEMeasurable L` that `hg` already provides.
- Harmless, but superfluous.

### C3. `rosenbaum_rubin` is the mean-independence, finite-covariate version
- **RR Thm 3:** (Y₀,Y₁) ⊥ D | X together with 0 < e(X) < 1 implies the same given e(X).
- **What is formalised:** MeanUnconfounded (E[Y(d) | D, X] = E[Y(d) | X], as in IR Ch. 12) is preserved under e(X), for finite κ.
- **Second conjunct:** P(D=d | e(X)=e(x)) = P(D=d | X=x) on non-null strata. For discrete X this is exactly the balancing property X ⊥ D | e(X) (RR Thm 1), so that part is correctly captured, though only implicitly.
- **Gap:** the overlap half of strong ignorability (Overlap X ⇒ Overlap e(X)) is not stated.
- **Docstring:** should say "mean version, discrete X".
- **Coding convention (harmless):** `pscore` sends null strata to propensity 0 (0/0 = 0 in `armProb`), merging them with genuine e = 0 strata. Null strata have no mass, so nothing changes, but it is worth a comment.

### C4. RR Theorem 2 only in the "if" direction
- `meanUnconfounded_coarsen` / `armProb_coarsen` prove that any b(X) finer than e(X) is a balancing score. That is the hypothesis `hg`: g x = g x' ⇒ e(x) = e(x') on non-null strata.
- The converse is missing: a balancing b must satisfy e(X) = f(b(X)).

### C5. YuleWalker: `Autocov` / `Innovation` are raw second moments
- **What the definitions are:** `Autocov` is E[x_t·x_s] = γ(t−s), uncentred. `Innovation` says E[ε_t·x_s] = 0 for s < t and E[ε_t·x_t] = σ².
- **Missing assumptions:** zero mean is never assumed (no E ε_t = 0, no E x_t = 0). So γ is the autocovariance only for zero-mean processes, and σ² equals E[ε_t²], not Var ε_t.
- **Correctness:** the Yule–Walker identities are still correct for second moments. The `Innovation` condition correctly encodes causality: it rules out the non-causal stationary solution when |φ| > 1.
- **Recommendation:** document this, or add `∫ x t = 0` to the hypotheses. A lemma σ² = ∫ ε_t² (it follows from the hypotheses) would also connect σ² to the textbook object.

### C6. `IsAR` indexes the order as p+1
- `φ : Fin (p+1) → ℝ` means `IsAR` with parameter p is an AR(p+1). `ar1_autocov` uses p := 0.
- AR(0) (white noise) is excluded. This is easy to misread against Hamilton's φ₁…φ_p.
- Statements are internally consistent: `yule_walker` h ≥ 1 gives γ(h) = Σ_j φ_j·γ(h−1−j), matching Hamilton (3.4.36) and BD (3.3.8).

### C7. `yule_walker_identify` assumes rather than derives invertibility of Γ
- **Assumption:** `IsUnit (toeplitz γ).det`.
- **Canonical result** (BD Prop. 5.1.1): γ(0) > 0 and γ(h) → 0 imply Γ_p is non-singular. For a causal AR with σ² > 0, Γ is positive definite.
- **Missing lemma** (cheap and canonical): σ² > 0 (and μ ≠ 0) ⇒ toeplitz γ is PosDef, hence invertible. Without it the identification statement is conditional on exactly the thing that makes it interesting.

### C8. No non-vacuity witness for YuleWalker
- The only obvious witness is x ≡ ε ≡ 0.
- On a point mass, any witness forces σ² = 0. A genuine witness needs a bi-infinite stationary Gaussian AR(1) on a product space, which is more expensive.
- The hypotheses are clearly consistent mathematically, so this is a low priority.

## OK items

**PropensityScore**
- `cell_comp_eq`, `stratum_comp_eq`, `measureReal_cell_add`, `measureReal_cell_le`: correct bookkeeping.
- `cell_cross`: correct. It is the cross-multiplied form of equal propensities, with null strata handled by the guarded hypothesis.
- `setIntegral_cell`, `condMean_coarsen`, `meanUnconfounded_coarsen`, `armProb_coarsen`: correct, with sensible null-cell guards.
- `pscore`: has codomain `Set.range propensity`, finite via `Fintype.ofFinite`; acceptable.
- Definitions: `stratum`, `cell`, `armProb`, `propensity`, `Overlap` and `MeanUnconfounded` (in Unconfoundedness.lean) match IR Ch. 3/12 in the discrete-X setting. Only `IsFiniteMeasure` is needed, since everything is a ratio; this is a mild generalisation.
- The task mentioned `MeasureUnconfounded`; it does not exist in these files, and only `MeanUnconfounded` is used.

**YuleWalker**
- `autocov_neg`, `integral_ar_mul`, `yule_walker`, `yule_walker_zero`: OK.
  - `yule_walker_zero`: γ(0) = Σ φ_j·γ(1+j) + σ², as in Hamilton (3.4.37) and BD (3.3.9).
- `toeplitz` and the first conjunct of `yule_walker_identify` (Γ_p·φ = γ_p): OK.
- `ar1_autocov`: OK. It gives γ(h) = φ^h·γ(0) for h ∈ ℕ, (1 − φ²)·γ(0) = σ² and γ(0) = σ²/(1 − φ²), as in Hamilton (3.4.5)–(3.4.6). Negative h follows from `autocov_neg`. The φ² = 1 case correctly forces σ² = 0.

**TwoStepGMM**
- `invFn`, `of_invFn`, `continuousAt_invFn`, `measurable_invFn`, `tendstoInMeasure_invFn`, `of_invFn_symm`, `rank_two_step`: OK. `rank_two_step` is G'S⁻¹G non-singular under full column rank and S positive definite.
- `two_step_gmm`: OK as efficient GMM with consistent Ŝ (aside from D2).
  - The moment structure σ̂ = Ĝθ₀ + gₙ is linear GMM, as in Hayashi §3.5.
  - The limit law N(0, (G'S⁻¹G)⁻¹) is correct (Hayashi Prop. 3.5(b), (3.5.14)).
  - The link between S (the plim of Ŝ) and the law of L appears only in the second conjunct. That is a correct modular design.
- Dependencies (gram, gmmA, jStat, jForm, `GMM.estimator`, `GMM.avar`, `avar_sub_posSemidef`) match the textbook objects:
  - `jStat` = n·ĝ(θ̂)'·Ŵ·ĝ(θ̂), with the two-step Ŵ = Ŝ⁻¹ plugged in.
  - `jForm` = S⁻¹ − S⁻¹G(G'S⁻¹G)⁻¹G'S⁻¹.

## Missing canonical results that would be cheap to add

1. **Propensity-score adjustment / IPW on e(X):**
   - `Overlap μ X D → Overlap μ (pscore ∘ X) D`. One line from `armProb_coarsen`.
   - Then `ate_eq_adjustment` and `ate_eq_ipw` with X replaced by e(X), applied to `rosenbaum_rubin`. This is the practical payoff of RR (1983, §3; IR Ch. 12–13).
2. **Converse of RR Thm 2:** if a coarsening g preserves arm probabilities on all non-null strata, then e is a function of g(X) on non-null strata.
3. **J test:** the χ²(l − k) law (D1), or at least the quadratic form expressed as a sum of l − k iid squared standard normals.
4. **Asymptotic variance estimator:** (Ĝ'Ŝ⁻¹Ĝ)⁻¹ →p (G'S⁻¹G)⁻¹, by `tendstoInMeasure_invFn` plus continuity (Hayashi Prop. 3.5(c)). Needed for Wald tests and standard errors.
5. **Efficiency of the two-step limit:** for any W₀ with gram unit, avar(W₀) − (G'S⁻¹G)⁻¹ ⪰ 0. This is already `GMM.avar_sub_posSemidef`; a corollary should restate it in terms of the two-step limit laws.
6. **Yule–Walker:**
   - σ² > 0 ⇒ toeplitz γ is PosDef (BD Prop. 5.1.1).
   - AR(1): σ² > 0 ⇒ |φ| < 1. This is immediate from (1 − φ²)·γ(0) = σ² and γ(0) = ∫ x_t² ≥ 0.
   - σ² = ∫ ε_t².
   - The Yule–Walker estimator as a plug-in φ̂ = Γ̂⁻¹·γ̂, consistent whenever γ̂ →p γ, by continuity of matrix inverse.
