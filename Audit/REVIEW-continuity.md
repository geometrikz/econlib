# Review record: continuity of demand and indirect utility (2026-11-23)

File: `EconLean/Consumer/Continuity.lean` (15 theorems, 2 definitions).
Frozen statements: generated into `challenge/` by `verify/make_challenge.py`.

## Step 1: context-isolated adversarial review
The reviewer saw only the statement files (proofs and comments stripped) and the
textbooks (MWG §3.D–3.E, Jehle–Reny, Aliprantis–Border). It was not told what
the authors intended.

**Result: no wrong or vacuous statement.** Budget correspondence uhc/lhc/closed
graph/compactness, `argmax_eq_demand`, `continuous_indirectUtility` and
`continuous_demand_function` are faithful; hypotheses are satisfiable
(u = Σ(1 − e^{−xᵢ}) meets every hypothesis of `exists_continuous_demand_function`).

Verdicts:
- **Faithful with documented deviation (fix recommended):** `StrictlyQuasiconcave`
  is required on all of ℝⁿ, not ℝⁿ₊, so `demand_subsingleton` and
  `exists_continuous_demand_function` miss textbook utilities such as Σ √xᵢ.
  Confirmed in Lean: `EconLean/Audit/ConsumerFindings.lean`, F7.
- **Faithful with documented deviation (harmless, document it):** `Continuous u`
  on all of ℝⁿ; replacing u by u(x ⊔ 0) gives the same demand and value.
- **Coverage gaps:** w = 0 (Jehle–Reny Thm 1.6 covers y ≥ 0); compact-valued
  demand; continuity of e(p, ū) (MWG 3.E.2) and of h(p, ū) (3.E.3); results for
  continuous preferences, not only utilities.
- **Check citations:** MWG Prop. 3.D.2 has parts (i)–(iii); continuity of demand
  is in the §3.D text (proof in M.K), and 3.D.3(iv) is continuity of v.

## Step 2: proof checks
Covered by `verify/check.sh` (lake check + lake comparator) on the whole library.

The reviewer's full report follows unchanged.

---

# Statement review: `EconLean/Consumer/Continuity.lean`

Reviewer: adversarial statement referee, working in isolation. I read only `/home/user/review_in2/`. Lean was not run. Every judgement comes from reasoning about Lean and Mathlib semantics.

Context definitions used (from the other files, which I did not review):
- `budgetSet p w = {x | 0 ≤ x ∧ cost p x ≤ w}`, where `cost p x = ∑ p i * x i`.
- `demand R p w = {x ∈ B(p,w) | ∀ y ∈ B(p,w), R x y}`.
- `prefOf u x y := u y ≤ u x`.
- `indirectUtility u p w = sSup (u '' budgetSet p w)`.
- `argmax`, `maxValue` and `ContinuousCorrespondence` come from Foundations. A correspondence is continuous when it is both UHC and LHC in Mathlib's sense.
- `upperHemicontinuousAt_iff_textbook` and `lowerHemicontinuousAt_iff_textbook` pin Mathlib's notions to the open-set definitions of Berge and Aliprantis–Border (Def 17.2). I assume those two lemmas are proved in their own file.

## Summary table

| # | Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|---|
| 1 | `PriceWealth` (abbrev) | MWG §3.D domain p ≫ 0, w > 0; Jehle–Reny Thm 1.6 uses p ≫ 0, y ≥ 0 | faithful with documented deviation | Matches MWG. Leaves out the w = 0 boundary that J–R includes (see F3). |
| 2 | `budgetCorr` | MWG 2.D.1, B(p,w) | faithful | Exactly B(p,w) on the subtype. The junk at w < 0 or p ≯ 0 cannot be reached. |
| 3 | `continuous_cost_joint` | none (auxiliary) | faithful | Joint continuity of (p,w,x) ↦ p·x on the subtype. |
| 4 | `isClosed_graph_budgetCorr` | A–B Ch. 17 (closed-graph characterization) / MWG M.H | faithful | Closed in the subspace PriceWealth × ℝ^L. That is what the uhc argument needs. |
| 5 | `eventually_near` | none (auxiliary) | faithful | True because p_i > 0 and w > 0. It is a local-boundedness helper with no economic content. |
| 6 | `upperHemicontinuous_budgetCorr` | Berge; A–B Ch. 17 (budget correspondence continuity); J–R App. A2 | faithful | Open-set uhc on all of p ≫ 0, w > 0. |
| 7 | `lowerHemicontinuous_budgetCorr` | same | faithful | lhc on p ≫ 0, w > 0, which is the standard interior condition. |
| 8 | `continuousCorrespondence_budgetCorr` | same | faithful | Both 6 and 7 together. |
| 9 | `budgetCorr_nonempty` | MWG 3.D (0 ∈ B) | faithful | |
| 10 | `isCompact_budgetCorr` | MWG 3.D.1 proof | faithful | |
| 11 | `continuous_uncurry_utility` | none (auxiliary) | faithful | Turns u into a parameter-independent objective for Berge. |
| 12 | `argmax_eq_demand` | definitional bridge | faithful | Both sides unfold to `{x ∈ B | ∀ y ∈ B, u y ≤ u x}`. Holds with no hypotheses on u. |
| 13 | `continuous_indirectUtility` | MWG Prop 3.D.3(iv); J–R Thm 1.6 | faithful with documented deviation | Uses global continuity of u on ℝ^L, but this costs no generality (F2). It does not need the LNS that MWG assumes, so it is stronger. Domain w > 0 only (F3). |
| 14 | `upperHemicontinuous_demand` | MWG §3.D text after 3.D.2 and M.K (Berge); A–B Berge Maximum Theorem (Ch. 17); J–R App. A2 (Berge) | faithful with documented deviation | Same deviations as 13. Compact-valuedness is not packaged here (F5). |
| 15 | `continuous_demand_function` | MWG §3.D / M.K: "if x(p,w) is single-valued it is continuous" | faithful | Uniqueness is an explicit hypothesis, which is legitimate. The hypothesis can be satisfied (2-good Cobb–Douglas). It does not presuppose continuity. |
| 16 | `StrictlyQuasiconcave` (def) | MWG Def 3.B.5 (strict convexity) and §3.C, strictly quasiconcave u | WEAK (too strong as a hypothesis) | Quantifies over all of ℝ^ι, not over ℝ^L_+. Standard utilities such as Σ√x_i (`Real.sqrt`) are strictly quasiconcave on ℝ^L_+ but fail this definition (F1). |
| 17 | `demand_subsingleton` | MWG Prop 3.D.2(iii), second half | faithful, inherits WEAK from 16 | Holds for all p and w, which is fine because B(p,w) is convex for every p and w. |
| 18 | `exists_continuous_demand_function` | MWG §3.D (continuity of Walrasian demand under strict convexity) | WEAK, inherits from 16 | The conclusion is right and as strong as the textbook's. The hypothesis is stronger than the textbook's. |

No item is VACUOUS-RISK. Every hypothesis set can be satisfied by a nondegenerate 2-good example, either u(x) = Σ_i (1 − e^{−x_i}) or Cobb–Douglas. I found no MISMATCH, meaning no case where the conclusion is wrong or weaker than claimed. None of the theorems is true only because of a junk value. `PriceWealth` is a subtype, so the `sSup ∅ = 0` junk of `indirectUtility` at w < 0 (shown in sanity test T6) can never be reached.

## Findings, ranked

### F1 (WEAK, most important). `StrictlyQuasiconcave` is required on all of ℝ^ι, not only on the consumption set

```lean
def StrictlyQuasiconcave (u : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y : ι → ℝ, x ≠ y → ∀ t, 0 < t → t < 1 → min (u x) (u y) < u (t • x + (1 - t) • y)
```

MWG defines strict convexity of ≿, and hence strict quasiconcavity of u, on the consumption set X = ℝ^L_+. Demand depends only on u restricted to ℝ^L_+. The Lean definition also constrains u on vectors with negative entries, and the economics never uses those values.

**Counterexample.** Take u(x) = Σ_i `Real.sqrt` (x_i) with 2 goods.
- On ℝ^2_+, u is strictly concave (√ is strictly concave on [0,∞) and the sum is separable), so it is strictly quasiconcave in MWG's sense. Its demand is unique and continuous.
- Mathlib sets √t = 0 for t < 0. With x = (−1,−1), y = (−2,−2) and t = 1/2, we get u(x) = u(y) = u(midpoint) = 0, so `min < u(...)` fails. Therefore `¬ StrictlyQuasiconcave u` (sanity test T2).

For this textbook example the user cannot apply `demand_subsingleton` or `exists_continuous_demand_function` directly. A strictly quasiconcave extension of u to ℝ^L must be built by hand. For √-type utilities a concave extension is impossible because the slope at 0 is infinite, and it is not clear that a strictly quasiconcave extension always exists. The hypothesis is stronger than the textbook's, so the theorem is weaker than MWG's.

Note that Cobb–Douglas fails strict quasiconcavity on the boundary even in MWG's sense, for example on the segment (0,1)–(0,2). So the Lean definition rejecting Cobb–Douglas is not itself a deviation. `continuous_demand_function` still covers Cobb–Douglas through its explicit uniqueness hypothesis.

**Fix.** Quantify over `0 ≤ x → 0 ≤ y → …`, or define it as `StrictlyQuasiconcaveOn (Set.Ici 0)`. Mathlib already has `StrictQuasiconcaveOn`, which would be preferable. Both theorems remain true under the weaker hypothesis, since only points of the convex set B(p,w) ⊆ ℝ^L_+ are used.

### F2 (documented deviation, harmless). `Continuous u` is global, not on ℝ^L_+

MWG and J–R assume u is continuous on ℝ^L_+. The Lean file requires continuity on all of ℝ^ι. This costs no generality, for two reasons:
- If u is continuous on ℝ^L_+, then ũ(x) = u(x ⊔ 0) is globally continuous.
- `demand (prefOf u) p w = demand (prefOf ũ) p w` and the indirect utilities are equal, because every budget point is ≥ 0 (sanity test T5).

This should be documented in the file. It differs from F1 because no "positive part" trick fixes strict quasiconcavity: x ↦ x ⊔ 0 collapses distinct points, which breaks strictness.

### F3 (coverage gap, minor). Domain w > 0 leaves out w = 0

J–R Thm 1.6 asserts that v(p,y) is continuous on ℝ^n_{++} × ℝ_+. At w = 0 with p ≫ 0, B = {0} (sanity test T7), and both the budget correspondence and demand remain continuous there relative to w ≥ 0. MWG works with w > 0, so the file is MWG-faithful. A J–R-faithful version would need `0 ≤ pw.2`. LHC at w = 0 relative to the domain w ≥ 0 still holds, because 0 ∈ B(p′,w′) for all w′ ≥ 0.

### F4 (citation hygiene). "MWG 3.D.2(iv)" is probably not an MWG label

As far as I recall, MWG Prop 3.D.2 has three parts: (i) homogeneity, (ii) Walras' law, (iii) convexity and uniqueness. Continuity of x(p,w) is stated in the running text and footnote of §3.D, with the proof deferred to M.K via the maximum theorem. Prop 3.D.3(iv) is the continuity of v. Docstrings that cite "3.D.2(iv)" should be corrected, for example to "MWG §3.D (text), proved in M.K; A–B Berge Maximum Theorem (Ch. 17)". I am uncertain about this because the comments were stripped and I could not see the exact citation.

### F5 (coverage gaps against MWG §3.D / §3.E)

1. **Compact-valuedness of demand** is not stated here. It is the standard companion of uhc (Berge gives "nonempty, compact-valued, uhc"). It can be derived from `berge_maximum_theorem` together with `argmax_eq_demand`, but the file states no such theorem. An instance of UHC without compact values is weak in Mathlib's open-set sense, because closed-graph and sequential characterizations require compactness.
2. **No closed-graph or sequential statement for demand.** Applications such as the existence of GE usually use the sequential form: if pⁿ → p and xⁿ ∈ x(pⁿ,wⁿ), then a subsequence converges into x(p,w). The general `UpperHemicontinuousAt.exists_tendsto_subseq` exists in Foundations, but no demand-specific corollary is given.
3. **MWG Prop 3.E.2** (e(p,u) is continuous) and **3.E.3** (h(p,u) is uhc, and continuous when single-valued) are missing from this file. Duality.lean also contains no continuity results for `expenditure` or `hicksian`. If the file is advertised as covering "continuity in §3.D–3.E", this is a gap. Continuity of e in ū needs care: ū must lie in the range of u above u(0), otherwise `sInf ∅ = 0` junk appears.
4. **Preferences rather than utility.** MWG states the results for continuous rational ≿ and uses Debreu's representation. The utility-only version is standard (J–R) and acceptable, but the preference version is not stated.
5. **Quasiconvexity, homogeneity and monotonicity of v** (the rest of 3.D.3) are not in this file. They appear partly in Duality.lean (`indirectUtility_smul`, `indirectUtility_mono`), so this is listed only for completeness.

## Checks that passed (attempted attacks)

- **Assuming the conclusion.** `continuous_demand_function` assumes only single-valuedness (`demand = {x pw}`), not continuity. `upperHemicontinuous_demand` assumes only `Continuous u`. Neither smuggles in the conclusion.
- **Vacuity.** The hypothesis `hx` can be satisfied. With u = √(x₁x₂) (rpow with exponent 1/2, which is globally continuous because exponent ≥ 0) and 2 goods, demand is {(w/2p₁, w/2p₂)}. `StrictlyQuasiconcave ∧ Continuous` can be satisfied by Σ(1 − e^{−x_i}), which is strictly concave on all of ℝ² and strictly increasing, so it is a genuine economic example (T3, T4).
- **Junk values.** `indirectUtility` uses `sSup`. On the domain, B is nonempty and compact and u is continuous, so `sSup` is a true maximum. When ι is empty, ℝ^ι is a single point and everything holds trivially. That is harmless and does not make any statement true for the wrong reason.
- **Topology.** `PriceWealth` carries the subspace topology of the product, which is the correct "continuity on p ≫ 0, w > 0". The graph is closed in the subspace, not in the full product, which is correct. In the full product it is false at the boundary w = 0 or p_i = 0 (the B(p,w) blow-up at p_i → 0).
- **Quantifiers.** `exists_continuous_demand_function` gives ∃ x, Continuous x ∧ ∀ pw, demand = {x pw}. This is the full textbook claim: the demand is a function, and that function is continuous.
- **`demand_subsingleton`** takes arbitrary p and w, including p with nonpositive entries. It is still true, since B(p,w) is convex for every p and w. It is also the empty set when w < 0 and p ≫ 0, and the empty set is subsingleton.
