# Statement review (reviewer A): GE + Foundations (supporting hyperplane, correspondences, Berge)

Scope: `GE/Exchange.lean`, `GE/SecondWelfare.lean`, `GE/Existence.lean`, `GE/Production.lean`,
`GE/Examples.lean`, `Foundations/SupportingHyperplane.lean`, `Foundations/Correspondence.lean`,
`Foundations/Maximum.lean`. Context definitions read: `Preferences/Basic.lean`,
`Preferences/Utility.lean`, `Consumer/Budget.lean`, `Consumer/Demand.lean` (`demand`,
`LocallyNonsatiated`, `StronglyMonotone`, `ConvexPref`).
Lean was not available, so everything below comes from reading the Lean/Mathlib semantics, and every concern has a matching test in `sanity_tests.lean`.

References: MWG = Mas-Colell, Whinston, Green (1995); AB = Aliprantis & Border, *Infinite
Dimensional Analysis* (3rd ed.), ch. 17; Debreu = *Theory of Value* (1959).

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `ConvexPref` (used as a hypothesis in both SWTs) | Consumer/Demand (used in GE/SecondWelfare, GE/Production) | MWG Def. 3.B.4 (convexity on the consumption set X = ℝⁿ₊) | **MISMATCH** | Requires upper contour sets to be convex in all of ℝⁿ, not ℝⁿ₊. `prefOf (Σ √xᵢ)` fails it (Mathlib `√` = 0 on negatives), so both SWTs do not apply to standard concave utilities |
| `second_welfare_theorem` (exchange) | GE/SecondWelfare | MWG Prop. 16.D.1 | **WEAK** | Statement and conclusion match 16.D.1, but the `ConvexPref` hypothesis is too strong (see above) |
| `second_welfare_theorem_demand` | GE/SecondWelfare | MWG 16.D.1 + 16.D.3/16.D.4 (cheaper point) | **WEAK** | Same `ConvexPref` problem. `hpos : x ≫ 0` is a standard sufficient condition (fine) |
| `ProductionEconomy.second_welfare_theorem` | GE/Production | MWG Prop. 16.D.1 | **WEAK** | Same `ConvexPref` problem. There is no production counterpart of `_demand`/`price_nonneg` (coverage gap) |
| `exists_freeDisposalEquilibrium` | GE/Existence | MWG 17.C.1 / Debreu 5.6 / AB | **VACUOUS-RISK** (for standard economies) | Requires a demand *selection on the closed simplex*. For any strongly monotone preferences, demand is empty at boundary prices, so the hypothesis cannot be met for Cobb–Douglas, linear and similar preferences. It is also conditional on `BrouwerSimplex ι` |
| `gale_nikaido_debreu` | GE/Existence | Debreu §5.6 (GND lemma); AB 17.x | **faithful with documented deviation** | Brouwer for the simplex is a *hypothesis* (`hB`), proved only for `Fin 2`. Single-valued `z` (the canonical result is for uhc convex-valued correspondences) |
| `BrouwerSimplex`, `brouwerSimplex_fin_two` | GE/Existence | Brouwer FPT | faithful (n = 2 only) | The definition is correct. `BrouwerSimplex (Fin 0)` is false (empty simplex), which is harmless |
| `exists_freeDisposalEquilibrium_two_goods` | GE/Existence | as above | **VACUOUS-RISK** | Unconditional on Brouwer, but has the same boundary-demand problem. The only witness (`leonEconomy`) is degenerate: every price is an equilibrium |
| `IsFreeDisposalEquilibrium` | GE/Existence | Debreu 5.7; MWG 17.B (free disposal) | faithful | p ≥ 0, demand, Σx ≤ ω̄, and goods in excess supply are free |
| `IsFreeDisposalEquilibrium.isWalrasianEquilibrium` | GE/Existence | — | faithful | Needs p ≫ 0, which is correct |
| `cost_excessDemand`, `isWalrasianEquilibrium_of_excessDemand_eq_zero`, `price_eq_zero_of_excess_supply` | GE/Existence | MWG 17.B.2 (Walras' law) | faithful | |
| *(missing)* existence with boundary condition / interior prices | GE/Existence | MWG Prop. 17.C.1 (z(p) unbounded as p → ∂Δ); Arrow–Debreu with production | **coverage gap** | No `IsWalrasianEquilibrium` existence theorem for standard (strongly monotone) economies, and none with production |
| `ExchangeEconomy.Feasible` / `Blocks` / `ParetoOptimal` | GE/Exchange | MWG 15.B (≤), 16.B.1, 18.B.2; Debreu (≤) | **faithful with documented deviation** | Feasibility uses *equality* (no free disposal). This matches MWG ch. 16's convention, but makes "Pareto optimal" and "in the core" weaker than the ≤ versions when preferences are non-monotone (see the bad-good example) |
| `ParetoDominates`, `WeaklyParetoOptimal`, `InCore`, `IndividuallyRational` | GE/Exchange | MWG 16.B.2, 18.B | faithful | |
| `IsWalrasianEquilibrium` (exchange) | GE/Exchange | MWG 15.B.1 / 17.B.1 | faithful with documented deviation | No sign or normalisation restriction on `p`. Negative prices are allowed, which is harmless for the theorems below (FWT does not need p ≥ 0 because feasibility is an equality) |
| `first_welfare_theorem` (exchange) | GE/Exchange | MWG Prop. 16.C.1 | faithful (conclusion relative to equality feasibility) | Hypotheses are satisfiable (`linEconomy`, `asymEconomy`). LNS is restricted to ℝⁿ₊ correctly |
| `IsWalrasianEquilibrium.inCore` | GE/Exchange | MWG Prop. 18.B.1 | faithful (equality blocking) | No LNS needed, which is correct for strict blocking. The core is relative to equality-feasible blocking |
| `InCore.individuallyRational`, `InCore.weaklyParetoOptimal`, `IsWalrasianEquilibrium.individuallyRational`, `ParetoOptimal.weaklyParetoOptimal` | GE/Exchange | MWG 18.B | faithful | |
| `cost_gt_of_mem_demand`, `cost_ge_of_mem_demand`, `Feasible.sum_cost`, `feasible_endow`, `cost_sum` | GE/Exchange | MWG 16.C proof steps | faithful | |
| `IsPriceEquilibriumWithTransfers`, `IsPriceQuasiEquilibriumWithTransfers` (exchange & production) | GE/SecondWelfare, GE/Production | MWG Def. 16.B.4, 16.D.1 | faithful | |
| `IsPriceEquilibriumWithTransfers.paretoOptimal`, `.cost_eq`, `.cost_ge`, `.mem_demand`, `.quasi` | GE/SecondWelfare | MWG Prop. 16.C.1 (with transfers) | faithful | |
| `cost_gt_of_cheaper_point`, `…quasi….isPriceEquilibriumWithTransfers` | GE/SecondWelfare, GE/Production | MWG Prop. 16.D.3 | faithful | Continuity is used relative to ℝⁿ₊, correctly |
| `IsPriceQuasiEquilibriumWithTransfers.price_nonneg` | GE/SecondWelfare | MWG 16.D (p ≥ 0 under monotonicity) | faithful | |
| `ContinuousPref` | GE/SecondWelfare | MWG Def. 3.C.1 | faithful | Relative-closedness in ℝⁿ₊ for x ≥ 0 |
| `convex_strictUpper`, `mem_closure_strictUpper` | GE/SecondWelfare | MWG 16.D proof | faithful | `convex_strictUpper` inherits the global `ConvexPref` |
| `ProductionEconomy` (structure), `Feasible`, `wealth`, `ProfitMax`, `ParetoOptimal`, `IsWalrasianEquilibrium` | GE/Production | MWG 16.B.1–16.B.3 | faithful | `Y_j` are arbitrary sets, which is fine for the welfare theorems |
| `ProductionEconomy.first_welfare_theorem`, `sum_wealth`, `.feasible` | GE/Production | MWG Prop. 16.C.1 | faithful | |
| `exists_cost_eq_linearMap(_ne_zero)`, `exists_linearMap_support`, `exists_price_support` | Foundations/SupportingHyperplane | MWG Thm. M.G.3; Rockafellar Thm 11.6 | faithful | Statement for `x ∉ interior C` (covers both boundary points and exterior points) |
| *(missing)* separating hyperplane for two disjoint convex sets | Foundations/SupportingHyperplane | MWG M.G.2 | coverage gap (minor) | Production SWT needs it. It may be proved inline |
| `upperHemicontinuousAt_iff_textbook`, `lowerHemicontinuousAt_iff_textbook` | Foundations/Correspondence | MWG Def. M.H.3/M.H.4; AB 17.2 | faithful | Two-directional bridges to Mathlib's `UpperHemicontinuous`/`LowerHemicontinuous`, which is good practice. `ContinuousCorrespondence` relies on them |
| `isClosed_graph_of_upperHemicontinuous` | Foundations/Correspondence | AB Thm. 17.10 | faithful | Regular Y + closed values |
| `upperHemicontinuousAt_of_isClosed_graph`, `upperHemicontinuous_of_isClosed_graph` | Foundations/Correspondence | AB Thm. 17.11; MWG M.H | faithful | |
| `UpperHemicontinuousAt.inter_of_isClosed_graph` | Foundations/Correspondence | AB Thm. 17.25 | faithful | |
| `IsCompact.biUnion_of_upperHemicontinuous` | Foundations/Correspondence | AB Lemma 17.8 | faithful | |
| `isClosed_graph_iff_seq`, `UpperHemicontinuousAt.exists_tendsto_subseq`, `isClosed_of_isClosed_graph`, `congr'` | Foundations/Correspondence | AB 17.16, 17.20 | faithful | |
| `maxValue` | Foundations/Maximum | MWG M.K; AB 17.31 | faithful with documented deviation | `sSup` takes junk value 0 on empty or unbounded sets. Every theorem guards this with `hne` and `hK` |
| `berge_maximum_theorem` | Foundations/Maximum | MWG Thm. M.K.6; AB Thm. 17.31 | faithful with documented deviation | `f` must be continuous on all of X × Y (AB: only on Gr Φ), which is slightly stronger. The conclusion is complete (value attained, continuous, argmax nonempty, compact and uhc) |
| `upperSemicontinuous_maxValue`, `lowerSemicontinuous_maxValue`, `continuous_maxValue`, `argmax_*`, `upperHemicontinuous_argmax`, `continuous_of_argmax_eq_singleton` | Foundations/Maximum | AB Lemmas 17.29, 17.30; Thm 17.31 | faithful | |
| `GEExamples.*` | GE/Examples | MWG 15.B Edgeworth box | faithful, but see note | Welfare examples are fine. The existence example uses a Leontief economy where *every* simplex price is an equilibrium, so it is a weak witness. This choice is itself a symptom of the existence finding |

## Detailed findings

### 1. `ConvexPref` is global on ℝⁿ, so both second welfare theorems exclude Σ√xᵢ (MISMATCH, then WEAK)

`ConvexPref R := ∀ x, Convex ℝ {y | R y x}` quantifies over all of `ι → ℝ`. MWG (Def. 3.B.4)
requires convexity of upper contour sets *within the consumption set* ℝⁿ₊. For
`u x = √(x 0) + √(x 1)` with Mathlib's `Real.sqrt` (= 0 on negatives), take `x = (1,0)`
(u = 1). Then
- `y = (1, −4)`: u y = 1 + 0 = 1 ≥ 1, so y is in the upper contour set;
- `z = (−4, 1)`: u z = 1, also in the set;
- the midpoint `(−3/2, −3/2)` has u = 0 < 1, so it is not in the set.

So `¬ ConvexPref (prefOf u)`, although u is concave and strictly monotone on ℝⁿ₊. `prefOf` of Cobb–Douglas
via `Real.rpow` has the same problem (rpow of negatives is a cos-modulated junk value). As a result,
`ExchangeEconomy.second_welfare_theorem`, `second_welfare_theorem_demand` and
`ProductionEconomy.second_welfare_theorem` cannot be applied to the textbook examples. A user
can only work around this by building an artificial extension, for example u := −1 off ℝⁿ₊.
The theorems are still *true*, because a stronger hypothesis is harmless for soundness, but they
are stated with a stronger hypothesis than the canonical one. All other preference properties
(`LocallyNonsatiated`, `StronglyMonotone`, `ContinuousPref`) are correctly relativised to
`0 ≤ x`, so only this definition is inconsistent with the rest.
**Fix:** `ConvexPref R := ∀ x, 0 ≤ x → Convex ℝ {y | 0 ≤ y ∧ R y x}`. `convex_strictUpper`
already intersects with `0 ≤ y`, so the SWT proofs should go through unchanged.
Test: `sqrt_not_convexPref` in `sanity_tests.lean`.

### 2. The existence theorem needs a demand selection on the closed simplex, which no strongly monotone economy has (VACUOUS-RISK)

`exists_freeDisposalEquilibrium` and `_two_goods` assume `E.IsDemandSelection d (priceSimplex ι)`,
which says `d a p ∈ demand …` for **every** p in the closed simplex, including vertices such as
p = (1,0). For any strongly monotone preference (or any preference with LNS that is strictly
increasing in a good whose price is 0), the budget set at such p is unbounded in the free good
and demand is **empty**, so the hypothesis is false. Specifically:
- `linEconomy` (linear, used in the welfare examples) has no such selection (test
  `linEconomy_no_demandSelection`);
- in general, strongly monotone preferences with ≥ 2 goods admit no such selection (test
  `stronglyMonotone_no_demandSelection`, sorry'd).

The hypotheses are not jointly contradictory. Leontief works (as the file shows), and so does
`u = −(x₀−x₁)² + φ(x₀+x₁)` with φ bounded and increasing. But the canonical existence theorem
(MWG 17.C.1) handles exactly the standard case through the boundary condition "‖z(pₙ)‖ → ∞ as pₙ → ∂Δ"
with z defined only on the interior of the simplex. Debreu and Arrow–Debreu handle it by truncating consumption sets.
Neither route is formalised, so **there is no theorem giving a Walrasian (or free-disposal)
equilibrium for any Cobb–Douglas, CES or linear economy**. In addition, the n-good version takes Brouwer
as hypothesis `hB`, which is proved only for `Fin 2`. The one existence example
(`leonEconomy`, `dLeon`) is degenerate: Σ_a dLeon a p = (p·ω̄, p·ω̄) = (3,3) = ω̄ for every p in
the simplex, so every price is an equilibrium (test `leon_every_price_is_equilibrium`).

### 3. `BrouwerSimplex` is a hypothesis of `gale_nikaido_debreu` (documented deviation)

`gale_nikaido_debreu (hB : BrouwerSimplex ι) …` is correct as a reduction GND ⇐ Brouwer. The
topological core of the existence theory is assumed, and it is discharged only for two goods. Any summary
should not say "existence of Walrasian equilibrium is formalised". The accurate claim is "GND from
Brouwer; Brouwer for n = 2". Also, GND is stated for continuous *functions*. Debreu's lemma is for
uhc, nonempty, convex-valued correspondences, which is what is needed when demand is
not single-valued (for example linear preferences at p = (1,1)). Mathlib has no Kakutani theorem.

### 4. Equality feasibility in `Feasible` and `Blocks` (documented deviation, low severity)

`Feasible x := (∀ a, 0 ≤ x a) ∧ ∑ a, x a = ω̄` and `Blocks` likewise requires
`∑_{a∈S} y a = ∑_{a∈S} ω_a`. Allowing fewer competitor allocations makes `ParetoOptimal`
and `InCore` *weaker* than the MWG 15.B or Debreu (≤, free-disposal) notions. For monotone preferences the two
coincide. With a bad they do not. Example (test `badEcon_*`): one agent, two goods,
u = x₀ − x₁, ω = (1,1). Then p = (1,−1) with x = ω is a Lean `IsWalrasianEquilibrium` (LNS holds),
and x is Lean-`ParetoOptimal` (it is the only equality-feasible allocation), but disposing of the bad gives
(1,0) ≤ ω with u = 1 > 0. So the FWT conclusion here is relative to "no disposal" feasibility. This
is consistent with MWG ch. 16 (disposal through production sets), but should be documented. The
existence file switches to a ≤ notion (`IsFreeDisposalEquilibrium`), so the library uses two
inconsistent feasibility notions.

### 5. Berge: joint continuity on X × Y instead of on Gr Φ (documented deviation, minor)

`berge_maximum_theorem` assumes `Continuous (Function.uncurry f)` on all of X × Y. AB 17.31 only
needs continuity on the graph of Φ. This matters when applying the theorem to indirect utility on
the open set of positive prices, but it can be handled by restricting X to a subtype. The conclusion is complete.
`maxValue` uses `sSup` (junk value 0), but every theorem assumes nonempty compact values, so
the junk value never matters (test `maxValue_junk_empty` shows what happens without the guard).

### 6. Coverage gaps

- Existence of Walrasian equilibrium for standard economies (MWG 17.C.1 boundary-condition
  version; Arrow–Debreu with production, MWG 17.BB/Debreu ch. 5). Not stated.
- A production version of `second_welfare_theorem_demand` (cheaper point plus p ≥ 0 plus demand). Not stated.
- Core convergence / Debreu–Scarf (MWG 18.B.3) and core equivalence. Not stated. The file names
  do not claim them, but a "core" section is present.
- Kakutani / GND for correspondences. Not stated.
- Separating hyperplane for two disjoint convex sets (MWG M.G.2). Not stated as a standalone result.

### Items checked and found sound (non-obvious)
- `IsWalrasianEquilibrium.inCore` has **no** rationality or LNS hypotheses. This is still correct, because
  strict blocking plus x ∈ demand gives p·y_a > w_a for a ∈ S, and summing over S contradicts
  coalition feasibility.
- `first_welfare_theorem` with unrestricted-sign p is correct because feasibility is an equality, so p·Σx′ = p·ω̄
  without needing p ≥ 0.
- `exists_price_support` with `x ∉ interior C` (rather than x on the boundary) is the correct
  finite-dimensional statement, and holds for exterior points too.
- `cost_gt_of_cheaper_point` uses `ContinuousPref` relative to ℝⁿ₊ and z ≥ 0, which matches MWG 16.D.3.
- The welfare-theorem hypotheses are jointly satisfiable in nondegenerate examples (`asymEconomy`
  has a Walrasian equilibrium different from the endowment).
