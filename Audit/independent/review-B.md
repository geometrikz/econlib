# Statement review B: Uncertainty and Producer

Scope: `Uncertainty/{VNM,Pratt,RiskAversion,StochasticDominance,MoneyLottery}.lean` and `Producer/{Production,Cost,Aggregation}.lean`. I read only the statement files under `/home/user/rv/in/` (proofs replaced by `sorry`, comments removed). Lean was not run, so every Lean/Mathlib claim below comes from reasoning about the semantics.

Overall: the Uncertainty block is mostly faithful. VNM in both directions, uniqueness up to positive affine transformations, FOSD, risk aversion ⟺ concavity, and Pratt are all stated correctly, and the hypotheses can be satisfied by non-trivial examples, several of them already in the files. The main problems are:
- Rothschild–Stiglitz has only its easy direction.
- Hotelling and Shephard (cost) are the "differentiability assumed" envelope versions, not MWG's "single-valued ⇒ differentiable" form.
- Every Arrow–Pratt/Pratt result is stated on all of ℝ with u′ > 0 everywhere, which excludes log, √ and CRRA.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `mix`, `lotteries`, `expectedUtility`, `degenerate` | VNM | MWG 6.B.1–6.B.3 | faithful | Simplex over finite `C`; EU is linear. |
| `VNMAxioms` | VNM | MWG Def 6.B.3, 6.B.4 | faithful | Rationality on the subtype; continuity uses closed α-sets (MWG form); independence holds for α∈(0,1) as an iff. |
| `HasEURepresentation` | VNM | MWG Def 6.B.5 | faithful | Stated only on lotteries. |
| `vnmAxioms_of_eu`, `exists_eu_of_vnmAxioms`, `vnm_theorem` | VNM | MWG Prop 6.B.2/6.B.3; Kreps ch. 5 | faithful | Both directions. The file's example shows the axioms admit a non-trivial strict preference. |
| `HasEURepresentation.affine`, `.unique` | VNM | MWG Prop 6.B.2 | faithful | Uniqueness up to `a>0`, `b`. Edge cases (empty `C`, total indifference) are harmless. |
| VNM helper lemmas (`indep_strict`, `strict_mix`, `le_mix`, …) | VNM | MWG proof of 6.B.3 | faithful | Internal steps. |
| `SimpleLottery`, `expect`, `mean`, `cdf` | MoneyLottery | MWG 6.C (finite support) | faithful with documented deviation | Finitely supported only, so no general distributions. Outcomes range over all of ℝ, including negatives. `cdf` is right-continuous. |
| `twoPoint`, `pure`, `integral` lemmas | MoneyLottery | — | faithful | Algebraic bookkeeping. |
| `RiskAverseOn`, `riskAverseOn_iff_concaveOn` | RiskAversion | MWG Def 6.C.1, Prop 6.C.1(i)⇔(ii); Gollier ch. 2 | faithful | Interval version with `Convex I` is correct, with weak inequality matching MWG's "weakly risk averse". |
| `exists_certaintyEquivalent`, `riskAverse_iff_certaintyEquivalent_le_mean` | RiskAversion | MWG 6.C.1(iii) | faithful with documented deviation | Requires u continuous and strictly monotone on all of ℝ, so √/log/CRRA are not admissible (see B3). |
| `MoreRiskAverse`, `moreRiskAverse_iff` | RiskAversion | MWG Prop 6.C.2 (i)⇔(ii)⇔(iii) | faithful with documented deviation | CE comparison ⟺ u₂ = ψ∘u₁ with ψ concave and increasing on `range u₁`. Domain is ℝ only. |
| `arrowPratt`, `riskAverse_iff_arrowPratt_nonneg` | RiskAversion | MWG 6.C.1 / Arrow–Pratt | WEAK (domain) | Needs u twice differentiable on ℝ with u′>0 everywhere. `Real.log` fails this (its `deriv` at 0 is 0, and it is negative on ℝ₋). No `RiskAverseOn I` version for intervals. |
| `marginalRatio`, `relSlope`, `exists_relSlope_eq`, `tendsto_relSlope` | Pratt | Pratt (1964) proof steps | faithful | Division-by-zero junk is avoided because u₁ is strictly monotone (`hp₁`). |
| `arrowPratt_le_iff_antitone_marginalRatio` | Pratt | Pratt (1964) | faithful | (u₂′/u₁′)′ = (u₂′/u₁′)(r₁−r₂). Direction is correct. |
| `arrowPratt_le_iff_moreRiskAverse` | Pratt | MWG Prop 6.C.2 / Pratt Thm 1 | faithful with documented deviation (domain) + partial coverage | Direction is correct (r₁ ≤ r₂ ⟺ u₂ more risk averse) and the CARA example is non-degenerate. Only on ℝ with u′>0 globally. The risk-premium and probability-premium equivalences in Pratt's Thm 1 are missing. |
| `FOSD`, `fosd_iff_cdf_le` | StochDom | MWG Def 6.D.1, Prop 6.D.1 | faithful | Defined with all nondecreasing u (non-measurable ones are fine with finite support). Both directions stated. |
| `SOSD` | StochDom | MWG Def 6.D.2 | faithful | Equal mean plus nondecreasing concave u. With equal means this is equivalent to RS's "all concave u". |
| `IsMeanPreservingSpread`, `expect_of_compound` | StochDom | MWG 6.D, RS (1970) | faithful | A compound lottery with mean-x conditional lotteries is the standard construction. |
| `expect_le_of_meanPreservingSpread`, `sosd_of_meanPreservingSpread` | StochDom | MWG Prop 6.D.2 (⇐), RS (1970) | WEAK (one direction) | Only MPS ⇒ SOSD. The converse SOSD ⇒ MPS, which is the content of Rothschild–Stiglitz, is not stated (B1). |
| `SOSD.shortfall_le`, `expect_shortfall_eq_integral_cdf` | StochDom | MWG Ex 6.D.4 / RS (1970) integral condition | WEAK (one direction) | Only SOSD ⇒ ∫F ≤ ∫G. Integral condition + equal mean ⇒ SOSD is missing. |
| `PossibilityOfInaction` … `Additive` | Production | MWG 5.B (a)–(h) | faithful | NFL is `Y∩ℝ₊ ⊆ {0}`, irreversibility is `Y∩−Y ⊆ {0}`, and the returns definitions match. |
| `NonincreasingReturns.of_convex`, `constantReturns_iff` | Production | MWG 5.B | faithful | |
| `Additive.nsmul_mem` | Production | — | MISMATCH (ill-formed file) | The text is a full term-mode proof followed by a stray `:= by sorry`, so the statement file will not parse (B6). |
| `Additive.constantReturns_and_convex` | Production | MWG Ex 5.B.4 (iff) | WEAK (one direction) | Only additive ∧ NIRS ⇒ convex cone. The converse is missing (trivial but absent). |
| `profit`, `supply`, `profitDomain` | Production | MWG Def 5.C | faithful with documented deviation | `profit` is `sSup`, so it is 0 (junk) when unbounded, where MWG has +∞. The theorems mostly carry `BddAbove`/`profitDomain` guards (B5). |
| `profit_nonneg`, `cost_le_profit`, `profit_eq`, `mem_supply` | Production | MWG 5.C | faithful | Boundedness hypotheses present. |
| `profit_smul`, `supply_smul` | Production | MWG Prop 5.C.1(i),(ii) | faithful (true partly by junk) | When unbounded, both sides are junk 0. Harmless. |
| `convexOn_profit`, `convex_supply`, `law_of_supply` | Production | MWG 5.C.1(iii),(v), (5.C.2) | faithful | |
| `hotelling`, `hotelling_partial`, `supply_subsingleton` | Production | MWG Prop 5.C.1(vi) | WEAK | Assumes `HasFDerivAt (profit Y)` and gets ∇π = y (envelope form). MWG proves differentiability from single-valued y(p). Hessian symmetry/PSD (5.C.1(vii)) is missing (B2). |
| `berge_supply` | Production | Berge / MWG M.K | faithful | Compact Y is stronger than textbook production sets, which is acceptable for a Berge instance. |
| `costFunction`, `factorDemand`, `mem_factorDemand` | Cost | MWG Def 5.C (c(w,q), z(w,q)) | faithful with documented deviation | `sInf`, so infeasible q gives junk c = 0 (MWG: +∞). Inputs are restricted to z ≥ 0 (correct). |
| `costFunction_smul`, `factorDemand_smul` | Cost | MWG Prop 5.C.2(i),(ii) | faithful | |
| `concaveOn_costFunction`, `costFunction_concave` | Cost | MWG 5.C.2(iii) | faithful | Feasibility hypothesis is present. Without it c ≡ 0 is concave anyway. |
| `shephard_cost` | Cost | MWG 5.C.2(vi) | WEAK | Same pattern as Hotelling: differentiability assumed, not derived. Negative semidefinite Hessian missing. |
| `costFunction_mono` | Cost | MWG 5.C.2 (nondecreasing in q) | faithful | Needs feasibility at q′, because junk 0 would otherwise break it. |
| `costFunction_crs` | Cost | MWG 5.C.2(viii)-style (c(w,q)=q c(w,1) under CRS) | faithful | Holds even in junk cases. |
| `factorDemand_of_profitMax` | Cost | MWG 5.C (two-stage) | faithful | |
| `aggregate`, `supply_aggregate`, `sum_mem_supply_aggregate`, `mem_supply_of_sum_mem_supply_aggregate` | Aggregation | MWG Prop 5.E.1 | faithful | Both directions of y*(p)=Σyⱼ(p). An empty `J` gives `{0}`, which is correct. |
| `profit_aggregate`, `profit_aggregate_of_supply` | Aggregation | MWG Prop 5.E.1 | faithful | Has the nonempty + `BddAbove` guards needed against the junk value (without them it would be false). |
| `Efficient`, `efficient_of_mem_supply` | Aggregation | MWG Def 5.F.1, Prop 5.F.1 | faithful | |
| `exists_price_of_efficient` | Aggregation | MWG Prop 5.F.2 | faithful | Convex Y, p ≥ 0, p ≠ 0. `Nonempty ι` is needed and present. |

## Details on non-faithful items

### B1. Rothschild–Stiglitz: only the easy direction (StochasticDominance.lean): WEAK / coverage gap
The canonical theorem (Rothschild–Stiglitz 1970; MWG Prop 6.D.2; Gollier ch. 3) says that for equal-mean F, G the following are equivalent:
- (i) G SOSD-dominated by F (all concave u)
- (ii) G is an MPS of F
- (iii) ∫_{−∞}^t G ≥ ∫_{−∞}^t F for all t

The file states only (ii)⇒(i) (`sosd_of_meanPreservingSpread`) and (i)⇒(iii) (`SOSD.shortfall_le` with `expect_shortfall_eq_integral_cdf`). The hard directions are missing: (i)⇒(ii) is the RS construction, and (iii)⇒(i) needs integration by parts or approximating concave u by shortfall functions. A reader who sees `IsMeanPreservingSpread` and `SOSD` side by side would assume the characterization is proved, and it is not. See `sanity_tests.lean`, which states the missing directions as `sorry` targets. For finite support, (iii)⇒(i) is true and (i)⇒(ii) is true (finite MPS chain), so these are provable statements.

### B2. Hotelling's lemma (Production.lean `hotelling`, `hotelling_partial`): WEAK
MWG Prop 5.C.1(vi) says: if y(p̄) is a single point, then π is differentiable at p̄ and ∇π(p̄)=y(p̄). The Lean version assumes `HasFDerivAt (profit Y) P' p` plus `profitDomain` near p, and concludes P'=y. That is the envelope "if differentiable, then the derivative is supply" half. It is useful but assumes what the textbook proves. `supply_subsingleton` is the converse-flavoured fact (differentiable ⇒ single-valued), which runs opposite to MWG.

Also missing: 5.C.1(vii), that the Jacobian Dy(p) = D²π(p) is symmetric PSD with Dy(p)p=0. Neither theorem can be falsified by trivial objects: an empty Y makes `hy` impossible, and the file's `Iic ybar` example is non-degenerate.

### B3. Arrow–Pratt and Pratt only on ℝ with u′>0 everywhere (RiskAversion.lean, Pratt.lean): WEAK (domain)
`riskAverse_iff_arrowPratt_nonneg`, `arrowPratt_le_iff_*`, `riskAverse_iff_certaintyEquivalent_le_mean` and `moreRiskAverse_iff` all quantify u over ℝ, with `Continuous`/`StrictMono`/`∀ x, 0 < deriv u x` on all of ℝ. The standard textbook comparisons (log vs √, CRRA family, MWG Ex 6.C.*) live on ℝ₊₊ and cannot be instantiated:
- `deriv Real.log 0 = 0`, and `deriv Real.log x < 0` for x<0.
- `Real.sqrt` is 0 on ℝ₋, so it is not concave on ℝ, and `¬ RiskAverseOn Real.sqrt univ` (witness: ½δ₋₁+½δ₁ has E√ = ½ > √0 = 0).

Only `riskAverseOn_iff_concaveOn` has an interval version. Only CARA-type utilities (as in the file's examples) qualify. This is the same "ℝⁿ instead of the consumption set" problem seen in earlier reviews.

### B4. Pratt's theorem partially covered (Pratt.lean): coverage gap
Pratt (1964) Thm 1 / MWG 6.C.2 list r₁ ≤ r₂, ψ concave, CE comparison, risk premium π₂ ≥ π₁, probability premium, and "u₂ accepts ⇒ u₁ accepts". The file covers the first three (via `moreRiskAverse_iff` and `arrowPratt_le_iff_moreRiskAverse`). Risk and probability premia, and DARA/relative risk aversion (MWG 6.C.3–6.C.4), are absent.

### B5. Junk values in `profit` and `costFunction` (Production.lean, Cost.lean): documented deviation, theorems guarded
- `profit Y p = sSup(...)` is 0 when p·y is unbounded on Y (MWG: +∞) and 0 for empty Y.
- `costFunction f w q = sInf(...)` is 0 when q is infeasible (MWG: +∞), and 0 for w with a negative entry whenever the image is unbounded below.

I checked each theorem. `profit_nonneg`, `cost_le_profit`, `convexOn_profit`, `hotelling`, `profit_aggregate` and `costFunction_mono` carry the needed guards. `profit_smul`, `costFunction_smul` and `costFunction_crs` are partly true by junk (0 = α·0), which is harmless. Without its `BddAbove` guard, `profit_aggregate` would be false: one unbounded Yⱼ makes both π_agg and πⱼ junk 0, while the other πₖ>0. The guard is present.

### B6. `Additive.nsmul_mem` is ill-formed (Production.lean): MISMATCH (file integrity)
The statement file contains a full structural-recursion proof followed by `:= by\n  sorry`. This will not parse, so `import EconLean` would fail on this file. It is probably a stripping artifact, but the statement file as given does not elaborate. The mathematical content ((n+1)•y ∈ Y for additive Y) is fine.

### B7. `Additive.constantReturns_and_convex` (Production.lean): WEAK, one direction
MWG Ex 5.B.4 says Y is a convex cone ⟺ Y is additive with NIRS. Only ⇒ is stated. Trivial gap.

### B8. Coverage gaps (Producer)
These are missing from the Producer files:
- Duality: Y closed, convex, free disposal ⇒ Y = {y : p·y ≤ π(p) ∀p≫0} (MWG 5.C, Prop 5.C.1 discussion; 5.G).
- Symmetric PSD supply substitution matrix.
- Symmetric NSD factor-demand substitution matrix.
- Convexity of z(w,q) when f is quasiconcave.
- c convex in q when f is concave.
- Le Chatelier.
- Single-output supply from the cost function (p = MC).

The headline "Shephard for cost" is the envelope form only (B2 pattern).

## Things I checked and believe are fine
- VNM continuity and independence match MWG exactly. The `Rational` instance is on the subtype of lotteries, not on all of `C → ℝ`, so the axioms do not demand anything off the simplex. Uniqueness holds even for constant u (choose a=1). Empty `C` makes everything vacuous but consistent.
- `fosd_iff_cdf_le` is a true iff for finitely supported lotteries. `Monotone u` without measurability is fine.
- `SOSD` with "monotone ∧ concave" vs RS's "concave": with equal means these are equivalent (on the convex hull of the supports, subtract the slope at the right end and flatten beyond it).
- `moreRiskAverse_iff` has the correct direction and domain (`range u₁`, which is an interval because u₁ is continuous).
- `arrowPratt_le_iff_antitone_marginalRatio` does not need `hd₁`, since `0 < deriv u₁ x` forces differentiability.
- `exists_price_of_efficient` is true via separation of Y from y+ℝ₊₊ⁿ.
