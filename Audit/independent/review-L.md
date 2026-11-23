# Statement review (reviewer L): GE existence, cooperative games, social choice, partial equilibrium

Scope: `GE/ExistencePreferences.lean` (with `GE/ExistenceInterior.lean` as context), `Cooperative/Core.lean`, `Cooperative/Shapley.lean`, `SocialChoice/May.lean`, `SocialChoice/MedianVoter.lean`, `Partial/{Monopoly,Oligopoly,Salop,PublicGoods,Externalities,DiamondParadox}.lean`.
I read definitions from `GE/Exchange.lean`, `GE/Existence.lean`, `Consumer/{Demand,Budget,Continuity}.lean`, `Preferences/{Basic,Utility}.lean`, `Games/Strategic.lean` and `Bridges/Aggregation/GrossSubstitutes.lean` (only for `PositivePrices`) for context.

Overall: these targets are in much better shape than the ones prior reviews flagged. I found no false or vacuous headline. Every headline was checked by hand against a nondegenerate instance. The real issues are about scope (Cobb–Douglas is not covered, symmetric-only equilibria, domain-of-ℝ hypotheses) and a couple of conclusions that are weaker than the canonical ones.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `exists_walrasianEquilibrium_of_preferences` | GE/ExistencePreferences | MWG Prop 17.B.2 + 17.C.1 | faithful with documented deviation / WEAK (coverage) | Hypotheses are about the economy (u continuous, strictly quasiconcave on ℝ₊ⁿ, strongly monotone, Σω ≫ 0). They are not assumed properties of z. But (a) it adds `hωa : ∀ a, endow a ≠ 0`, which MWG does not need; (b) preferences must come from a utility that is continuous on all of ℝⁿ; (c) like MWG, it does **not** cover Cobb–Douglas (fails both strong monotonicity and strict quasiconcavity on the boundary), and no Cobb–Douglas existence result is stated anywhere |
| `boundaryCondition_excessDemand` | GE/ExistencePreferences | MWG 17.B.2(v) | faithful | Holds for any demand selection; uses only continuity, strong monotonicity and Σω ≫ 0, as in MWG |
| `wealth_pos` | GE/ExistencePreferences | — | faithful | Helper lemma |
| `uSqrt`, `continuous_uSqrt`, `strictlyQuasiconcave_uSqrt`, `stronglyMonotone_uSqrt`, `sqrtEconomy_exists_equilibrium` | GE/ExistencePreferences | — | faithful | Gives a nondegenerate witness that the headline's hypotheses can all hold together (√ is continuous on ℝ, strictly concave on ℝ₊, so the sum is strictly quasiconcave on ℝ₊²) |
| `BoundaryCondition`, `ExcessBoundedBelow` | GE/ExistenceInterior | MWG 17.B.2(iv),(v) | faithful | max_l z_l(pⁿ) → ∞, and bounded below on p ≫ 0 |
| `exists_equilibrium_of_boundaryCondition` | GE/ExistenceInterior | MWG 17.C.1 | faithful (slightly more general) | Drops homogeneity of degree 0, which the simplex proof does not need |
| `exists_walrasianEquilibrium_of_boundaryCondition` | GE/ExistenceInterior | MWG 17.C.1 | faithful (intermediate) | Assumes properties of z, but that is fine for an intermediate result; the headline discharges them |
| `IsInCore`, `IsBalancedFamily`, `IsBalanced` | Cooperative/Core | O–R Def 258.1, 262.1 | faithful with documented deviation | ∅ is included as a coalition. The core then forces v ∅ ≤ 0, and the weight on ∅ is unconstrained, so balancedness also forces v ∅ ≤ 0. The two sides stay consistent, so the iff is unaffected |
| `bondareva_shapley` | Cooperative/Core | Bondareva 1963 / Shapley 1967; O–R Prop 262.1 | faithful | Full iff |
| `shapley`, `IsShapleyAxioms` | Cooperative/Shapley | Shapley 1953; O–R §14.4 | faithful | Random-order formula. Efficiency is stated as v N − v ∅, a harmless generalisation of v ∅ = 0. Axioms: symmetry, null player, additivity |
| `shapley_axioms`, `IsShapleyAxioms.unique`, `eq_shapley_of_axioms` | Cooperative/Shapley | O–R Prop 293.1 | faithful | Existence and uniqueness both stated, through the unanimity basis including T = ∅ (the constant game); I checked that this is consistent |
| `may_theorem` | SocialChoice/May | May 1952; MWG Prop 21.C.1 | faithful | Iff. F's codomain is ℤ, not {−1,0,1}, but the axioms force F = sign Σα on profiles, so nothing is lost |
| `SinglePeaked` | SocialChoice/MedianVoter | MWG Def 21.D.3 | faithful | Same-side strict monotonicity, as in MWG |
| `IsMedianPeak`, `median_condorcet`, `exists_median` | SocialChoice/MedianVoter | MWG Prop 21.D.2 / Cor (odd I); Black 1948 | faithful | For an odd number of voters the median peak is a strict Condorcet winner |
| `median_not_defeated` | SocialChoice/MedianVoter | MWG Prop 21.D.2 | WEAK | 2nd conjunct #{y ≻ m} ≤ #{m ≿ y} counts indifferent voters on m's side. The canonical (and provable) statement is #{y ≻ m} ≤ #{m ≻ y} |
| (coverage) | SocialChoice/MedianVoter | MWG Prop 21.D.4 | gap | Transitivity of pairwise majority under single-peakedness (odd I) is not stated |
| `monopoly_foc`, `lerner_rule`, `monopoly_price_gt_mc` | Partial/Monopoly | MWG 12.B; Tirole 1.1 | faithful | `lerner_rule` with P′ = 0 holds through x/0 = 0 junk on both sides, but this is consistent (P = C′ then) |
| `monopoly_output_lt`, `monopoly_optimum_lt_competitive` | Partial/Monopoly | MWG 12.B | faithful (generalised) | `MC` is tied to C′ only at qₘ, which makes the statement more general, not less |
| `linear_monopoly`, `linearSurplus_eq` | Partial/Monopoly | Tirole 1.1 | faithful | I checked qₘ = (a−c)/2b, p = (a+c)/2 and DWL = (a−c)²/8b |
| `discrimination_price_le`, `third_degree_discrimination` | Partial/Monopoly | Tirole 3.2 | faithful | Interior joint optimum; the hypothesis ε > 1 rules out the P′ = 0 junk |
| `bertrand_isNash_iff` | Partial/Oligopoly | Tirole 5.1; MWG 12.C.1 | faithful | Unique NE (c,c); I checked the asymmetric cases by hand |
| `cournot_isEq_iff`, `cournot_price`, `cournot_price_tendsto` | Partial/Oligopoly | Tirole 5.4; MWG 12.C | faithful | Uniqueness holds: with k active firms an inactive firm always wants to enter |
| `stackelberg_leader_optimal` | Partial/Oligopoly | Tirole 8.2 | faithful with minor WEAK | The last conjunct compares with the literal (a−c)²/(9b) and is never linked to `cournotQ`/`cournotProfit` |
| `salop_equilibrium`, `salop_free_entry`, `salop_social_optimum`, `salop_excess_entry` | Partial/Salop | Salop 1979; Tirole 7.1.2 | faithful with documented deviation | Symmetric equilibrium only; n is real-valued; `salopLocalDemand` is valid on the relevant range q ≥ c (checked) |
| `samuelson_condition`, `samuelson_sufficient`, `lindahl_efficient` | Partial/PublicGoods | MWG 11.C | faithful | |
| `voluntary_underprovision` | Partial/PublicGoods | MWG 11.C; Bergstrom–Blume–Varian (1986) | WEAK (domain) | Requires every φᵢ to be differentiable on **all of ℝ** with a positive, strictly decreasing derivative. This excludes the textbook √G and log G (and log(1+G)), even though only G ≥ 0 matters |
| `IsParetoExt`, `coase_pareto_iff`, `coase_theorem` | Partial/Externalities | MWG 11.D; Coase 1960 | faithful with documented deviation | Efficiency/invariance version (quasilinear TU). No bargaining protocol is modelled; invariance is stated for total surplus, not for the level h |
| `pigou_tax` | Partial/Externalities | MWG 11.D (Pigouvian tax t = −φ₂′(h°)) | faithful | |
| `IsPartialEq`, `competitive_maximizes_surplus` | Partial/Externalities | MWG 10.D (FWT, partial eq.) | faithful | |
| `diamond_paradox` | Partial/DiamondParadox | Diamond 1971 | WEAK / documented deviation | Only checks symmetric profiles (all others charge p), and consumer search behaviour is hard-coded as "buy iff q ≤ min(u, p+s)". The canonical result (every equilibrium has all firms at the monopoly price) is not stated |

## Details on non-faithful items

### 1. `exists_walrasianEquilibrium_of_preferences`: Cobb–Douglas is not covered (coverage / WEAK)
The brief asked whether the hypotheses are met by Cobb–Douglas and whether they concern the economy rather than excess demand.
- **Economy vs. excess demand.** All hypotheses concern primitives: `hpref`, `hu`, `hsq`, `hmono`, `hω`, `hωa`. Nothing about `z` is assumed; `boundaryCondition_excessDemand` derives the boundary condition. Good.
- **Cobb–Douglas fails.** Take u(x) = √(x₀x₁) (or x₀^a x₁^(1−a) via `rpow`, which is in fact continuous on all of ℝ² for 0 < a < 1).
  - `StronglyMonotone (prefOf u)` fails: x = 0 ≤ y = (1,0) and x ≠ y, yet u x = u y = 0.
  - `StrictlyQuasiconcave u` fails: x = (0,1), y = (0,2) and t = ½ give min(0,0) = 0 = u(0, 3/2).

  This matches MWG, where 17.B.2 likewise needs strong monotonicity and Cobb–Douglas is handled only in remarks and examples. Even so, the most-used textbook utility has no existence theorem in this file. The weaker canonical condition "boundary-indifference: anything ≫ 0 is preferred to anything on the boundary" (or monotone + strictly positive demand) is missing. The only example, `sqrtEconomy`, uses Σ√xᵢ.
  See `sanity_tests.lean` §1.
- **Extra hypothesis `hωa : ∀ a, E.endow a ≠ 0`.** MWG 17.B.2 assumes only Σω ≫ 0. A consumer with ω = 0 has budget set {0} at p ≫ 0, so their demand {0} is perfectly well behaved. The theorem therefore excludes economies (e.g. endowments ((3,3),(0,0))) for which the canonical result applies. This is minor and harmless for soundness.
- **`Continuous (u a)` on all of ℝⁿ** is stronger than continuity on ℝ₊ⁿ. A piecewise-defined utility (`if 0 ≤ x then … else 0`) would need to be rewritten. Tietze makes this harmless in principle, but it is the same pattern prior reviews flagged. Also, "of_preferences" actually assumes a utility representation, not just a continuous preference relation (Debreu's theorem is not invoked). Both are documented deviations.

### 2. `median_not_defeated`: conclusion weaker than canonical (WEAK)
The second conjunct is `#{i | u i m < u i y} ≤ #{i | u i y ≤ u i m}`. The right-hand side includes voters indifferent between m and y. MWG Prop 21.D.2 says m is not defeated under pairwise majority, i.e. `#{y ≻ m} ≤ #{m ≻ y}`. That is provable under the stated hypotheses: if y > m, everyone with peak ≤ m (at least n/2 of them) strictly prefers m, and only voters with peak > m (at most n/2) can strictly prefer y. The first conjunct (`2·#{y ≻ m} ≤ n`) does not imply the strict-vs-strict form either. Stronger statement given as a `sorry` example in §4.

### 3. `voluntary_underprovision`: hypotheses on all of ℝ (WEAK, domain)
`hd : ∀ i x, HasDerivAt (φ i) (d i x) x`, `hpos : ∀ i x, 0 < d i x`, `hanti : StrictAnti (d i)` quantify over every real x. Real.sqrt is not differentiable at 0. Real.log and `log (1+·)` have negative derivative left of their singularity (Mathlib's log is log|x|), so `hpos` fails. Only exponential-type utilities such as −e^{−G} qualify. The canonical result needs these properties only on [0, ∞) (really only on [0, max(G, G*)]). §3 proves that φ(G) = log(1+G) violates the hypotheses. This is the same kind of issue as the known Σ√xᵢ finding.

### 4. `diamond_paradox`: symmetric-only, reduced form (WEAK / documented deviation)
`IsSearchEq n c u s p` asks whether a firm can profitably deviate when all others charge p. Consumer behaviour is not derived; it is fixed as "buy iff q ≤ u ∧ q ≤ p + s". So the theorem says the unique *symmetric* equilibrium price is u. Diamond's paradox says every equilibrium, including asymmetric ones and with consumers' optimal sequential search, has all firms charging the monopoly price. The iff itself is correct: I checked p > u (deviate to u), p < u (deviate to min(u, p+s)) and p = u.

### 5. `stackelberg_leader_optimal`: disconnected comparison (minor)
The conjunct `(a−c)²/(9b) < (a−c)²/(8b)` is pure arithmetic. Nothing in the file proves that (a−c)²/(9b) is the Cournot duopoly profit `cournotProfit a b c i (fun _ => cournotQ a b c 2)` for `I = Fin 2`. The link is given in §5 (`sorry`).

### 6. `Cooperative/Core`: ∅ as a coalition (documented deviation, not an error)
`IsInCore` quantifies over all `S`, including ∅, so it requires `v ∅ ≤ 0`. `IsBalancedFamily` puts no constraint on `w ∅` beyond `0 ≤ w ∅`, so `IsBalanced` also forces `v ∅ ≤ 0`. Both sides of `bondareva_shapley` thus fail together when `v ∅ > 0` and agree otherwise. The iff is correct for all TU games, not only those with v ∅ = 0. §6 has the sanity example.

### Items checked and judged faithful (short notes)
- `may_theorem`: proved informally that A+N+PR force F = majority on profiles, even with codomain ℤ (balanced profile ⇒ F = 0 by A+N; PR lifts it to ±1). The empty electorate case is consistent.
- `IsShapleyAxioms.unique`: the constant game makes every player null, which matches efficiency v N − v ∅ = 0. `apply_unanimity` at T = ∅ gives 0 on both sides. Consistent.
- `bertrand_isNash_iff`: the strategy space is all of ℝ (negative prices allowed). Since x ≥ 0 and is antitone with x(c) > 0, every p ≠ (c,c) has a profitable deviation. True.
- `cournot_isEq_iff`: inverse demand a − bQ is not truncated at 0, but corner equilibria are still impossible (k active firms leave positive margin for an entrant). Unique.
- `salop_equilibrium`: for q < c the profit is ≤ 0; for q ≥ c the profit is r(2/n − r/t) with r = q − c, maximised at r = t/n with value t/n². True.
- `pigou_tax`: interior FOC gives φ₁′ = −φ₂′. Concavity of φ₁ − t·h then gives the global max on ℝ₊.
