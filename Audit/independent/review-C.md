# Statement review, Group C: Aggregation bridges and behavioral (RI / Logit / Ambiguity)

Scope: `Bridges/Aggregation/{Gorman,GrossSubstitutes,LawOfDemand,Examples}.lean`, `Behavioral/{RationalInattention,Logit,Ambiguity}.lean`.
References: MWG = Mas-Colell, Whinston and Green (1995); MM = Matějka and McKay (2015, AER); GS89 = Gilboa and Schmeidler (1989, JME).

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `AggregatesThroughWealth` | Gorman | MWG 4.B (aggregate demand depends only on Σwᵢ) | faithful with documented deviation | Fixed prices (no `p` argument). Wealth ranges over all of ℝ, including negative wealth. Demands are arbitrary functions: no budget, no utility, no consumption set. |
| `GormanForm` | Gorman | MWG 4.B, eq. after (4.B.1): xᵢ(p,wᵢ)=aᵢ(p)+wᵢb(p) | faithful with documented deviation | Demand-level parallel linear Engel curves at one fixed price. |
| `aggregatesThroughWealth_of_gorman` | Gorman | MWG 4.B (sufficiency) | faithful | |
| `gorman_of_aggregatesThroughWealth` | Gorman | MWG 4.B (necessity) | faithful with documented deviation | Uses continuity where MWG uses differentiability (weaker, fine). Needs `Nontrivial α`, which is correct. Quantifies over negative wealth. |
| `gorman_of_aggregatesThroughWealthNonneg` (+ `.transfer`, `.pair`) | Gorman | MWG 4.B | faithful | Nonnegative-wealth version. Correct by Cauchy's equation on ℝ≥0. |
| MWG Prop 4.B.1 itself (Gorman *indirect utility* form vᵢ=aᵢ(p)+b(p)wᵢ) | Gorman | MWG Prop 4.B.1 | WEAK (coverage gap) | The file is named "Gorman", but no indirect utility, preferences or price dependence appears. The headline Prop 4.B.1 (preferences ⇔ Gorman polar form) is not stated. |
| `PositivePrices`, `HomogeneousZero` | GrossSubstitutes | MWG 17.B | faithful | |
| `GrossSubstitutes` | GrossSubstitutes | MWG Def 17.F.2 | faithful | Strict, raises one price, positive prices only. Matches the textbook definition. |
| `GrossSubstitutes.add/.sum` | GrossSubstitutes | (aggregation of GS) | faithful | `.sum` correctly needs `s.Nonempty`. |
| `GrossSubstitutes.le_mixPrices`, `.lt_of_le` | GrossSubstitutes | MWG proof of 17.F.3 | faithful | |
| `GrossSubstitutes.unique_equilibrium` | GrossSubstitutes | MWG Prop 17.F.3 | faithful | Needs only GS and homogeneity, as in MWG. The one-good case is trivially true, which is also canonical. |
| GS ⇒ tâtonnement stability | GrossSubstitutes | MWG Prop 17.H.9 (Arrow–Block–Hurwicz) | WEAK (coverage gap) | The brief names "stability (MWG 17.F)", but no dynamics or stability statement exists. Existence of equilibrium is also not stated. |
| `WalrasLaw` | LawOfDemand | MWG 17.B.2(ii) | faithful | |
| `ExcessWARP` | LawOfDemand | MWG Def 17.F.1 | faithful | |
| `LawOfDemand` | LawOfDemand | MWG Def 4.C.1 (ULD) | VACUOUS-RISK | Faithful for a demand function at fixed wealth. On a cone of prices together with `WalrasLaw` and `HomogeneousZero`, it forces z ≡ 0 (proof below). That is exactly the excess-demand setting in which the file uses it. |
| `WeakLawOfDemand`, `LawOfDemand.weak` | LawOfDemand | MWG 4.C | faithful | |
| `LawOfDemand.sum` | LawOfDemand | MWG 4.C (aggregate ULD: sums of ULD demands are ULD) | faithful with documented deviation | Proof idea is correct, including the strictness bookkeeping and the empty `s` case. Wealth is implicit and fixed. |
| Prop 4.C.1 (homothetic ⇒ ULD), Hildenbrand Prop 4.C.2 | LawOfDemand | MWG 4.C.1–4.C.2 | WEAK (coverage gap) | No link from preferences to ULD. The "aggregate law of demand" is only additivity of an assumed property. |
| `LawOfDemand.excessWARP` | LawOfDemand | MWG 17.F (ULD-type monotonicity ⇒ WA) | VACUOUS-RISK | True as stated. On the positive orthant with homogeneity, its hypotheses only admit z ≡ 0. The repository never shows a non-degenerate instance: the only `LawOfDemand` example is z(p) = −p, which is not an excess demand. |
| `ExcessWARP.convex_equilibria` | LawOfDemand | MWG Prop 17.F.1 | faithful | Instantiated non-trivially by `zCD`. |
| `zCD` and its lemmas | Examples | MWG Ex. 17.F style | faithful with documented deviation | Named after Cobb–Douglas, but z is posited, not derived from an economy (it equals the excess demand of two consumers with CD(½,½) preferences and endowment (1,1)). The lemmas are correct (checked by hand: Walras, homogeneity, GS, WA, uniqueness at p ∝ (1,1)). |
| `lawOfDemand_neg` | Examples | – | WEAK | True, but z(p) = −p is not an excess demand (it fails Walras' law). It does not exercise `LawOfDemand.excessWARP`. |
| `xG`, `xG_gorman`, `xG_budget` | Examples | – | WEAK | xG 1 0 = (−1, 1/2): negative consumption. The example is not a demand from any consumer on ℝ₊². |
| `techY`, `prodEconomy*` and the welfare examples | Examples | MWG 16 | faithful | Checked by hand: equilibria, feasibility and profit maximisation hold, and `budgetSet` imposes x ≥ 0, so the linear utilities are bounded. |
| `objective`, `Z`, `generalizedLogit` | Logit | MM eq. (10); Gibbs | faithful with documented deviation | Uses the convention 0·log 0 = 0. When pᵢ > 0 = Pᵢ, the term −λ·pᵢ log(pᵢ/Pᵢ) is junk: it should be −∞. Every theorem that allows Pᵢ = 0 assumes `habs` (p ≪ P), so no theorem is affected. |
| `generalizedLogit_optimal`, `eq_generalizedLogit_of_optimal`, `objective_generalizedLogit` | Logit | Gibbs variational principle (Donsker–Varadhan, finite) | faithful | Holds for any positive (not necessarily normalised) P. λ > 0 is assumed. |
| `softmax_optimal` | Logit | Entropy-regularised choice = logit (Anderson–de Palma–Thisse 1992) | faithful | Existence, optimality and uniqueness are all stated. |
| `term_le`, `term_lt`, `log_generalizedLogit`, `Z_pos` etc. | Logit | – | faithful | |
| Random-utility logit (Gumbel shocks ⇒ logit, McFadden) | Logit | McFadden 1974 | WEAK (coverage gap) | The file name suggests it, but it is not stated. |
| `kl` | RationalInattention | KL divergence | faithful with documented deviation | When qᵢ = 0 < pᵢ the value is finite junk and can be negative (see test). Theorems guard against this with `hqpos`/`habs`. |
| `kl_nonneg`, `kl_eq_zero_iff`, `kl_nonneg0` | RationalInattention | Gibbs' inequality | faithful | |
| `IsRule`, `IsPrior`, `marginal`, `mutualInfo`, `avgKL` | RationalInattention | MM §2, eq. (4) | faithful with documented deviation | The prior has full support and Ω is finite. Mutual information has no junk, because p ≪ marginal automatically when g > 0. |
| `avgKL_eq`, `mutualInfo_le_avgKL`, `sum_objective_eq` | RationalInattention | standard identity I = min_Q E KL(p‖Q) | faithful | This is an algebraic identity, valid without hypotheses. |
| `riObjective`, `IsOptimalRule` | RationalInattention | MM Problem 1 | faithful | |
| `optimal_is_generalizedLogit` | RationalInattention | MM Theorem 1 | faithful with documented deviation | States only the necessary condition. Existence of an optimum and MM Corollary 1 (P⁰ maximises Σ_ω g log Σᵢ Pᵢ e^{vᵢ/λ}) are absent, as is the converse. |
| `optimal_is_softmax_of_uniform` | RationalInattention | MM Problem 2 / §4 (symmetric prior ⇒ multinomial logit) | WEAK | It *assumes* the unconditional choice probabilities are uniform. MM derive uniformity from an exchangeable prior, and that derivation is the economic step. |
| Gibbs0 section (`gl_*`, `term_*0`, `objective_le0`, `eq_gl_of_optimal0`) | RationalInattention | Gibbs principle with zero-mass actions | faithful | `habs` is necessary: without it the junk objective beats the Gibbs rule (see test). |
| `eu`, `meu` | Ambiguity | GS89 functional | faithful with documented deviation | C is a *finite* set of *arbitrary* vectors: there is no probability, convexity or closedness requirement. Finite suffices for linear eu via polytopes, but sets such as a disc of priors are not expressible. |
| `meu_le_eu`, `exists_eq_meu` | Ambiguity | – | faithful | |
| `meu_mono` | Ambiguity | GS89 monotonicity | faithful | Requires π ≥ 0. |
| `meu_mix_ge` | Ambiguity | GS89 uncertainty aversion (on utility acts) | faithful | |
| `meu_mix_const` | Ambiguity | GS89 C-independence | faithful | Holds for all α ≥ 0, which is more general. |
| Gilboa–Schmeidler representation theorem (axioms ⇔ maxmin) | Ambiguity | GS89 Theorem 1 | WEAK (coverage gap) | Only easy properties of the min functional on utility acts are stated. There are no preferences, no Anscombe–Aumann acts and neither direction of the representation theorem. |
| `ellsberg_not_seu` | Ambiguity | Ellsberg 1961 | faithful | Holds even without probability constraints on π (stronger). |
| `ellsbergPriors`, `ellsberg_meu` | Ambiguity | Ellsberg/GS89 | faithful | Checked by hand: meu(B)=0 < 1/3=meu(R), and meu(RY)=1/3 < 2/3=meu(BY). |

## Details on non-faithful items

### 1. `LawOfDemand` (and `LawOfDemand.excessWARP`): degenerate for homogeneous excess demand on a cone (VACUOUS-RISK)

Claim: suppose D = {p | PositivePrices p}, and z satisfies `LawOfDemand z D`, `WalrasLaw z D` and `HomogeneousZero z`. Then z p = 0 for every p ∈ D.

Proof:
1. Fix p′ ∈ D with z p′ ≠ 0. Since p′·z(p′) = 0 and p′ ≫ 0, z(p′) has a strictly negative coordinate i.
2. Choose p ∈ D with nearly all its weight on i. Then p·z(p′) < 0.
3. Case z p = z p′. Walras' law at p gives p·z(p) = 0, but p·z(p) = p·z(p′) < 0. Contradiction.
4. Case z p ≠ z p′. For every c > 0, homogeneity gives z(cp) = z(p) ≠ z(p′), and Walras' law gives (p′ − cp)·(z p′ − z p) = −p′·z(p) − c·p·z(p′). Since p·z(p′) < 0, this is positive for large c, which contradicts `LawOfDemand`.

The test file instantiates this concretely: `zCD` (the repository's own excess demand) violates `LawOfDemand` at p = (1,3), p′ = (1/10, 2/10). There (p′−p)·(z p′ − z p) = 9/10 − 28/60 > 0.

MWG define the uncompensated law of demand for x(p,w) at fixed w, which is not homogeneous in p alone. For excess demand, MWG use either WA (Def 17.F.1) or monotonicity relative to an equilibrium, p*·z(p) > 0 (17.H). Consequences:
- `LawOfDemand.excessWARP` has no non-degenerate instance on the positive orthant.
- On the price simplex it is non-degenerate. For example, with s = p₁/p₀, z = (s−1)/(1+s)·(s,−1) satisfies it. Nothing in the repository says so.

Suggested fix: restrict D to a normalisation slice (simplex or p₀ = 1) in the bridge theorem's documentation and examples. Alternatively, state the law of demand only for non-collinear p, p′, though the argument above also rules that out on cones. Provide a non-degenerate example.

### 2. Gorman: Prop 4.B.1 is not stated (coverage gap)
`GormanForm` and `AggregatesThroughWealth` concern a demand system x : α → ℝ → ι → ℝ at one implicit price vector. MWG Prop 4.B.1 is a statement about preferences: indirect utility vᵢ(p,wᵢ) = aᵢ(p) + b(p)wᵢ. That is not formalised.

The definitions also accept objects that are not demands:
- x ≡ 0 is in Gorman form with no budget identity.
- The repository's example `xG` has xG 1 0 = (−1, 1/2), which is negative consumption.

In the unrestricted variant, `AggregatesThroughWealth` quantifies over negative wealth. The `Nonneg` variant fixes this, and both directions are correct.

### 3. `optimal_is_softmax_of_uniform`: assumes the key step (WEAK)
The hypothesis `hunif : ∀ i, marginal g p i = c` is what MM derive from an a-priori symmetric prior. Once uniformity is assumed, the conclusion is algebra on `optimal_is_generalizedLogit`. A faithful version would take a prior invariant under permutations of ι and conclude that *some* optimal rule is multinomial logit. Under symmetry, uniqueness of P⁰ is not guaranteed in general, so the statement should be "there exists an optimal rule".

### 4. `optimal_is_generalizedLogit`: necessity only (documented deviation / coverage)
MM Theorem 1 is matched. Also missing:
- existence of an optimal rule;
- MM Corollary 1, the characterisation of P⁰ as the maximiser of Σ_ω g(ω) log Σᵢ Pᵢ e^{vᵢ(ω)/λ} over the simplex;
- the sufficiency direction: a generalized-logit rule whose P equals its own marginal need not be optimal, because a fixed point is not enough.

Corollary 1 is half of the paper's headline characterisation.

### 5. Junk values in `kl` and `Logit.objective` (documented deviation; guarded)
`kl ![1/2,1/2] ![1,0] = log(1/2) < 0`, because log 0 = 0 replaces +∞. Similarly, `objective 1 ![1,0] 0 ![1/2,1/2] = log 2`, which exceeds `objective` at the Gibbs rule (= 0). Every theorem carries `hqpos`, `hP`, or `habs`, so none is false. The definitions are still not textbook KL without those guards. In RI, mutual information is safe because p(·|ω) ≪ marginal when g > 0.

### 6. Ambiguity: representation theorem absent; priors unconstrained (WEAK / coverage)
`meu` accepts any finite set of vectors. For example, `meu {0}` is identically 0, and the mixture lemmas hold for it. The Gilboa–Schmeidler theorem (preference axioms ⇔ ∃ closed convex C of probabilities with ≽ represented by min_{π∈C} E_π u(f)) is not stated in either direction. Only properties of the functional are proved: monotonicity, concavity and C-independence. Acts are already utility vectors, so there is no Anscombe–Aumann lottery structure.

### 7. Gross substitutes: stability not covered (coverage gap)
MWG 17.F.3 (uniqueness) is faithfully stated. Not stated:
- the global stability of tâtonnement under GS (MWG Prop 17.H.9);
- that GS + Walras imply ∂zₗ/∂pₗ < 0, and that the equilibrium is regular;
- existence.

### 8. Examples: `lawOfDemand_neg`, `xG` (WEAK illustrations)
- z(p) = −p satisfies `LawOfDemand` but is not an excess demand: p·z(p) = −|p|² ≠ 0.
- `xG` is not a demand on ℝ₊².

Neither example exercises the economic content of the bridge theorems. `zCD` is a good example for GS and WA but fails `LawOfDemand` (item 1).
