# Statement review: Games/ (all files) and the SOSD converse in Uncertainty/StochasticDominance.lean

Scope: only the files under `/home/user/review/games_in`. Statements and definitions only; proofs are `sorry`.
I checked each sorried statement by hand for truth. **No statement looks false.** The problems are
(a) one definition that is more general than the textbook concept and can be made vacuous (`IsBNE` and its prior),
(b) several results that are weaker than the textbook results their names suggest (pure-strategy ISD, `IsDominant`, `zermelo`), and
(c) coverage gaps (the MPS converse, the rationalizability/ISD equivalence, chance nodes, the zero-sum/Nash link).

Verdict key: OK = faithful; WEAK = true but weaker or narrower than the textbook; MISMATCH = the name or definition differs from the cited concept;
VACUOUS-RISK = it can be satisfied trivially in degenerate inputs; SUSPICIOUS = it may be false.

## Summary table

### Games/Strategic.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `IsBestResponse` | MWG 8.D (pure best response) | OK | `update s i t'` is the correct deviation by i alone |
| `IsNash` | MWG Def 8.D.1 (pure) | OK | standard; with an empty player set every profile is Nash, which is correct |
| `isNash_iff_bestResponse` | MWG 8.D | OK | uses `update s i (s i) = s` |
| `IsDominant` | MWG Def 8.B.4 / 8.B.5 | MISMATCH | only asks for weak inequality and no strict case, so it is neither MWG's "strictly dominant" nor "weakly dominant"; it is satisfied trivially when payoffs do not depend on own action (see F3) |
| `isNash_of_dominant` | MWG 8.B (dominant-strategy eq. is Nash) | OK | true, and stronger because the hypothesis is weaker |
| `StrictlyDominated` | MWG Def 8.B.3 (domination by a pure strategy) | WEAK / VACUOUS-RISK | pure dominators only (MWG 8.D uses mixed dominators); vacuously true when an opponent's set `R j` is empty (F2, F7) |
| `isdStep`, `isd` | MWG 8.B iterated deletion of strictly dominated strategies | WEAK | simultaneous, maximal deletion, and the dominator must survive: matches MWG 8.B, but not the mixed-domination version of 8.D |
| `isd_succ_subset`, `isd_antitone` | — (structural) | OK | |
| `isNash_mem_isd` | MWG 8.D (Nash strategies survive ISD) | OK | |
| `isNash_of_isd_singleton` | MWG 8.B (dominance solvable implies Nash) | OK | `Fintype (S i)` is needed and is assumed (with infinite S, a same-round chain of dominators can run forever); uniqueness follows from `isNash_mem_isd` |
| `pdPayoff` + example | MWG Ex. 8.B.1 (Prisoner's Dilemma) | OK | `true` = confess; payoffs are correct |

### Games/Mixed.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `profileProb`, `mixedPayoff` | MWG 8.D (independent mixing) | OK | junk values for non-lotteries, but they are only used under `IsMixedProfile` |
| `IsMixedProfile` | MWG 8.D | OK | every `σ i ∈ lotteries` |
| `IsMixedNash` | MWG Def 8.D.2 | OK | **requires probability distributions** (`IsMixedProfile`), and deviations range over `lotteries` |
| `pureDev` | — | OK | i's payoff from switching to a degenerate t |
| `profileProb_update`, `mixedPayoff_update`, `mixedPayoff_eq_sum_pureDev`, `pureDev_update` | multilinearity | OK | checked: true for arbitrary τ, with no normalization needed |
| `isMixedNash_iff_pure` | MWG Prop 8.D.1 (checking pure deviations is enough) | OK | |
| `IsMixedNash.eq_of_pos` | MWG Prop 8.D.1 (indifference on the support) | OK | together with the previous item this gives the full MWG iff |
| `profileProb_nonneg`, `sum_profileProb`, `sum_update_degenerate`, `pureDev_eq_sum_update`, `profileProb_slice` | — | OK | checked algebraically |
| `pureProfile`, `profileProb_pureProfile`, `mixedPayoff_pureProfile`, `update_pureProfile` | — | OK | |
| `isMixedNash_pureProfile_iff` | MWG 8.D (a pure NE is a mixed NE) | OK | |
| `isCompact_lotteries` | — | OK | |
| `nashGain`, `nashMap` | Nash (1951) map | OK | denominator is at least 1 for every σ, so x/0 junk never arises |
| `continuous_*`, `nashGain_nonneg`, `nashMap_mem`, `exists_pos_pureDev_le`, `isMixedNash_of_nashMap_eq` | Nash (1951) | OK | |
| `exists_isMixedNash` | MWG Prop 8.D.2 | OK | needs `Fintype I` and nonempty finite `S i` (both present); empty I gives a trivial witness, which is correct |
| `penniesPayoff`, `sum_bool_arrow_bool`, example | MWG Ex. 8.D.1 (Matching Pennies) | OK | |

### Games/Rationalizability.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `IsBestResponseTo` | MWG 8.C | OK | pure best reply to `σ_{-i}`, compared against all of `S i` |
| `IsBRSet` | Bernheim/Pearce best-response set; MWG Def 8.C.1–8.C.2 | OK (note) | beliefs are **independent** mixed profiles, with `σ_j` supported in `R j` for j ≠ i only (σ_i is irrelevant because `pureDev` overwrites it). This matches MWG; Osborne–Rubinstein and Fudenberg–Tirole (n ≥ 3) use correlated beliefs (F9) |
| `Rationalizable` | MWG Def 8.C.2 | OK | union of BR sets equals the iterated never-best-response set for finite games |
| `isBRSet_support`, `rationalizable_of_isMixedNash` | MWG Prop 8.C.1 (NE strategies are rationalizable) | OK | |
| `exists_rationalizable` | MWG 8.C | OK | |
| `mem_of_profileProb_pos` | — | OK | |
| `IsBRSet.subset_isd`, `Rationalizable.mem_isd` | MWG 8.C/8.D (rationalizable ⊆ survives ISD) | WEAK | true, but only against **pure-domination** ISD. The textbook equivalence for 2 players (rationalizable = survives mixed-domination ISD) cannot be stated with this `isd` and is false for it (F2) |

### Games/Correlated.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `obedienceGain` | Aumann (1974); Fudenberg–Tirole §2.2 | OK | unconditional (joint-weighted) obedience, so zero-probability recommendations are trivially obeyed, which is correct |
| `IsCorrelatedEq` | Aumann (1974) | OK | **requires μ to be a probability distribution** on profiles; per-recommendation constraints are equivalent to deviation maps `S_i → S_i` |
| `profileProb_mem`, `obedienceGain_profileProb` | — | OK | checked: true without a lottery hypothesis |
| `isCorrelatedEq_of_isMixedNash` | Aumann (1974) | OK | |
| `exists_isCorrelatedEq` | — | OK | |
| `convex_correlatedEq` | F–T §2.2 | OK | |
| `chickenPayoff`, `trafficLight`, example | Aumann's Chicken | OK | the obedience inequalities hold (7 ≥ 6 and 2 ≥ 0) |

### Games/ZeroSum.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `matrixPayoff` | x^T A y | OK | |
| `IsSaddle` | Osborne–Rubinstein ch. 2.5 / von Neumann | OK | **signs are correct**: the row player maximizes (`A(x',y) ≤ A(x,y)`) and the column player minimizes (`A(x,y) ≤ A(x,y')`); both strategies are required to be lotteries |
| `IsValue` | maxmin = minmax = v | OK | both guarantees are present; with empty m or n there are no lotteries, so no value exists, which is consistent |
| `matrixPayoff_mix_left/right`, `continuous_*` | — | OK | |
| `exists_saddle` | von Neumann minimax theorem | OK | |
| `IsSaddle.isValue`, `IsValue.unique`, `exists_unique_value` | O–R Prop 22.2 | OK | |
| `IsSaddle.interchange` | O–R Prop 22.2(c) (interchangeability) | OK | |
| example | Matching Pennies value 0 | OK | |
| (missing) | saddle iff mixed NE of (A, −A) | GAP | not linked to `IsMixedNash` (F10) |

### Games/Bayesian.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `play`, `exAnte` | MWG 8.E (ex-ante payoff under a common prior) | VACUOUS-RISK | `p` is an arbitrary function: it is not required to be nonnegative or to sum to 1 (F1) |
| `IsBNE` | MWG Def 8.E.1 | VACUOUS-RISK | Nash of the ex-ante game, but with any `p`; `p = 0` makes **every** profile a BNE (F1) |
| `interim` | MWG Prop 8.E.1 (unnormalized conditional EU) | OK | weighted by the joint probability, not the conditional one |
| `play_update`, `exAnte_update`, `exAnte_eq_sum_interim` | — | OK | |
| `isBNE_iff_interim` | MWG Prop 8.E.1 | OK (note) | correct **without** a positive-marginal hypothesis: interim is unnormalized, so a zero-marginal type has `interim ≡ 0` and the condition is trivial, matching the ex-ante freedom at null types. For a positive marginal, dividing by it gives the textbook condition. Only for negative `p` does it stop meaning "maximizes conditional EU" (F1) |
| `exists_mixed_BNE` | MWG 8.E (existence via the ex-ante game) | WEAK | mixes over whole plans `Θ i → A i` (ex-ante mixing), not type-by-type behavioural mixing; there is no interim mixed-BNE notion; `p` is arbitrary (F8) |

### Games/Extensive.lean
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `GameTree` | MWG 7.C, finite perfect information | WEAK (scope) | no chance moves, no information sets; at least one action per node (`k+1`) (F6) |
| `Profile` | MWG 7.D (strategy = complete contingent plan) | OK | an action at **every** node, including off-path nodes, which is what SPE needs |
| `outcome` | — | OK | |
| `OnlyDeviates` | unilateral deviation | OK | s' agrees with s at every node not owned by i, recursing into all subtrees (including off-path ones); i may change all of its own nodes at once, as Nash requires |
| `IsNashTree` | MWG Def 8.D.1 on the normal form | OK | |
| `IsSPE` | MWG Def 9.B.1 | OK | in perfect information every node starts a subgame; the recursion requires Nash at every node |
| `NoOneShotDeviation` | backward induction / one-shot deviation | OK | |
| `onlyDeviates_refl`, `NoOneShotDeviation.isNashTree`, `IsSPE.isNashTree` | — | OK | |
| `isSPE_iff_noOneShotDeviation` | one-shot deviation principle (finite horizon) | OK | |
| `exists_isSPE` | MWG Prop 9.B.1 (Zermelo/Kuhn) | WEAK | true, but only for trees without nature moves |
| `IsLeafOf`, `outcome_mem` | — | OK | |
| `zermelo` | Zermelo (1913) | WEAK | the hypothesis is two-player, win/lose payoffs (±1) with **no draws**, so it is not the chess version (win / lose / draw trichotomy). The conclusion is correct: one player has a strategy that wins against every deviation of the opponent (F4) |
| `incumbentNode`, `entryNext`, `entryGame`, `outFight`, `inAccommodate`, example | MWG Ex. 9.B.1 (entry game) | OK | payoffs match MWG (Out (0,2), Fight (−1,−1), Accommodate (1,1)); NE-not-SPE is shown correctly |

### Uncertainty/StochasticDominance.lean (SOSD converse only)
| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `SOSD` (context) | MWG Def 6.D.2 | OK | equal means and all nondecreasing concave u on ℝ (note: concave on `univ`, F10b) |
| `expect_affine_eq` | — | OK | uses total mass 1 |
| `exists_hinge_rep` | proof device (piecewise-linear hinge representation), no textbook result | OK | the hypotheses force `m = min T` when T is nonempty; checked it is true (choose B = u'₋(m)) |
| `expect_le_of_shortfall` | Rothschild–Stiglitz (1970) | OK | equal means plus shortfall dominance gives E_G u ≤ E_F u for **all** concave u, which is stronger than needed |
| `sosd_iff_shortfall` | MWG Prop 6.D.2 (i)⇔(iii) in hinge form | OK | |
| `sosd_iff_concave` | MWG remark after Def 6.D.2 | OK | with equal means, monotonicity can be dropped |
| `sosd_iff_integral_cdf` | MWG Prop 6.D.2 (i)⇔(iii) | OK | `a` strictly below both supports makes `∫_a^t` equal to `∫_{-∞}^t`; for every t such an a ≤ t exists; the direction is correct (F less risky ⇒ smaller integrated cdf); the cdf is a step function, so there is no junk value from a non-integrable function |
| (missing) | MWG Prop 6.D.2 (i)⇒(ii): SOSD ⇒ G is an MPS of F | GAP | only MPS ⇒ SOSD (`sosd_of_meanPreservingSpread`) is stated (F5) |

---

## Detailed findings (non-OK items), ranked by severity

### F1 (VACUOUS-RISK): `IsBNE` / `exAnte` do not require the prior to be a probability distribution
`exAnte u p i s = ∑ θ, p θ * u i (play s θ) θ` with `p : (∀ j, Θ j) → ℝ` unrestricted, and `IsBNE u p s := IsNash (exAnte u p) s`.
This differs from `IsMixedNash` and `IsCorrelatedEq`, which both require `lotteries`.
- **Example (vacuous):** take `p = fun _ => 0`. Then `exAnte ≡ 0`, so `IsBNE u 0 s` holds for every `u` and `s`.
- **Example (sign flip):** take `p = -p₀` for a genuine prior `p₀`. Then `IsBNE u p s` holds exactly when s *minimizes* every type's conditional expected payoff.
- The theorems (`isBNE_iff_interim`, `exists_mixed_BNE`) are still **true**, because they are pure algebra or existence results about a finite game. But `IsBNE` is not MWG Def 8.E.1 unless `p ∈ lotteries (∀ j, Θ j)` is added, and any downstream result of the form "X is a BNE" can be proved for a degenerate prior.
- **Fix:** add `p ∈ lotteries _` to `IsBNE`, or as a hypothesis everywhere it is used.

### F2 (WEAK): iterated deletion uses domination by **pure** strategies only
`StrictlyDominated` asks for `∃ t' ∈ R i` (a pure dominator). MWG 8.D (and Fudenberg–Tirole, and Osborne–Rubinstein Def 60.2) use mixed dominators. As a result:
- `Rationalizable.mem_isd` / `IsBRSet.subset_isd` are true but strictly weaker than the textbook "rationalizable ⊆ survives ISD".
- The converse (MWG 8.C–8.D, for 2 players, rationalizable = survives ISD), is **false** for this `isd`, so it cannot be added later without changing the definition.
- **Counterexample:** player 1 has {T, M, B} and player 2 has {L, R}. Player 1's payoffs: T = (3, 0), M = (1, 1), B = (0, 3). M is not dominated by T (0 < 1 at R) or by B (0 < 1 at L), so `M ∈ isd u n 1` for every n. But ½T + ½B gives (1.5, 1.5) > (1, 1), so M is never a best response and is not `Rationalizable`.
- The name `isd` suggests the textbook procedure; a reader will assume the mixed version.

### F3 (MISMATCH): `IsDominant` is neither MWG's strictly nor weakly dominant strategy
`IsDominant u i t := ∀ s t', u i (update s i t') ≤ u i (update s i t)`. MWG Def 8.B.4 (strictly dominant) requires `<` for every t' ≠ t. MWG Def 8.B.5 (weakly dominant) requires `≤` everywhere **and** `<` for some s₋ᵢ. The Lean notion is "very weakly dominant".
- **Example:** if u i does not depend on i's own action (for instance it is constant), every strategy of i is `IsDominant`. In MWG no strategy is weakly or strictly dominant in that case.
- `isNash_of_dominant` is still true (and slightly stronger). Only the name is misleading, but it would mislead a statement such as "the dominant strategy is unique".

### F4 (WEAK): `zermelo` excludes draws
The hypothesis `hwl` forces every leaf to be (1, −1) or (−1, 1). The conclusion (one player has a strategy that wins against every unilateral deviation by the opponent) is the correct encoding for win/lose games, because `OnlyDeviates false t s s'` fixes the nodes owned by `true`. However, the canonical Zermelo theorem (chess) has the trichotomy "White can force a win, or Black can force a win, or both can force at least a draw". Draw leaves such as (0, 0) are not covered. This is not wrong, but it is narrower than the name implies. A generalization would be the existence of a value v together with a strategy guaranteeing ≥ v and one guaranteeing ≤ v for zero-sum trees.

### F5 (GAP): SOSD ⇒ mean-preserving spread (Rothschild–Stiglitz) is not stated
MWG Prop 6.D.2 is a three-way equivalence: (i) SOSD, (ii) G is an MPS of F, (iii) the integrated-cdf condition. The file proves (i)⇔(iii) (`sosd_iff_integral_cdf`), (i)⇔ the hinge form (`sosd_iff_shortfall`), and (ii)⇒(i) (`sosd_of_meanPreservingSpread`). The direction (i)⇒(ii) is missing. The converse theorems that are present are all correct.

### F6 (WEAK, scope): extensive form is perfect information with no chance moves
`GameTree` has only player nodes and leaves. `IsSPE` is faithful to MWG Def 9.B.1 for that class (every node is a subgame root), and `exists_isSPE` is Kuhn's theorem without nature moves. MWG Prop 9.B.1 and Kuhn's theorem allow chance nodes, and MWG 9.B defines SPE for imperfect information too. There is no information-set structure, so "subgame" cannot be stated in general. This is acceptable if documented, but the names (`IsSPE`, `zermelo`) are broader than the coverage.

### F7 (VACUOUS-RISK, edge case): `StrictlyDominated` is vacuous when an opponent's surviving set is empty
If some `R j` (j ≠ i) is empty, the condition `∀ s, (∀ j, s j ∈ R j) → …` holds vacuously, so every t ∈ R i is "strictly dominated", even by itself (`t' = t`).
- **Example:** S₁ = ℕ with u₁(s) = s₁ (every strategy is beaten by a larger one, so `isd 1 1 = ∅`), and S₂ = {a} with a constant payoff. At round 2, player 2's only strategy a is deleted, because domination against the empty set of player-1 profiles is vacuous: `isd 2 2 = ∅`.
- The same happens at round 1 if any `S j` is empty. All theorems that need it assume `Fintype` or `Nonempty`, so nothing proved is wrong. But `isd` is not meaningful outside finite games with nonempty strategy sets, and nothing in the definition signals this.

### F8 (WEAK): `exists_mixed_BNE` is existence for ex-ante mixing over strategy functions
`σ : ∀ i, (Θ i → A i) → ℝ` mixes over entire plans. There is no definition of a mixed BNE in behavioural (type-by-type) form, and no `IsBNE` analogue for mixed strategies is given. The two are equivalent in payoff terms (Kuhn-type argument), but that equivalence is not stated. The theorem also inherits F1 (any p).

### F9 (note): rationalizability uses independent beliefs
`IsBRSet` requires the belief to be a product `σ` of independent mixtures. This is faithful to MWG 8.C (and to Bernheim/Pearce). For n ≥ 3, Osborne–Rubinstein and Fudenberg–Tirole use correlated beliefs, under which rationalizable = survives mixed ISD in all finite games. With independent beliefs, that equality fails for n ≥ 3 even with mixed ISD, so F2 compounds this.

### F10 (GAP / minor)
a) `ZeroSum`: there is no theorem linking `IsSaddle A x y` to `IsMixedNash` for the two-player game (A, −A), and no statement of the value as `max_x min_y = min_y max_x`. The sign conventions of `IsSaddle` and `IsValue` are correct.
b) `SOSD`: utilities must be concave on all of ℝ. Utilities defined only on ℝ₊ (√x, log x) are not directly admissible, so "SOSD ⇒ E_G √ ≤ E_F √" for nonnegative lotteries supported at 0 is not an instance. It is still true, through the hinge/shortfall route, but it is not stated.

## Checks that came out clean (asked about explicitly)
- **`Function.update s i t`**: a correct one-player deviation everywhere (`IsNash`, `IsBestResponse`, `StrictlyDominated`, `obedienceGain`, `interim`).
- **`OnlyDeviates`**: correct. It fixes every node not owned by i, including off-path subtrees, and lets i change all of its own nodes at once.
- **`pureDev`**: correct. It is independent of σ i (`pureDev_update`) and equals the expected payoff of (t, σ₋ᵢ) when σ i is a lottery (`pureDev_eq_sum_update`).
- **`IsMixedNash` and `IsCorrelatedEq`**: both require probability distributions. `IsBNE`'s prior and `IsSaddle`'s inputs: the prior does not (F1); `IsSaddle` and `IsValue` do.
- **`isBNE_iff_interim`**: correct without a positive-marginal hypothesis, because `interim` is unnormalized.
- **Minimax signs**: correct.
- **Junk values**: the only division is in `nashMap`, whose denominator is at least 1 for every σ. No theorem relies on `x / 0 = 0`.
