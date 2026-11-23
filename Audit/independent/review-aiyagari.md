# Statement review, batch 4: Doeblin, parametric invariant measures, Aiyagari

Scope: `/tmp/claude-0/review4/statements.lean` only. I judged the statements and definitions as written. The proofs are `sorry` and were not reviewed.

## Summary table

| Declaration | Textbook reference | Verdict | Reason |
|---|---|---|---|
| `integrable_of_bounded` | standard measure theory | OK | A bounded measurable function is integrable under a finite measure. |
| `integral_sub_le_hahn` | Hahn decomposition bound | OK | Correct for f in [0,c]. The degenerate case X = ∅ gives 0 ≤ 0. |
| `comp_real_eq_integral` | (μK)(A) = ∫K(x,A)dμ | OK | Standard identity. |
| `doeblin_step` | Dobrushin/Doeblin TV contraction (M–T Thm 16.2.4 proof; SLP Lemma 11.11) | OK | One-sided sup-contraction by (1-ε). Taking A = ∅ forces c ≥ 0, so there is no junk case. |
| `iterComp`, `isProbabilityMeasure_iterComp` | μPⁿ | OK | |
| `doeblin_convergence` | M–T Thm 16.0.2 / 16.2.4 (uniform ergodicity under whole-space minorization) | WEAK | The rate is correct (TV sup convention). It assumes an invariant π exists and does not prove one does. The hypothesis is minorization, not SLP Condition D. |
| `doeblin_unique` | M–T 16.2; SLP Thm 11.12 (Condition M) as a special case | WEAK | Proves uniqueness only. Existence of an invariant measure under minorization is not stated for general kernels. |
| `isMarkovKernel_pow`, `invariant_pow` | trivial | OK | |
| `unique_invariant_of_pow` | M–T Thm 16.0.2(v) (state space νₘ-small) | WEAK | Gives uniqueness only. There is no N-step convergence rate for general kernels (the matrix version has one). N = 0 can only be met on a trivial σ-algebra, where the result still holds. |
| `IsStochastic.pow`, `IsInvariant.pow` | trivial | OK | |
| `doeblin_pow` | SLP Thm 11.4 (finite chains, some Qᴺ > 0); Dobrushin | OK | The rate 2(1-\|Z\|ε)^⌊n/N⌋ is correct. N = 0 forces \|Z\| = 1 (Q⁰ = I) and the bound is then trivially true. Junk n/0 = 0 does no harm. |
| example after `doeblin_pow` | periodic-free, non-positive Q with Q² > 0 | OK | A good nondegenerate witness. |
| `IsJointlyFeller` | SLP Thm 12.13 hypothesis (joint continuity of (x,θ) ↦ ∫f dP_θ(x,·)) | OK | Faithful. |
| `tendsto_invariant_of_unique` | SLP Thm 12.13 (local form) | OK | Uses the weak topology on `ProbabilityMeasure`, as SLP does. It is valid for an arbitrary topological Θ (tube lemma plus compactness of 𝒫(X)). |
| `continuous_invariant_of_unique` | SLP Thm 12.13 | OK | |
| `continuous_integral_invariant` | SLP Thm 12.13, corollary | OK | |
| `ParamSavings` | Aiyagari (1994) household; L–S ch. 18 | WEAK | Assets are capped at an exogenous `kbar`. Aiyagari derives the upper bound; here it is imposed and may bind. Wage and labor are folded into an arbitrary h(θ,k,z). |
| `slice`, `S`, `continuous_hS`, `augΓ`, `augF`, `augΓ_isClosed_graph`, `augΓ_lhc`, `aug` | SLP §3.3 / Berge with the parameter as a frozen state | OK | Faithful augmentation: θ' = θ. |
| `value_slice`, `objective_slice`, `policy_slice` | consistency of the augmented DP | OK | |
| `exists_joint_policy` | SLP Thm 9.8 + Berge (joint continuity of the policy in (θ,s)) | OK | Strict concavity of u and concavity of h give a single-valued policy. |
| `isJointlyFeller_policyKernel` | SLP Ex. 8.x / Thm 12.13 application | OK | |
| `assets`, `assets_le`, `integral_assets_le` | aggregate supply ∫a dλ | OK | Bounded and continuous, so there is no integrability junk. |
| `UniqueStationary` | Hopenhayn–Prescott (1992) Thm 2 conclusion; Aiyagari's uniqueness claim | WEAK | This is a definition used as a hypothesis everywhere. No theorem in the file derives it from model primitives (HP92 monotone mixing, or Doeblin through `unique_invariant_of_pow`). |
| `continuous_aggregate` | SLP Thm 12.13 applied to Aiyagari | OK (conditional) | Faithful, but it assumes `huniq` for every θ. |
| `exists_equilibrium` | Aiyagari (1994) Fig. II–III existence; Açıkgöz (2018) | WEAK / MISMATCH | Plain IVT on supply minus Kd. `hhi` assumes the endogenous supply at r_hi. Kd is an arbitrary continuous function, not tied to h or a firm. `huniq` is stronger than Açıkgöz needs. The only end-to-end instance is degenerate (K = 0). Truncation artifacts are possible. |
| `aiyagariFamily` + example | Aiyagari parametrisation | VACUOUS-RISK | Only `exists_joint_policy` is instantiated. Neither `UniqueStationary` nor `hhi` is shown, so `exists_equilibrium` is never applied to an economy where saving earns a return. |
| `noReturn`, `noReturn_value`, `noReturn_policy`, `noReturn_uniqueStationary` | none (toy model) | OK as lemmas | Correct: h does not depend on k, so g ≡ 0. |
| example `exists_equilibrium noReturn` | none | VACUOUS-RISK | Degenerate witness. Supply ≡ 0, demand Kd(r) = 1-r, and the equilibrium is r = 1 with K = 0. |

## Details on the non-OK items

### 1. `exists_equilibrium`: the hypotheses carry the economics (MEDIUM-HIGH)

The proof is the intermediate value theorem applied to A(r) - Kd(r), where A is continuous by `continuous_aggregate`:
- `hlo : kbar ≤ Kd rlo` combined with `integral_assets_le` gives A(rlo) ≤ Kd(rlo);
- `hhi` gives A(rhi) ≥ Kd(rhi).

The structure is correct, but the key economic step in Aiyagari is the endpoint behaviour:
- demand exceeds supply as r ↓ -δ;
- supply diverges as r ↑ 1/β - 1 (Chamberlain–Wilson / Aiyagari).

The second fact is assumed through `hhi`, which is a statement about the endogenous stationary distribution. It is never derived. It also cannot be derived in this setup: assets are capped at `kbar`, so the "supply → ∞" mechanism does not exist. `hhi` therefore has to be checked by hand for each economy, which is half of the existence argument.

`hhi` is also trivially satisfiable when Kd(rhi) ≤ 0, because supply is nonnegative. Kd is not required to be positive or to come from a production function F_K(K,L) = r + δ. Consistency with how r and w enter h is not required either: h(θ,k,z) is arbitrary in θ, and there is no wage w(r) and no labor-market clearing L = Σ z π(z). The theorem is a partial-equilibrium market-clearing statement for an arbitrary continuous demand curve, not Aiyagari's general equilibrium. The concept is right, but the statement is weaker than its name suggests.

### 2. Exogenous cap `kbar` can manufacture "equilibria" (MEDIUM)

`ParamSavings.S = Icc 0 kbar`, and the choice y is required to lie in S. Aiyagari proves there is an upper bound ā when β(1+r) < 1. Here the bound is imposed exogenously, and nothing requires that it does not bind.

Counterexample sketch: take Θ = [0, 0.5], β = 0.9, h = (1+r)k + z.
- At r = 0.5, β(1+r) = 1.35 > 1. Agents accumulate to `kbar`, and the stationary law is a point mass at `kbar` (times the z-marginal), so it is unique and `huniq` can hold.
- Set kbar = 1 and Kd(r) = 1.2 - r. Then `hlo` holds (Kd(0) = 1.2 ≥ 1), and `hhi` holds if supply at 0.5 is about kbar = 1 ≥ 0.7.
- The IVT can then return an r with β(1+r) ≥ 1. In the untruncated economy, assets diverge there and no stationary distribution exists.

So `exists_equilibrium` can certify equilibria that exist only because of the cap. A faithful version would need either rhi < 1/β - 1 together with a theorem that the policy satisfies g < kbar (the natural bound), or a hypothesis that the cap does not bind.

### 3. `UniqueStationary` is assumed and never established in a nondegenerate model (MEDIUM)

`continuous_aggregate` and `exists_equilibrium` both take `huniq : ∀ θ, UniqueStationary θ`. The only proved instance is `noReturn`, where the policy is g ≡ 0 and the result is immediate.

In the literature, uniqueness comes from one of two routes, and neither is formalized or connected here:
- Hopenhayn–Prescott (1992) Thm 2: monotone policy plus a mixing condition;
- a Doeblin/minorization argument: after N bad shocks every agent hits the borrowing limit 0, so Kᴺ(x,·) ≥ ε δ₀⊗q.

`Doeblin.lean` is imported by `Aiyagari.lean`, but no statement links `unique_invariant_of_pow` to `UniqueStationary` for `policyKernel`. This is a coverage gap: the hardest part of the Aiyagari existence proof is a hypothesis.

Açıkgöz (2018) shows that existence holds without uniqueness. The invariant-measure correspondence is upper hemicontinuous with convex values, so aggregate supply is a UHC correspondence with interval values and the IVT for correspondences applies. With respect to that reference, `huniq` is an unnecessary assumption, and the theorem is strictly weaker than the state of the art.

### 4. The witnesses are degenerate (MEDIUM)

- The `noReturn` example instantiates `exists_equilibrium` with h independent of (θ,k). Saving earns nothing, so g ≡ 0 and supply ≡ 0. The equilibrium is r = 1 with K = Kd(1) = 0. `hhi` is discharged by `sub_self` plus nonnegativity, so it is the trivial form "Kd(rhi) ≤ 0" from §1.
- `aiyagariFamily` (r ∈ [0, 0.05], β = 0.9, β(1+r) ≤ 0.945 < 1) is the economically meaningful model. Only `exists_joint_policy` is applied to it. Neither `UniqueStationary` nor `hhi` (positive supply at r = 0.05) is shown.

The hypotheses of `exists_equilibrium` are therefore jointly satisfiable, so the theorem is not vacuous, but this is only demonstrated in a model where saving earns no return and nobody saves.

Recommended fix: prove `UniqueStationary` for `aiyagariFamily`. The minorization route is plausible: with i.i.d. shocks and the low shock, agents run down to 0 within N steps. Also exhibit a positive Kd with an explicit lower bound on supply at r = 0.05.

### 5. The general-kernel "Doeblin" is minorization, not SLP Condition D (LOW-MEDIUM: naming and coverage)

`hmin : ε φ(A) ≤ K(x,A)` for all x and A is uniform minorization: the whole space is small (M–T Thm 16.0.2(v)). It is strictly stronger than both of the following:
- SLP **Condition D**: ∃ φ, N, ε such that φ(A) ≤ ε ⇒ Pᴺ(x,A) ≤ 1-ε;
- M–T's "Doeblin's condition" in §16.2.

Minorization implies SLP **Condition M** with ε/2, so the results are special cases of SLP Thm 11.12, not of Thm 11.10.

Counterexample to "this covers SLP 11.10": take the periodic chain P = [[0,1],[1,0]].
- It satisfies Condition D: with φ uniform and ε < 1/2, the only A with φ(A) ≤ ε is ∅.
- It has a single ergodic set, so SLP Thm 11.10 gives a unique invariant measure (1/2, 1/2) and Cesàro convergence.
- No Pᴺ admits a minorization, because Pᴺ is I or the swap.

So `doeblin_unique` and `unique_invariant_of_pow` cannot reach this chain, and Thm 11.10, including its Cesàro-convergence conclusion, is not formalized. Two smaller points:
- Existence of an invariant measure under minorization (Banach fixed point in TV) is missing for general kernels. `doeblin_convergence` and `doeblin_unique` both take π as given.
- There is no N-step geometric convergence for general kernels. `doeblin_pow` provides it only for finite Z.

### 6. `doeblin_convergence` topology and rate (LOW: confirmation)

The conclusion |μPⁿ(A) - π(A)| ≤ (1-ε)ⁿ, uniform in A, is total-variation convergence in the sup-over-sets convention. It equals M–T's ‖·‖ ≤ 2(1-ε)ⁿ. It is not weak convergence. This is correct and matches the textbook.

### 7. `ParamInvariant`: no problems found

`IsJointlyFeller` matches the SLP 12.13 hypothesis. X is compact and pseudo-metrizable and Θ is an arbitrary topological space. The statement remains true for general Θ, because joint continuity on Θ × X with X compact gives θ ↦ P_θ f continuous in the sup norm, and 𝒫(X) is weakly compact. Uniqueness is only needed at θ₀ in the local version, as in SLP.

---

## Round 2 (regenerated statements.lean)

### Changes verified

| Declaration | Reference | Verdict | Reason |
|---|---|---|---|
| `invariant_of_tendsto` | SLP Thm 12.13 proof step; Açıkgöz (2018) Lemma (UHC of the invariant correspondence) | OK | True as stated, for any filter (nets) and any topological Θ. On compact X, joint Feller gives Kθ f → Kθ₀ f uniformly (tube lemma). Weak convergence then gives ∫Kθ₀f dμ₀ = ∫f dμ₀ for all f ∈ C_b. Pseudo-metrizability makes C_b determine measures. Dropping `T2Space X` is harmless: the argument works for any limit μ₀. |
| `isClosed_invariant_graph` | Açıkgöz (2018); closed graph of λ ↦ Λ(θ) | OK | Follows from the previous lemma by the filter characterisation of closure in Θ × 𝒫(X) (weak topology). |
| `exists_equilibrium` (no `huniq`) | Açıkgöz (2018) Thm 1 (existence without uniqueness), partial equilibrium | OK (true) / WEAK (content) | Now a correct IVT for an upper-hemicontinuous, convex-valued correspondence: Λ(r) is convex, the integral is linear, so A(r) is an interval with closed graph. `hlo` gives D ≥ 0 at rlo for all selections, and `hhi` gives D ≤ 0 at rhi for all selections, so 0 ∈ D(r) for some r. The statement is true, and the HIGH-1 uniqueness issue is fixed. |
| `example` on `aiyagariFamily` | Aiyagari with r ∈ [0, 0.05], β(1+r) ≤ 0.945 | WEAK (see R2-1) | Instantiates the theorem on a model with returns, but both endpoint hypotheses are discharged trivially. |
| `continuous_aggregate`, `UniqueStationary` | SLP 12.13 | OK, unchanged | Still conditional on `huniq`. No longer on the critical path. |

### Nothing became false or vacuous

I found no new MISMATCH or SUSPICIOUS item. Removing `huniq` strengthens `exists_equilibrium`. The new lemmas are correct generalisations, using filters instead of sequences, and need no metrisability of Θ.

### R2-1 (MEDIUM): the new `aiyagariFamily` example discharges both boundary conditions trivially, so it checks no economics

With Kd(r) = 1 − 20r:
- `hlo` is `kbar = 1 ≤ Kd 0 = 1`, which compares demand against the cap only;
- `hhi` is `Kd(1/20) = 0 ≤ ∫ assets`, which is just nonnegativity of assets (`integral_nonneg`).

This is exactly the trivial form flagged in round 1, §1. In general, the theorem holds for any household block as soon as Kd(rlo) ≥ kbar and Kd(rhi) ≤ 0, because supply always lies in [0, kbar].

The theorem is still true, and its content in that regime is "a continuous demand curve sweeping [0, kbar] crosses the supply correspondence". That is fine as a statement, but the example should not be read as evidence that the boundary condition `hhi` is economically checkable. Kd(rhi) = 0 is also not neoclassical: with F_K → ∞ as K → 0, demand is strictly positive at every finite r.

Side remark: a quick Euler check suggests the equilibrium found is nondegenerate. At a = 0 with high income, u'(1/2) ≈ 0.707 < 0.945 · E u'(z') ≈ 0.807, so agents with high income save and supply at r = 0.05 is positive. Equilibrium therefore has K = 1 − 20r > 0. Nothing in the file states or proves this, so the formal witness does not certify K > 0.

Suggested fix: use a demand curve with Kd(rhi) > 0, together with a lemma giving a positive lower bound on stationary supply at rhi (for example, from the Euler inequality above). Alternatively, label the example as an existence check only.

### R2-2 (MEDIUM, documented, unchanged): the exogenous cap `kbar`

This is still not fixed. `exists_equilibrium` can return r with β(1+r) ≥ 1, where only the truncation keeps supply finite (counterexample in round 1, §2). It is now documented, which is acceptable as a stated gap. A cheap guard is to require rhi < 1/β − 1 in the statement.

For `aiyagariFamily` this is harmless in practice (β(1+r) < 1 on the whole interval), but the code does not show that the cap kbar = 1 is slack.

### R2-3 (LOW): `hhi` is quantified more strongly than Açıkgöz needs

`hhi` requires Kd(rhi) ≤ ∫assets dμ for every invariant μ at rhi. The correspondence IVT only needs one such μ. The `∃` form is weaker, still yields the conclusion, and matters when stationary distributions are not unique, which is exactly the case the uniqueness-free version is meant to handle. This is not wrong, only stronger than necessary.

### R2-4 (LOW, documented): the remaining gaps are honest

- Partial equilibrium only: there is no firm, no wage w(r), and no labor-market clearing. The household's θ-dependence of h is not tied to Kd. This is acceptable now that it is documented, but the name `exists_equilibrium` still overstates what is proved. Consider `exists_asset_market_clearing`.
- The general-kernel Doeblin results use uniform minorization (SLP Condition M special case). SLP Condition D and Thm 11.10 (Cesàro convergence) remain uncovered. Existence of an invariant measure under minorization for general (non-compact, non-Feller) kernels is still not stated.
- `UniqueStationary` is still not derived for any model with returns. Since `exists_equilibrium` no longer needs it, this only affects `continuous_aggregate`.

### Round-2 ranking

- HIGH: none remaining.
- MEDIUM: R2-1 (the new witness discharges both endpoint conditions trivially, using Kd(rhi) = 0); R2-2 (cap artifact, documented but unguarded).
- LOW: R2-3 (`∀` where `∃` suffices in `hhi`); R2-4 (theorem name versus partial-equilibrium content; Condition D / Thm 11.10 and general-kernel existence still missing; `UniqueStationary` underived).
