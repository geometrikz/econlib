# Statement review G: general GE existence and fixed-point foundations

Targets: `GE/ExistenceGeneral.lean`, `Foundations/FixedPoint.lean`, `Foundations/FixedPoint/**` (Brouwer/KKM, Common/*, Kakutani/*).
Context read: `GE/Existence.lean`, `GE/Exchange.lean`, `GE/Examples.lean`, `Consumer/Demand.lean`, `Consumer/Budget.lean`, `Preferences/*`.
I reasoned about the Lean/Mathlib semantics by hand. Lean was not run.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `ExchangeEconomy.exists_freeDisposalEquilibrium'` | GE/ExistenceGeneral | MWG Prop 17.C.1 + 17.B.2; Debreu ToV 5.7; Arrow–Debreu 1954 | **VACUOUS-RISK / MISMATCH** | It needs a demand selection that is defined and continuous on the **closed** simplex. No economy with ≥2 goods and a strongly monotone, Cobb–Douglas, CES or linear consumer can meet this. Only Leontief-type (satiated-in-a-direction) economies can. |
| `gale_nikaido_debreu'` | GE/ExistenceGeneral | Gale–Nikaido–Debreu lemma (Debreu ToV 5.6; Border Thm 18.x, single-valued case) | faithful with documented deviation | Single-valued version only. The correspondence version (needed for Debreu/AD) is absent. |
| `brouwerSimplex` | GE/ExistenceGeneral | Brouwer on Δ | faithful | Discharges the `BrouwerSimplex` hypothesis of `GE/Existence.lean`. `Nonempty ι` is needed (Δ(∅)=∅), see G5. |
| `convex_/isCompact_/priceSimplex_nonempty` | GE/ExistenceGeneral | – | faithful | |
| `brouwer_fixedPoint`, `Brouwer.KKM.exists_fixedPoint` | FixedPoint, Brouwer/KKM | Brouwer; Border Cor 6.6 | faithful | Covers any nonempty compact convex set in a finite-dim real normed space: the simplex, compact convex subsets of ℝⁿ and closed balls (checked in G5). Brouwer is **not** a hypothesis. |
| `brouwer_fixedPoint_continuousMap`, `exists_fixedPoint_continuousMap` | FixedPoint, KKM | same | faithful | `C(s,s)` form. |
| `Brouwer.KKM.exists_fixedPoint_stdSimplex` | Brouwer/KKM | Brouwer on Δʳ | faithful | |
| `Brouwer.KKM.exists_fixedPoint_of_innerProductSpace` | Brouwer/KKM | Brouwer | faithful | |
| `Brouwer.KKM.exists_mem_iInter` | Brouwer/KKM | KKM lemma (KKM 1929; Border Thm 5.4) | faithful | Closed `F i`, with every face conv{eᵢ : i∈I} ⊆ ⋃_{i∈I} Fᵢ. The conclusion is even slightly stronger: the common point lies in Δ. The hypotheses are not vacuous (e.g. Fᵢ = Δ). |
| `Sperner.count_eq_one` | Common/Sperner | Sperner's lemma (Sperner 1928; Border Thm 4.?) | faithful with documented deviation | States the parity of fully-labelled cells for the **n-fold iterated barycentric subdivision** only, not for arbitrary triangulations. The subdivision is non-degenerate: cells shrink like (r/(r+1))ⁿ (`exists_cell`, `l1_verts_sub_le`). The labelling condition `v (h v) ≠ 0` is exactly Sperner's. |
| `Sperner.count`, `Sperner.doors` (defs) | Common/Sperner | – | faithful | Recursive mod-2 count over cells `vmap σ₁ ∘ … ∘ vmap σₙ (Δ)`. Only the values of `h` on Δ matter (`count_congr`). |
| `Sperner.exists_cell` | Common/Sperner | (Sperner → approximate fixed point) | faithful | A nonzero count gives a cell carrying label set A with mesh ≤ 2(r/(r+1))ⁿ. |
| other Sperner lemmas (`sum_erase_image_eq`, `doors_eq*`, `facet*`, `pieceOf*`, `count_fin_one`, …) | Common/Sperner | – | faithful (quick pass) | Combinatorial helpers. |
| `simplex`, `vertex`, `vmap`, `coord`, `piece`, `coords`, `verts`, `interp`, `l1` | Common/Subdivision | barycentric subdivision | faithful | `vertex σ k` is the barycentre of {σ0..σk}. |
| `l1_vmap_le` | Common/Subdivision | barycentric diameter bound r/(r+1) | faithful | Checked on extreme points (e_j−e_k)/2: ‖vertex σ j − vertex σ k‖₁ = 2(k−j)/(k+1) ≤ 2r/(r+1). |
| `l1_verts_sub_le`, `dist_verts_le`, `continuousOn_interp`, other Subdivision lemmas | Common/Subdivision | – | faithful (quick pass) | |
| `FixedPoint.exists_simplex_coords`, `exists_subset_convexHull_simplex` | Common/EnclosingSimplex | – | faithful | Enclosing simplex with continuous barycentric coordinates. Covers finrank = 0. |
| `FixedPoint.exists_fixedPoint_of_euclidean`, `exists_mem_self_of_euclidean` | Common/Euclidean | – | faithful (helper) | These take Brouwer/Kakutani on `EuclideanSpace` as hypothesis `H`. That is legitimate for a transfer lemma, and no headline theorem inherits `H`. |
| `FixedPoint.exists_fixedPoint_continuousMap_of` | Common/ContinuousMap | – | faithful (helper) | |
| `NearestPoint.exists_lipschitzWith_retraction` | Common/NearestPoint | Hilbert projection | faithful | |
| `kakutani_fixedPoint`, `Kakutani.exists_fixedPoint*` | FixedPoint, Kakutani/* | Kakutani 1941; Border Cor 15.3 | faithful | Graph is closed relative to s × V. Closed values follow. |
| `Kakutani.isClosed_graph_iff_seq`, `exists_mem_self_of_approx` | Kakutani/* | – | faithful (helper) | |
| — coverage — MWG 17.C.1 (excess demand on the open simplex + boundary condition 17.B.2(v)) | – | MWG 17.C.1 | **MISSING** | No boundary condition, no z on the interior, no derivation of 17.B.2 properties from preferences. |
| — coverage — Debreu / Arrow–Debreu existence (production, demand correspondences via Kakutani) | – | Debreu ToV 5.7; AD 1954 Thm I | **MISSING** | Kakutani is formalized but unused for GE. `GE/Production.lean` has no existence theorem. |

## Detailed findings

### F1 (most serious). `exists_freeDisposalEquilibrium'` cannot be applied to any strongly monotone economy

```
theorem exists_freeDisposalEquilibrium' [Nonempty ι] (E : ExchangeEconomy α ι)
    (hlns : ∀ a, LocallyNonsatiated (E.pref a)) {d}
    (hd : E.IsDemandSelection d (priceSimplex ι))
    (hc : ∀ a, ContinuousOn (d a) (priceSimplex ι)) : ...
```

`IsDemandSelection d (priceSimplex ι)` requires `d a p ∈ demand (E.pref a) p (E.wealth p a)` for **every** p in the closed simplex, including corners such as p = e₀.

- **Strongly monotone** (`StronglyMonotone`, the library's own notion). Take p with pᵢ = 0. For x in the budget set, y = x + eᵢ costs the same and is strictly preferred, so `demand R p w = ∅` for **every** w. Hence with ≥2 goods and ≥1 strongly monotone agent the hypothesis `hd` is false. This is proved in `sanity_tests.lean` as `demand_eq_empty_of_stronglyMonotone` and `not_isDemandSelection_of_stronglyMonotone`. It is then instantiated on the project's own `GEExamples.linEconomy`, which has an equilibrium at p=(1,1) that this theorem cannot find.
- **Cobb–Douglas** u = x₀x₁ (not `StronglyMonotone` here, since u=0 on the axes). At p = e₀ with wealth 1, (1, x₁+1) is affordable and strictly better than any affordable x, so demand is empty (G2). Any agent with ω₀ > 0 therefore breaks `hd`. Also, demand x₁ = w/(2p₁) blows up as p₁ → 0, so `hc` fails on the closed simplex regardless.
- **CES** (ρ ∈ (0,1)): same as Cobb–Douglas.
- **Linear**: empty demand at corners. In addition, there is no continuous selection even on the open simplex, because demand jumps at p₀ = p₁ (G3).
- Satisfiable cases: `GEExamples.leonEconomy` (Leontief min(x₀,x₁)) does satisfy `hd`/`hc`, so the theorem is not literally vacuous. But its domain is essentially preferences that are satiated in the direction of each free good, or agents with zero wealth at every corner.

This is exactly the defect the brief warned about in the "earlier version", and it is **still present**: `ExistenceGeneral` only discharges `hB : BrouwerSimplex` from `GE/Existence.lean`. The hypotheses are otherwise identical. The canonical result (MWG 17.C.1) instead assumes z defined and continuous only on the **interior** {p ≫ 0}, homogeneous of degree 0, satisfying Walras' law, bounded below, and the boundary condition 17.B.2(v): if pⁿ → p ≠ 0 with some p_l = 0, then max_l z_l(pⁿ) → ∞. Those are exactly the properties strongly monotone, strictly convex, continuous preferences with ω ≫ 0 deliver (MWG Prop 17.B.2). None of this is stated.

Fix: state a `Prop 17.C.1` version with `z : (ι → ℝ) → ι → ℝ` continuous on `{p | ∀ i, 0 < p i}` plus the boundary condition. Then derive 17.B.2 from preferences, using Berge's maximum theorem from `Foundations/Maximum.lean`. Alternatively, use the Debreu truncation-of-consumption-sets argument with the correspondence GND.

### F2. The key economic step (continuity of demand) is assumed

`hc : ∀ a, ContinuousOn (d a) (priceSimplex ι)` assumes what MWG 17.B.2(i)/Debreu prove from continuity and strict convexity of preferences via Berge's theorem. Combined with F1, the theorem is close to `gale_nikaido_debreu'` (Walras' law, given LNS) relabelled as an economic theorem. There is no primitive-level existence theorem: continuous, (strictly) convex, LNS/strongly monotone preferences with ω ≫ 0 ⇒ ∃ Walrasian equilibrium.

### F3. Coverage gaps: MWG 17.C.1, Debreu, Arrow–Debreu not stated

- MWG 17.C.1 (interior excess demand + boundary condition): absent (see F1).
- Debreu, *Theory of Value* §5.7 / Arrow–Debreu (1954): existence with production sets Yⱼ (closed, convex, 0 ∈ Yⱼ, irreversibility, free disposal) and demand **correspondences**. Absent. `kakutani_fixedPoint` is formalized but no correspondence-valued GND (Border; Debreu 1956) or GE theorem uses it. `GE/Production.lean` defines equilibria but has no existence theorem.
- Free-disposal equilibrium → Walrasian equilibrium needs p ≫ 0 (`IsFreeDisposalEquilibrium.isWalrasianEquilibrium`). Under the theorem's hypotheses (which exclude strongly monotone agents) there is no general route to an equilibrium with Σx = ω.

### F4 (minor). Trivial instances

The theorem holds for an empty set of agents (G4). It is harmless, and `IsFreeDisposalEquilibrium` is then trivially satisfied, but it confirms that the content comes entirely from `hd`/`hc`.

### F5 (minor, documented deviation). Sperner only for iterated barycentric subdivisions

`Sperner.count_eq_one` is not the general statement "every Sperner-labelled triangulation has an odd number of fully labelled cells". It counts cells of the n-fold barycentric subdivision, encoded as sequences of permutations. It is **not** degenerate:
- `vmap σ` maps Δ affinely onto the barycentric piece for σ, with affinely independent vertices.
- `l1_vmap_le` gives the contraction r/(r+1), so the mesh goes to 0 (`exists_cell`).
- The n = 0 case is the trivial one-cell subdivision, but the statement is for all n.
- Sperner condition `v (h v) ≠ 0` on Δ is equivalent to h(v) ∈ supp v.

This is enough for Brouwer/KKM. Users expecting general Sperner should be told.

### F6 (positive). Brouwer status

- `brouwer_fixedPoint` / `Brouwer.KKM.exists_fixedPoint` take no Brouwer-type hypothesis. The spaces covered are any nonempty compact convex subset of a finite-dimensional real normed space: simplex, compact convex subsets of ℝⁿ, closed balls.
- Brouwer **is** still a hypothesis (`hB : BrouwerSimplex ι`) in `GE/Existence.lean`'s `gale_nikaido_debreu` and `exists_freeDisposalEquilibrium`. `ExistenceGeneral` discharges it via `brouwerSimplex`. That is acceptable, but the hB-versions should be deprecated or renamed so they are not cited as unconditional.
- `Common/Euclidean.lean` helpers take Brouwer/Kakutani on `EuclideanSpace` as `H`. These are transfer lemmas only.
- Not covered (not claimed): sets homeomorphic to compact convex sets, and Schauder.

### F7 (positive). KKM

`Brouwer.KKM.exists_mem_iInter` matches Border Thm 5.4: closed Fᵢ, with conv{eᵢ : i ∈ I} ⊆ ⋃_{i∈I} Fᵢ for all I. It is not trivially true. For I = ∅ the condition is vacuous, as in the textbook. The conclusion also puts the common point in Δ. This is a genuine strengthening, since the Fᵢ may extend outside Δ, and it is still true because the standard proof finds the point in Δ.
