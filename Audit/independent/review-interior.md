# Statement review: `GE/ExistenceInterior.lean`

Reviewer: context-isolated adversarial referee. Only files under `/home/user/rv3/in/` were read.
References: MWG (Mas-Colell, Whinston, Green 1995) Prop. 17.B.2 and Prop. 17.C.1; Jehle–Reny (3rd ed.) Thm 5.3 / 5.4.

**Overall verdict:** the headline theorem is a **faithful** formalization of MWG Prop. 17.C.1 (first sentence). It is actually slightly *stronger*, because homogeneity of degree zero is not assumed. I found no vacuity, no junk-value loophole and no quantifier error. The main gap is in **coverage**: the "Hence, a Walrasian equilibrium exists in any exchange economy..." half of 17.C.1, and Prop. 17.B.2 (economy ⇒ (i)–(v)), are not stated.

## Summary table

| Declaration | File | Reference | Verdict | Reason |
|---|---|---|---|---|
| `exists_equilibrium_of_boundaryCondition` | GE/ExistenceInterior.lean | MWG Prop. 17.C.1 | faithful with documented deviation | It has all of 17.B.2's conditions except (ii) homogeneity, which is dropped. That makes it a strict generalization, and it is still true. Conclusion is p ≫ 0 with z(p)=0. |
| `ExcessBoundedBelow` | GE/ExistenceInterior.lean | MWG 17.B.2(iv) | faithful | `∃ s, ∀ p ≫ 0, ∀ l, −s < z_l(p)` is the uniform bound. Positivity of s is not required, which doesn't matter. |
| `BoundaryCondition` | GE/ExistenceInterior.lean | MWG 17.B.2(v) | faithful | `∀` sequences pⁿ ≫ 0 with pⁿ → p̄ ≠ 0 and some p̄_l = 0, `∀ M`, eventually `∃ l, M < z_l(pⁿ)`. This is exactly max_l z_l(pⁿ) → ∞. p̄ ≥ 0 is automatic as a limit. |
| `exists_approx_equilibrium` | GE/ExistenceInterior.lean | MWG 17.C.1 proof step (truncated / ε-shrunk simplex); no numbered result | faithful (true intermediate lemma) | It follows from GND applied to p ↦ (1−Nε)z(shrink p)+ε(Σz)𝟙, whose value is 0 on Δ by Walras. It is still true in the edge case Nε = 1. |
| `shrinkPrice`, `shrinkPrice_mem`, `cost_shrinkPrice`, `continuous_shrinkPrice` | GE/ExistenceInterior.lean | auxiliary | faithful | These are correct algebra: shrink p_i ≥ ε > 0, Σ = (1−Nε)+Nε = 1. |
| `isOpen_positivePrices` | GE/ExistenceInterior.lean | auxiliary | faithful | `[Finite ι]` is needed, and it is present. With infinitely many goods the statement would be false in the product topology. |
| (coverage) "Hence a WE exists in any exchange economy with Σω ≫ 0, continuous, strictly convex, strongly monotone preferences" | — | MWG 17.C.1 second sentence, Prop. 17.B.2; JR Thm 5.4 / 5.5 | WEAK (coverage gap) | No theorem builds an `ExchangeEconomy`'s aggregate excess demand and proves it satisfies (i)–(v). The only instance (`AggregationExamples.zCD`) is a hand-written 2-good formula. |

## Detailed checks of the headline theorem

### Hypotheses vs MWG 17.B.2

MWG 17.B.2: z defined on ℝ^L_{++} with (i) continuous, (ii) homogeneous of degree zero, (iii) Walras' law p·z(p)=0, (iv) ∃ s > 0, z_l(p) > −s ∀ l, p, (v) pⁿ → p ≠ 0 with p_l = 0 for some l ⇒ max_l z_l(pⁿ) → ∞.

| MWG | Lean | Match? |
|---|---|---|
| (i) continuity on ℝ^L_{++} | `ContinuousOn z {p \| PositivePrices p}` | yes |
| (ii) homogeneity of degree 0 | **absent** | dropped: this makes the Lean theorem stronger. It is still true because MWG's proof only uses z on the relative interior of Δ. Homogeneity is used only to say that this loses nothing. `exists_approx_equilibrium` shows that this simplex route is the one taken. See sanity test §2: a non-homogeneous z satisfying every hypothesis. |
| (iii) Walras' law (equality) | `∀ p ≫ 0, cost p (z p) = 0` | yes (equality, not ≤) |
| (iv) uniform lower bound | `ExcessBoundedBelow` (one s for all p, l) | yes, uniform |
| (v) boundary condition | `BoundaryCondition` | yes. The quantifiers are ∀ sequence, ∀ limit, ∀ M, eventually ∃ l, and this is exactly max → +∞. Sequences are required to lie in ℝ^L_{++}, as in MWG. |
| L ≥ 1 | `[Nonempty ι]` | harmless. With ι empty, the conclusion would hold trivially anyway. |

### Conclusion

`∃ p, PositivePrices p ∧ z p = 0`: p ≫ 0 and z(p) = 0 exactly. This matches 17.C.1 (where the domain of z is ℝ^L_{++}). It is not weakened to z ≤ 0 or p ≥ 0.

### Junk values / off-cone behaviour

Every hypothesis quantifies only over p ≫ 0, and so does the conclusion. Values of z off ℝ^L_{++}, where for example the Lean Cobb–Douglas formula returns junk because x/0 = 0, can never serve as a witness. So the theorem cannot hold for the wrong reason, and there is no `sSup`/`sqrt`/`log` in the statement.

### Non-vacuity: Cobb–Douglas exchange economy (sanity tests §1)

Agents a with α_a in the open simplex and ω_a ≥ 0, where Σ_a ω_a = ω ≫ 0. Then
z_l(p) = Σ_a α_al (p·ω_a)/p_l − ω_l.

* (i) It is continuous on ℝ^L_{++}, because the denominators are positive.
* (iii) Σ_l p_l z_l = Σ_a (p·ω_a)Σ_l α_al − p·ω = 0.
* (iv) z_l ≥ −ω_l, so s = max_l ω_l + 1 works uniformly.
* (v) Take p̄ ≥ 0 with p̄ ≠ 0 and p̄_l = 0. Then p̄·ω > 0 because ω ≫ 0, so some agent has p̄·ω_a > 0. Since α_al > 0, z_l(pⁿ) ≥ α_al(pⁿ·ω_a)/pⁿ_l − ω_l → +∞. This holds even when the individual endowments are on the boundary. (The concrete instance uses 2 agents and 3 goods, with ω = (1,1,0), (0,0,1).)
* The theorem then returns p ≫ 0, and p = (1,1,1) does clear the market.

The repository's own instance `AggregationExamples.zCD` = (p₁/p₀ − 1, p₀/p₁ − 1), which is 2 agents with Cobb–Douglas ½–½ and endowments e₁, e₂ (scaled by 2), also satisfies all hypotheses. I checked by hand: Walras holds; z_l > −1; if p̄₀ = 0 then p̄₁ > 0, so p₁/p₀ → ∞.

### Triviality checks

* z ≡ 0 with ≥ 2 goods: it fails `BoundaryCondition` (§3). The hypotheses are not satisfied by junk objects.
* One good: `BoundaryCondition` is vacuous (§4), and Walras forces z ≡ 0 on ℝ_{++}. The conclusion is then correct for economic reasons, and this matches MWG.
* Hypotheses are not contradictory: see the Cobb–Douglas instance.

### Is anything assumed that MWG proves?

No. Continuity, Walras, the lower bound and the boundary condition are exactly the hypotheses of 17.C.1. The economic content (Brouwer/KKM via GND on the shrunk simplex, then the limit ε → 0 using (iv) and (v)) has to be proved.

## Non-faithful / gap items

### G1 (WEAK, coverage): the economy-level half of MWG 17.C.1 and Prop. 17.B.2 are missing

MWG 17.C.1 continues: "Hence, a Walrasian equilibrium exists in any pure exchange economy in which Σω_i ≫ 0 and every consumer has continuous, strictly convex, and strongly monotone preferences." This relies on 17.B.2: such an economy's excess demand satisfies (i)–(v), including the boundary condition, which is the nontrivial part. In the inputs:

* No theorem constructs a demand selection for an `ExchangeEconomy` with strictly convex, strongly monotone, continuous preferences and shows that `E.excessDemand d` satisfies `ExcessBoundedBelow` and `BoundaryCondition`.
* No theorem composes `exists_equilibrium_of_boundaryCondition` with `ExchangeEconomy.isWalrasianEquilibrium_of_excessDemand_eq_zero` (GE/Existence.lean) to get `∃ p ≫ 0, ∃ x, E.IsWalrasianEquilibrium p x`.
* The only economy-level existence results (`exists_freeDisposalEquilibrium`, `...'`) give free-disposal equilibria on the closed simplex and assume continuity of demand on the closed simplex. That assumption fails for strongly monotone preferences at boundary prices (demand is unbounded), so it does not cover the standard MWG/JR case either.
* The instance `zCD` is a hand-typed formula, not derived from `ExchangeEconomy`/`demand`.

Suggested addition: `ExchangeEconomy.exists_walrasianEquilibrium` with the MWG 17.C.1 hypotheses, plus a lemma corresponding to MWG 17.B.2 / JR Thm 5.3.

### D1 (documented deviation, benign): homogeneity dropped

This is not an error, because the statement is strictly more general and true. A reader might expect it to be listed, though. A non-homogeneous z satisfying every hypothesis is in sanity test §2 (`zNH = (1 + 1/(1+p₀²))·zCD`).

## Minor notes

* `ExcessBoundedBelow` allows s ≤ 0. That is a stronger condition when it holds, and it is harmless.
* `BoundaryCondition` does not require p̄ ≥ 0, but this is automatic because every pⁿ ≫ 0.
* Context file `Bridges/Aggregation/GrossSubstitutes.lean` places `PositivePrices` in a section with `[DecidableEq ι]`. The variable is unused in the body, so it is not included and is harmless.
