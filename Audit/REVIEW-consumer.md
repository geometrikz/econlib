# Adversarial statement review log

Step 1 of the verification protocol (`verify/README.md`, PLAN.md §5). Each
review is done by a fresh, context-isolated agent that sees only the
statement files (proofs and comments stripped) and the textbook.

## 2026-11-23: Preferences/ and Consumer/ (MWG ch. 1–3), 68 theorems

**Result: no false statement and no vacuous theorem found.** Every hypothesis
set was met by a concrete two-good example. The problems are theorems that are
weaker than the textbook, one definition that is stronger than the textbook,
and two definitions with junk values that current theorems avoid.

Confirmed in Lean (`EconLean/Audit/ConsumerFindings.lean`, sorry-free):
- F1, F2: `expenditure` and `indirectUtility` return the junk value 0 when the
  utility level is unreachable or the budget set is empty or unbounded.
- F3: `ConvexPref` is **stronger than MWG Def. 3.B.4** (counterexample proved),
  so `convex_demand` covers fewer preferences than Prop. 3.D.2(iii). *Fix needed.*
- F4: `slutsky` is a chain-rule lemma about arbitrary functions; the duality
  identity and Shephard's lemma are hypotheses. *Restate for the actual
  `demand`/`hicksian`/`expenditure`, or rename and document it as a lemma.*
- F5: the compensated law of demand is the WARP hypothesis rewritten; only
  one direction of MWG Prop. 2.F.1 is stated.
- F6: local nonsatiation is satisfiable (linear utility), so Walras' law, Roy
  and duality are not vacuous.

Checked and dismissed: the reviewer flagged `import Mathlib.Basic.Real.Basic`
as a possible typo. That module exists in Mathlib v4.36 and the build passes.

Verdicts by the plan's scale (faithful / faithful with documented deviation /
wrong):
- **Wrong (blocks freezing):** `ConvexPref` (F3); `slutsky` as a statement of
  MWG 3.G.3 (F4).
- **Faithful with documented deviation:** `shephard`, `roy` (assume
  differentiability, MWG derives it); `indirectUtility_mono` (weak, not strict);
  `expenditure_concave` (pointwise, not `ConcaveOn`); `expenditure_smul`
  (has an unneeded hypothesis); `compensated_law_of_demand` (one direction);
  `demand_nonempty` (continuity on all of ℝⁿ).
- **Faithful:** everything else (45 declarations).

The reviewer's full report follows unchanged.

---

# Adversarial statement review: EconLean (MWG ch. 1–3, consumer theory)

Scope: the 7 files under `review_in/EconLean/` (proofs replaced by `sorry`). I checked statements and
definitions only, against Mas-Colell, Whinston & Green (MWG), ch. 1–3. Lean was not available, so
everything below comes from reading Lean/Mathlib semantics by hand.

**Overall verdict.** None of the statements looks false. I found no theorem whose hypotheses
contradict each other: every hypothesis set can be met by a concrete 2-good Cobb–Douglas or linear
example (see §3). The problems are of four kinds:

* **(a) Assumed instead of proved:** the "big" results (Shephard, Roy, Slutsky) take as hypotheses things
  the textbook proves, such as differentiability. Slutsky is a chain-rule lemma about arbitrary functions.
* **(b) Weaker conclusions:** monotonicity is weak rather than strict, and there are one-directional
  versions of iff results.
* **(c) Junk values:** `sSup`/`sInf` return junk in places the theorems carefully avoid. Any later user of these
  definitions will hit them, though.
* **(d) Coverage gaps:** large parts of MWG ch. 1–3 are not stated at all (choice structures, 3.C.1,
  3.D.3/3.E.2 monotonicity parts, 3.E.4, 3.G.2, the Slutsky matrix, integrability, welfare, SARP).

## 1. Summary table

| # | Declaration | File | MWG reference | Verdict | Reason |
|---|---|---|---|---|---|
| 1 | `P`, `I` | Preferences/Basic | Def 1.B.1 (strict pref., indifference) | OK | Textbook definitions |
| 2 | `Rational` | Preferences/Basic | Def 1.B.1 | OK | complete + transitive; reflexivity derived |
| 3 | `Rational.refl` | Preferences/Basic | remark after 1.B.1 | OK | |
| 4 | `Rational.P_iff_not` | Preferences/Basic | standard | OK | uses completeness correctly |
| 5 | `P_irrefl` | Preferences/Basic | Prop 1.B.1(i) | OK | |
| 6 | `P_trans` | Preferences/Basic | Prop 1.B.1(i) | OK | needs only transitivity (correct) |
| 7 | `P_of_P_of_R`, `P_of_R_of_P` | Preferences/Basic | Prop 1.B.1(iii) | OK | |
| 8 | `Rational.I_equivalence` | Preferences/Basic | Prop 1.B.1(ii) | OK | |
| 9 | `Rational.isPreorder` | Preferences/Basic | – | OK | bridge to Mathlib |
| 10 | `Rational.trichotomy` | Preferences/Basic | standard | OK | |
| 11 | `Represents` | Preferences/Utility | Def 1.B.2 | OK | `R x y ↔ u y ≤ u x` is the right orientation |
| 12 | `Represents.rational` | Preferences/Utility | Prop 1.B.2 | OK | |
| 13 | `Represents.P_iff` | Preferences/Utility | standard | OK | |
| 14 | `Represents.comp_strictMono` | Preferences/Utility | remark after Def 1.B.2 | OK (narrow) | converse (uniqueness up to monotone transform) missing |
| 15 | `prefOf`, `represents_prefOf` | Preferences/Utility | – | OK | |
| 16 | `lowerContour`, `countingUtility`, `lowerContour_subset` | Preferences/Utility | Ex. 1.B.5-style construction | OK | |
| 17 | `exists_utility_of_finite`, `rational_iff_exists_utility` | Preferences/Utility | Prop 1.B.2 + finite-X existence | OK / WEAK | finite only; **Prop 3.C.1 (Debreu, continuous representation) absent** |
| 18 | (import) `Mathlib.Basic.Real.Basic` | Preferences/Utility | – | SUSPICIOUS (build) | Mathlib's module is `Mathlib.Data.Real.Basic`; check that the stripped copy matches the source |
| 19 | `cost` + 9 algebra/topology lemmas | Consumer/Budget | – | OK | all true unconditionally |
| 20 | `budgetSet` | Consumer/Budget | Def 2.D.1 | OK | no `p ≫ 0, w ≥ 0` built in; lemmas add them where needed |
| 21 | `budgetSet_smul`, `zero_mem_budgetSet`, `convex_budgetSet`, `isClosed_budgetSet` | Consumer/Budget | §2.D | OK | |
| 22 | `le_div_of_mem_budgetSet`, `isCompact_budgetSet` | Consumer/Budget | §2.D / used in 3.D.1 | OK | |
| 23 | `demand` | Consumer/Demand | §3.D (UMP solution set) | OK | Set-valued; may be empty |
| 24 | `demand_smul` | Consumer/Demand | Prop 3.D.2(i) | OK | |
| 25 | `LocallyNonsatiated` | Consumer/Demand | Def 3.B.3 | OK | restricted to orthant, sup-metric (equivalent) |
| 26 | `exists_better_affordable` | Consumer/Demand | lemma for 3.D.2(ii) | OK | |
| 27 | `walras_law` | Consumer/Demand | Prop 3.D.2(ii) | OK | does not even need rationality; correct |
| 28 | `StronglyMonotone` | Consumer/Demand | Def 3.B.2 | OK | (weak "monotone", y ≫ x ⇒ y ≻ x, is not defined) |
| 29 | `StronglyMonotone.locallyNonsatiated` | Consumer/Demand | remark after 3.B.3 | OK | |
| 30 | `demand_nonempty` | Consumer/Demand | Prop 3.D.1 | WEAK (minor) | asks for `u` continuous on all of ℝ^ι, not just on ℝ^L_+ |
| 31 | `ConvexPref` | Consumer/Demand | Def 3.B.4 | **MISMATCH (stronger)** | upper contour sets must be convex in all of ℝ^ι, for x outside the orthant as well |
| 32 | `convex_demand` | Consumer/Demand | Prop 3.D.2(iii) | WEAK | hypothesis stronger than textbook (via #31); uniqueness under strict convexity missing |
| 33 | `indirectUtility` | Consumer/Duality | Def §3.D | VACUOUS-RISK (def) | `sSup` junk = 0 when `w < 0`, when some `p_i ≤ 0` (unbounded), or when `u` is unbounded |
| 34 | `upperSet`, `hicksian` | Consumer/Duality | §3.E | OK | |
| 35 | `expenditure` | Consumer/Duality | Def §3.E | VACUOUS-RISK (def) | `sInf ∅ = 0`: unattainable ū gets expenditure 0; nonpositive prices also give 0 |
| 36 | `indirectUtility_eq` | Consumer/Duality | v(p,w) = u(x(p,w)) | OK | true with no hypotheses |
| 37 | `expenditure_eq` | Consumer/Duality | e(p,ū) = p·h(p,ū) | OK | |
| 38 | `exists_cheaper_above` | Consumer/Duality | lemma for 3.E.1/3.E.3 | OK | |
| 39 | `demand_subset_hicksian` | Consumer/Duality | Prop 3.E.1(i) | OK | |
| 40 | `expenditure_indirectUtility` | Consumer/Duality | eq. (3.E.1), e(p,v(p,w)) = w | OK | w = 0 case also correct |
| 41 | `utility_eq_of_mem_hicksian` | Consumer/Duality | Prop 3.E.3(iii) ("no excess utility") | OK | |
| 42 | `hicksian_subset_demand` | Consumer/Duality | Prop 3.E.1(ii) | OK | |
| 43 | `hicksian_nonempty` | Consumer/Duality | existence in EMP (§3.E) | OK | |
| 44 | `indirectUtility_expenditure` | Consumer/Duality | eq. (3.E.2), v(p,e(p,ū)) = ū | OK | |
| 45 | `indirectUtility_smul` | Consumer/Duality | Prop 3.D.3(i) | OK | |
| 46 | `indirectUtility_mono` | Consumer/Duality | Prop 3.D.3(ii) | **WEAK** | only *weakly* increasing in w; strict increase, nonincreasing in p, quasiconvexity (iii) and continuity (iv) missing |
| 47 | `hicksian_smul` | Consumer/Duality | Prop 3.E.3(i) | OK | convexity/uniqueness (3.E.3(ii)) missing |
| 48 | `expenditure_smul` | Consumer/Duality | Prop 3.E.2(i) | WEAK (harmless) | needless hypothesis `x ∈ hicksian`; true unconditionally (`Real.sInf_smul_of_nonneg`) |
| 49 | `expenditure_concave` | Consumer/Duality | Prop 3.E.2(iii) concavity | WEAK | true, and even superadditive, but guarded by minimizers existing at 3 price vectors; not `ConcaveOn`; strict increase in ū (3.E.2(ii)) and nondecreasing in p missing |
| 50 | `costCLM`, `costCLM_apply`, `cost_single`, `eventually_pos` | Consumer/Envelope | – | OK | |
| 51 | `expenditure_le` | Consumer/Envelope | – | OK | |
| 52 | `shephard`, `shephard_partial` | Consumer/Envelope | Prop 3.G.1 | **WEAK** | **assumes** e is differentiable at p; MWG concludes differentiability (from strict convexity / single-valued h) |
| 53 | `hicksian_unique` | Consumer/Envelope | converse remark to 3.G.1 (3.F) | OK | nice; not in MWG verbatim |
| 54 | `le_indirectUtility` | Consumer/Envelope | – | OK | |
| 55 | `roy`, `roy_partial` | Consumer/Envelope | Prop 3.G.4 | WEAK | correct sign and form; **assumes** v is differentiable |
| 56 | `slutsky` | Consumer/Envelope | Prop 3.G.3 | **WEAK / MISMATCH in spirit** | about *arbitrary* functions X, H, E; duality identity and Shephard are hypotheses; no link to `demand`/`hicksian`/`expenditure` |
| 57 | `warp_of_unique_demand` | Consumer/RevealedPreference | Def 2.F.1 applied to rational demand (cf. §3.J / Prop 1.D.1) | OK | |
| 58 | `WARP` | Consumer/RevealedPreference | Def 2.F.1 | OK | w ≥ 0 rather than w > 0 (harmless) |
| 59 | `warp_of_rational` | Consumer/RevealedPreference | §3.J opening claim | OK | hypothesis satisfiable (Cobb–Douglas) |
| 60 | `compensated_law_of_demand` (+`_strict`) | Consumer/RevealedPreference | Prop 2.F.1 | **WEAK** | only the WARP ⇒ CLD direction, for one pair, with no demand function; the conclusion is 3 lines of algebra from `hwarp`; the converse (the substantive direction of 2.F.1) is missing |

Counts: 60 rows. OK: 45. WEAK: 11 (#17, 30, 32, 46, 48, 49, 52, 55, 56, 60; #14 is narrow but OK).
MISMATCH: 1 (#31). VACUOUS-RISK on definitions: 2 (#33, #35). Build-level SUSPICIOUS: 1 (#18).
**No theorem looks false, and none has contradictory hypotheses.**

## 2. Detailed findings (non-OK items)

### 2.1 `slutsky` is a chain-rule lemma, not the Slutsky equation for the model (#56). Highest severity.

```lean
theorem slutsky {X : (ι → ℝ) × ℝ → (ι → ℝ)} {H : (ι → ℝ) → (ι → ℝ)} {E : (ι → ℝ) → ℝ} ...
    (hdual : ∀ᶠ q in 𝓝 p, H q = X (q, E q)) ... (hshep : ∀ δ, E' δ = cost δ (H p)) :
    ∀ δ, H' δ = X' (δ, 0) + cost δ (H p) • X' (0, 1)
```

* X, H, E are *arbitrary* functions. Nothing ties them to `demand`, `hicksian` or `expenditure` from a
  utility `u`. Both economic inputs are assumed: the duality identity h(p,ū) = x(p, e(p,ū)) (`hdual`) and
  Shephard's lemma (`hshep`). What remains is (H)' = (X ∘ (id, E))' = X'(·,0) + E'(·)·X'(0,1).
* Sanity instance: X ≡ 0, H ≡ 0, E ≡ 0, all derivatives 0. Every hypothesis holds and the theorem says
  0 = 0 (see `sanity_tests.lean`, test S8). With a nonzero `E` the `hshep` hypothesis is the only
  "economics" left.
* What the formula gets right: with δ = e_k, `H' e_k = X'(e_k,0) + h_k · X'(0,1)`, i.e.
  ∂h_ℓ/∂p_k = ∂x_ℓ/∂p_k + x_k ∂x_ℓ/∂w at w = e(p,ū). The sign and orientation are correct.
* **To be MWG 3.G.3** the theorem needs: (i) `X`, `H`, `E` taken to be selections with `demand (prefOf u) q w = {X (q,w)}`,
  `hicksian u q ū = {H q}`, `E q = expenditure u q ū`; (ii) `hdual` *derived* from
  `hicksian_subset_demand` + `expenditure_eq` (both already exist); (iii) `hshep` derived from
  `shephard`. Without a "glue" theorem, the formalization does not show that the model's demand satisfies Slutsky.
* Also missing: Prop 3.G.2 (D_p h symmetric, negative semidefinite, D_p h · p = 0) and the corollary
  that the Slutsky matrix S(p,w) is symmetric NSD. That is the main *content* of §3.G. Nothing
  about a Slutsky matrix appears at all.

### 2.2 `shephard`, `roy`: differentiability is assumed (#52, #55)

`shephard` takes `hE : HasFDerivAt (fun q => expenditure u q ū) E' p` as a hypothesis and only identifies
the derivative. MWG Prop 3.G.1 assumes u continuous, LNS and *strictly convex*, and *concludes* that
e(·,ū) is differentiable with gradient h(p,ū). The same holds for `roy` (MWG 3.G.4 derives Roy from 3.G.1 and
duality, with differentiability of v following from the assumptions there).

* The envelope argument used here is a legitimate textbook *variant* (Varian/Jehle–Reny prove Shephard via
  "q·h − e(q) has a local min at p"). But as a formalization of "MWG 3.G.1" it is the weaker half.
* Hypotheses are satisfiable. Example: u(x) = √x₁·√x₂, ū = 1, e(p,1) = 2√(p₁p₂), smooth at p ≫ 0, so not vacuous.
* `roy` statement check: `V'(δ, δ·x) = 0 ∀δ` ⟺ ∂v/∂p_ℓ + x_ℓ ∂v/∂w = 0 ∀ℓ. Correct.
  `roy_partial`: x_j = −V'(e_j,0)/V'(0,1), with the division guarded by `hw`. Correct.
* `hicksian_unique` (e differentiable ⇒ h single-valued) is a nice true corollary. MWG has the
  converse (strict convexity ⇒ unique h ⇒ differentiability), and that converse is the missing piece.

### 2.3 `compensated_law_of_demand` (+strict) is one direction of Prop 2.F.1, for one pair, with the WARP instance as a hypothesis (#60)

MWG Prop 2.F.1: *for x(p,w) homogeneous of degree 0 and satisfying Walras' law, x satisfies WARP **iff**
for every compensated price change, (p'−p)·(x(p',w')−x(p,w)) ≤ 0, strict when x(p,w) ≠ x(p',w').*

The Lean statement involves no demand function at all. It takes four vectors with
`cost p x = w`, `cost p' x' = w'`, `w' = cost p' x`, and the single instance of WARP for that pair. Then

(p'−p)·(x'−x) = p'·x' − p'·x − p·x' + p·x = w' − w' − p·x' + w = w − p·x',

and `hwarp` (whose premise `cost p' x ≤ w'` is automatically true by `hcomp`) gives `w < p·x'`. So the
theorem is the algebraic identity plus the hypothesis. Test S6 proves the identity directly.

* The **converse direction** (CLD for all compensated changes ⇒ WARP) is missing. MWG proves it by
  a continuity/homogeneity argument along a path of prices, and it is the substantive half.
* Prop 2.F.2 (WARP ⇒ Slutsky matrix NSD, v·S·v ≤ 0) and 2.F.3 (p·S = 0, S·p = 0) are absent.

### 2.4 `ConvexPref` is stronger than MWG Def 3.B.4 (#31, #32)

```lean
def ConvexPref (R : (ι → ℝ) → (ι → ℝ) → Prop) : Prop := ∀ x, Convex ℝ {y | R y x}
```

MWG: *for every x ∈ X = ℝ^L_+, {y ∈ X : y ≿ x} is convex.* Lean quantifies over **every x ∈ ℝ^ι**
and takes the upper contour set in **all of ℝ^ι**, including bundles with negative coordinates. Meanwhile
`LocallyNonsatiated` and `StronglyMonotone` *are* restricted to the orthant, so the file treats the
consumption set inconsistently.

Counterexample to "harmless": take u(x) = max(x₀,0) + max(x₁,0). This is the standard way to extend
the linear (perfect-substitutes) utility u(x)=x₀+x₁ from the orthant to ℝ². On ℝ²₊ the preference is
convex, but `ConvexPref (prefOf u)` fails: with x = (2,0), y = (2,−10) and z = (−10,2), we have u(y) = u(z) = 2 = u(x),
while the midpoint (−4,−4) has u = 0 < 2 (test S5).

The fix is either `∀ x, 0 ≤ x → Convex ℝ {y | 0 ≤ y ∧ R y x}` or carrying the consumption set
everywhere. `convex_demand` stays true under the textbook hypothesis, because only budget-set points matter.
Relatedly, **strict convexity** and **Prop 3.D.2 single-valuedness** (strictly convex ⇒ x(p,w) unique)
are missing. Single-valuedness is what makes `warp_of_rational`'s hypothesis `demand R p w = {x p w}`
dischargeable, and `slutsky` needs it as well.

Minor, same theme: `demand_nonempty`, and all of Duality and Envelope, ask for `Continuous u` on all of ℝ^ι.
This is not a real restriction, since one can precompose with the coordinatewise positive part, which is
continuous and the identity on the orthant. But it rules out writing `Real.log`-based utilities directly
(`Real.log 0 = 0` is junk and discontinuous).

### 2.5 Junk values in `indirectUtility` / `expenditure` (#33, #35)

* `indirectUtility u p w = sSup (u '' budgetSet p w)`:
  * w < 0 and p ≥ 0 makes the budget set empty, so v = `sSup ∅` = **0**. For u ≡ 5 we get v(1, −1) = 0 (test S2).
  * some p_i ≤ 0 makes the budget set unbounded, so for unbounded u, v = **0** (`Real.sSup_of_not_bddAbove`) (test S3).
  * `indirectUtility_smul` is stated for arbitrary p, w. It is true, but only because both sides are the
    same junk; it is fine.
* `expenditure u p ū = sInf (cost p '' upperSet u ū)`:
  * ū above sup u makes the upper set empty, so e = **0**. "Unattainable utility costs nothing" (test S1).
  * Some p_i < 0 makes cost unbounded below, so e = **0**.

All theorems I checked guard against these cases (`hp : ∀ i, 0 < p i`, existence of a Hicksian bundle,
`x ∈ upperSet`, `0 ≤ w`), and **no theorem is true *because of* a junk value**. I verified this for
`expenditure_smul`, `expenditure_concave`, `shephard` (near p, all q ≫ 0 and the upper set is nonempty), `roy`
and `indirectUtility_mono`. But any future theorem such as "e is strictly increasing in ū" or
"e is continuous" will be false as stated unless it restricts ū to the attainable range.

### 2.6 `indirectUtility_mono` is weaker than Prop 3.D.3(ii) (#46)

MWG 3.D.3(ii): v is *strictly increasing* in w and *nonincreasing* in p_ℓ, under LNS. Lean has only
weak monotonicity in w, with no LNS. This is the trivial direction (B(p,w) ⊆ B(p,w′)). Strict increase
(which needs LNS) and monotonicity in p are not stated. 3.D.3(iii) (quasiconvexity: {(p,w): v ≤ v̄} convex)
and (iv) (continuity) are absent.

### 2.7 `expenditure_concave`, `expenditure_smul` (#48, #49)

* `expenditure_concave` is correct and slightly stronger than MWG (a, b ≥ 0 arbitrary gives
  superadditivity + homogeneity, which is concavity on the cone). But it is conditioned on Hicksian bundles
  existing at p, q and ap + bq, and it is not packaged as `ConcaveOn ℝ {p | ∀ i, 0 < p i} (expenditure u · ū)`.
  Under continuity those hypotheses follow from `hicksian_nonempty`, so they can be discharged, but nobody has done so.
* Prop 3.E.2(ii) (e strictly increasing in ū) and (iii)'s "nondecreasing in p_ℓ" part are missing, as is
  (iv) continuity.
* `expenditure_smul` needs no hypothesis at all (`Real.sInf_smul_of_nonneg` and
  `cost (α•p) '' S = α • (cost p '' S)`). The `hx` hypothesis is harmless but makes the result look
  conditional when it isn't.

### 2.8 Import path `Mathlib.Basic.Real.Basic` (#18)

`Preferences/Utility.lean` imports `Mathlib.Basic.Real.Basic`. To my knowledge the module is
`Mathlib.Data.Real.Basic`. Either the review copy was altered during stripping, or the source does not build
as given. The latter would be serious, because then the "proved" status of everything downstream would be meaningless. Check with
`lake build` on the original.

### 2.9 Smaller points

* `comp_strictMono`: only "monotone transforms preserve representation". The converse (any two
  representations differ by a strictly increasing transform of the range) is not stated.
* `rational_iff_exists_utility` is for `Fintype X` only. Neither the countable case nor
  **Prop 3.C.1** (continuous rational preferences on ℝ^L_+ admit a continuous utility) appears, nor the
  lexicographic counterexample. The whole consumer-theory layer therefore *starts* from a utility `u`
  rather than from a preference `R` with properties, so ch. 3.C is effectively skipped.
* `WARP` uses `0 ≤ w` instead of MWG's `w > 0`. This is harmless, and at w = 0 demand is forced to 0.
* `LocallyNonsatiated` with empty `ι` is unsatisfiable (needs `P R 0 0`). It is consistent and harmless.
* Only `StronglyMonotone` is defined. MWG's weak `Monotone` (y ≫ x ⇒ y ≻ x), used in 3.C.1, is not.

## 3. Satisfiability check (no vacuous theorems found)

Running example: ι = Fin 2, u(x) = √x₀ · √x₁ (Real.sqrt, continuous on ℝ², equal to Cobb–Douglas ½,½ on
the orthant), p = (1,1).

| Theorem | Hypotheses | Satisfied by |
|---|---|---|
| `walras_law`, `demand_subset_hicksian`, `roy` | LNS(prefOf u) | u = x₀ + x₁ (strongly monotone ⇒ LNS). The Cobb–Douglas u is LNS too (increase both coords). |
| `demand_nonempty` | continuous, p ≫ 0, w ≥ 0 | any of the above |
| `utility_eq_of_mem_hicksian`, `hicksian_subset_demand`, `indirectUtility_expenditure` | u 0 ≤ ū, x ∈ hicksian | ū = 1, h = (1,1), u 0 = 0 |
| `warp_of_rational` | ∀ p ≫ 0, w ≥ 0, demand = {x p w} | Cobb–Douglas: x(p,w) = (w/2p₀, w/2p₁) is the unique maximizer (w = 0 gives {0}) |
| `shephard` | e(·,ū) differentiable at p | e(p,1) = 2√(p₀p₁) |
| `roy` | v differentiable at (p,w) | v(p,w) = w / (2√(p₀p₁)); ∂v/∂w ≠ 0 |
| `slutsky` | hdual, Shephard | Cobb–Douglas (and also, trivially, X=H=E=0) |
| `compensated_law_of_demand` | Walras, compensation, WARP-instance | any Cobb–Douglas pair |
| `convex_demand` | Rational, ConvexPref | linear u = x₀ + x₁ on all of ℝ² (but **not** its orthant-only extension, §2.4) |

## 4. Coverage gaps vs MWG ch. 1–3 (named topics not actually stated)

* **Ch. 1:** choice structures (Def 1.C.1), WARP for choice structures, Prop 1.D.1 (rational ⇒ WARP),
  Prop 1.D.2 (WARP + budget family containing all ≤3-element sets ⇒ rationalizable). None present.
  RevealedPreference.lean only has the Walrasian (ch. 2) version.
* **Ch. 2:** Euler/Cournot/Engel aggregation (Props 2.E.1–2.E.3); Prop 2.F.1 converse; 2.F.2 (Slutsky
  matrix NSD under WARP); 2.F.3; the fact that the WARP Slutsky matrix need not be symmetric.
* **Ch. 3.B/C:** weak monotonicity, strict convexity, homotheticity/quasilinearity (Defs 3.B.6–3.B.7),
  **Prop 3.C.1** (existence of continuous utility), and the lexicographic non-representability example.
* **Ch. 3.D:** single-valued demand under strict convexity (3.D.2(iii) second half), upper hemicontinuity /
  continuity of demand, Prop 3.D.3(ii)–(iv) (strict in w, nonincreasing in p, quasiconvex, continuous).
* **Ch. 3.E:** 3.E.2(ii) (strictly increasing in ū), monotone in p, continuity; 3.E.3(ii) (convex/unique h);
  **Prop 3.E.4 (compensated law of demand for h)**.
* **Ch. 3.F:** duality theorem (recovering preferences from e), support functions.
* **Ch. 3.G:** **Prop 3.G.2** (D_p h symmetric, NSD, D_p h·p = 0), the Slutsky matrix, a non-abstract 3.G.3,
  Prop 3.G.4 with differentiability derived.
* **Ch. 3.H–3.J:** integrability, welfare (CV, EV, Prop 3.I.1), Strong Axiom / Houthakker (Prop 3.J.1).

## 5. Ranked severity

1. `slutsky` is an abstract chain-rule lemma: no link to the model's demand, Hicksian demand or expenditure. Duality and Shephard are assumed.
2. The Slutsky/Hicksian substitution matrix properties (3.G.2, 2.F.2) are not stated anywhere, although they are the core of ch. 2.F / 3.G.
3. `compensated_law_of_demand` is one direction only, pointwise, and reduces to algebra on its WARP hypothesis. The substantive converse of 2.F.1 is missing.
4. `shephard` / `roy` assume differentiability that MWG derives, and the strict-convexity ⇒ unique-h/x results are missing.
5. `ConvexPref` quantifies over all of ℝ^ι, stronger than MWG and inconsistent with LNS/StronglyMonotone (counterexample in §2.4).
6. Import `Mathlib.Basic.Real.Basic` looks wrong, so the build status of the source needs checking.
7. `indirectUtility_mono` is only weak monotonicity in w. Strict increase, monotonicity in p, quasiconvexity and continuity are all missing.
8. Junk-value definitions (`sSup`/`sInf` = 0 on empty or unbounded sets) are safe in current theorems but are a trap for future ones (e.g. "e strictly increasing in ū" would be false as stated).
9. Prop 3.C.1 is absent, and the utility existence result is finite-X only. Consumer theory is built on a primitive `u`, not on preferences.
10. Ch. 1 choice-structure WARP (1.C–1.D), 3.E.4, 3.H–3.J and 2.E aggregation are absent.
