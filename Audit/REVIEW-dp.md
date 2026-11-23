# Review record: dynamic programming foundations, M5 / F8–F9 (2026-11-23)

Files: `EconLean/Macro/DP/{Blackwell,SequenceProblem,Bellman,Concavity,BrockMirman,Examples}.lean`.
Frozen statements: `EconLean/Audit/Statements/DP.lean`.

## Step 1: context-isolated adversarial review
Reviewer saw only the statements and definitions (proofs and comments stripped); reference
Stokey–Lucas (SL) Thms 3.2–3.3, 4.2–4.11, 4.15 and the Brock–Mirman closed form.
Result: **no PROBLEM-level findings**; every hypothesis bundle satisfiable, no junk-value conclusions.

| Declaration | Verdict |
|---|---|
| `blackwell`, `blackwell_fixedPoint` (SL 3.2–3.3) | faithful (on `X →ᵇ ℝ`; discrete topology recovers `B(X)`) |
| `IsFeasiblePlan`, `partialPayoff`, `payoff` (summable for feasible plans) | faithful |
| `IsOptimalValue` | faithful with deviation: requires attainment (now documented; `IsOptimalValue.unique` added) |
| `IsOptimalPlan` | faithful (catching-up criterion; equals SL optimality when payoffs converge) |
| `verification` (SL 4.3/4.4), `verification_of_lowerBound` | faithful / sound generalization (lower-bound variant handles log utility) |
| `euler_transversality` (SL 4.15) | faithful generalization (supergradient on the graph) |
| `DynProg`, `bellmanOp`, `bellman_equation`, `value_unique`, `iterate_converges` (SL 4.6) | faithful; deviation: `F` continuous on `X × X` (documented) |
| `policy`, `mem_policy_iff`, `policy_nonempty_compact_uhc`, `continuous_policy_of_singleton` | faithful |
| `principle_of_optimality`, `isOptimalValue_value` (SL 4.2–4.5) | faithful, bounded case only (documented) |
| `value_monotone`, `value_strictMono` (SL 4.7) | faithful |
| `ConvexGraph`, `StrictlyConcaveReturn`, `value_strictlyConcave`, `exists_continuous_policy` (SL 4.8) | faithful |
| `hasDerivAt_of_concaveOn_of_le` (SL 4.10) | faithful generalization (W need not be concave), 1-D |
| `DynProg.hasDerivAt_value` (SL 4.11) | faithful with deviation: 1-D; `hloc` replaces `g(x₀) ∈ int Γ(x₀)` (weaker) |
| `BrockMirman.Γ/F/A/B/V/g`, `brockMirman_value` | faithful; feasible set excludes `c = 0`, avoiding `log 0 = 0` junk |
| `brockMirman_optimal_of_euler` (was `brockMirman_euler`) | faithful |

Fixes applied after review: attainment documented and `IsOptimalValue.unique`,
`IsOptimalValue.tendsto_of_isOptimalPlan` added; `brockMirman_value` now also states the policy
plan's payoffs converge to `V(k₀)`; Euler equation and TVC stated as lemmas
(`brockMirman_euler_equation`, `brockMirman_transversality`) and the duplicate-named theorem renamed;
deviations (F continuity on X×X, bounded-only principle of optimality, strict concavity reused in B–S)
documented in file headers.

Open (not done): SL 4.2/4.4 in full generality (Assumptions 4.1–4.2, extended reals); SL 4.9
(approximate policies); multi-dimensional Benveniste–Scheinkman; a lemma deriving `hloc` from
`g(x₀) ∈ int Γ(x₀)` for interval-valued Γ; uniqueness of the Brock–Mirman policy; F14 (linear
difference systems, Blanchard–Kahn).

## Step 2: proof checks
- `#print axioms` on 24 headline declarations: only `propext, Classical.choice, Quot.sound`. No sorry.
- `leanchecker`: passes on all 7 modules (one module per call).
- `nanoda_bin` 0.4.17 on a `leanexport` of the headline declarations: 19,985 declarations, no
  typechecker errors (one pretty-printer message, "Unable to print axioms", not a check failure).
- Comparator stand-in: `Audit/Statements/DP.lean` restates the headlines verbatim, closed by the library.
- Full `lake build` warning-free.
