# Review record: behavioral round 7 (2026-11-23)

Modules: `Behavioral/LimitedAttention` (sufficiency section),
`Behavioral/MultiplierPreferences`, `BoundedRationality/NoRegret`,
`BoundedRationality/ESS`. Frozen statements:
`Audit/Statements/BehavioralVII.lean` (31 theorems).

## Step 1: adversarial statement review

An isolated reviewer read the stripped statements against
Masatlioglu–Nakajima–Ozbay (2012), Hansen–Sargent (2001, 2008) and
Maccheroni–Marinacci–Rustichini (2006), Hart–Mas-Colell (2000) /
Foster–Vohra (1997), and Maynard Smith–Price (1973) / Weibull (1995). It
checked the WARP(LA), revealed-preference and attention-filter definitions,
the Gibbs variational formula (full support needed, normalization of `p` not
needed), the regret definitions and their signs, the quantifier order in the
invasion-barrier characterization (`ε̄` chosen after the mutant `y`), the
Hawk–Dove matrix and the second-order ESS condition at `V/C`.

No major issues. Minor issues and resolutions:

1. `IsCLA` ranks by an injective `X → ℕ`, narrowing the model on infinite
   `X`. **Documented** (already in the header; MNO take `X` finite and
   sufficiency assumes `[Fintype X]`).
2. `revealedAttention` was defined but unused in statements. **Fixed:**
   `cla_of_warpLA` now states `∃ u, IsCLA c u (revealedAttention c)`, i.e.
   MNO's own construction is an attention filter that represents `c`.
3. MNO identification of revealed attention / "iff" form of Theorem 2 not
   stated. **Documented** (`revPref_ranked` is the soundness half).
4. Full support of the reference model is necessary (Lean's `log 0 = 0`
   makes `kl` finite off support). **Documented** in the header.
5. Limits `θ → 0, ∞` and representation over acts not stated. **Documented**
   as out of scope.
6. "Internal regret" is pairwise, not swap regret. **Fixed** in the header
   and blueprint (swap regret can be `|S i|` times larger).
7. Limit theorems are about convergent sequences, and regret matching itself
   is not formalized. **Documented** (header already says the convergence of
   regret matching is not formalized; the limit theorem is called "the
   deterministic step").
8. Invasion barrier depends on the mutant. **Fixed** in docs (uniform-barrier
   version not stated).
9. `mix` clashed with VNM's `mix`. **Fixed:** renamed `hdMix`,
   `hdMix_surj`.

## Step 2: mechanical checks

- Full `lake build EconLean` against the shared tree as of 2026-11-23
  ~20:30 UTC (7,342 jobs): success, no warnings.
- `#print axioms` on 99 declarations (68 library + 31 frozen): only
  `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker`: all 4 modules and `Audit.Statements.BehavioralVII` pass.
- `leanexport` + `nanoda` on the 31 frozen theorems: 17,573 declarations, no
  typechecker errors (usual single "Unable to print axioms" pretty-printer
  message).
- `leanblueprint pdf` and `web` build; every `\lean{}` name in
  `behavioral.tex` (466) resolves.
