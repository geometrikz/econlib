# Review record: Gilboa–Schmeidler, stochastic choice, networks, persuasion, existence (2026-11-23)

Files:
- `EconLean/Behavioral/GilboaSchmeidler.lean`
- `EconLean/Behavioral/StochasticChoice.lean`
- `EconLean/Networks/KeyPlayer.lean`
- `EconLean/Information/Persuasion.lean`
- `EconLean/BoundedRationality/Existence.lean`

Frozen statements: `EconLean/Audit/Statements/ModernMicro.lean` (36 headline theorems).
Blueprint: `behavioral.tex` (§ Gilboa–Schmeidler, stochastic choice), `bounded_rationality.tex` (§ existence),
new `networks.tex` and `information.tex`. Every theorem in these files has a `\lean` entry; all names resolve;
`leanblueprint pdf` and `leanblueprint web` build with no LaTeX errors.

## Step 1: context-isolated adversarial review

The reviewer saw only statements and definitions (proofs stripped) plus the sources: Gilboa–Schmeidler 1989,
Luce 1959, Block–Marschak 1960, Ballester–Calvó-Armengol–Zenou 2006, Kamenica–Gentzkow 2011,
McKelvey–Palfrey 1995, Esponda–Pouzo 2016. No blocking problems. Fixes:

| Finding | Fix |
|---|---|
| `gilboa_schmeidler` named "Theorem 1" but GS also prove uniqueness of the set of priors | Added `eq_priorSet` (a closed convex representing set equals `priorSet I`, by separation) and `gilboa_schmeidler_unique`. Necessity is `gsAxioms_of_isMaxminFunctional`. |
| Utility acts range over all of `ℝ^S` | Documented (GS allow a bounded utility range). |
| `softmax_eq_luce`: λ convention | Documented: `Logit.softmax` uses temperature `exp(v/λ)`, QRE uses precision `exp(λU)`; at `λ = 0` both sides use `v/0 = 0`. |
| Networks: no worked numbers; reduced-game equilibrium not tied to the key-player aggregate; `Dominant` stronger than `φρ(G) < 1` | Added `leontief_pair`, `pair_numbers` (`b = (2,2)`, aggregate 4, intercentrality 3, aggregate 1 after removal), `Dominant.remove`, `isNash_remove`. `Dominant` documented as a sufficient condition. |
| Persuasion: attainment of `V` (KG Cor. 2 optimal signal) not stated; `v̂` abstract | Documented as not formalized. |
| `exists_isBerkNash` scope | Labelled the finite-Θ, full-support special case of EP Theorem 1. |

A second pass on the new declarations found no remaining problems.

## Step 2: mechanical checks

- `lake build` of all five modules and the frozen statements file: no errors, no warnings, no `sorry`.
- `#print axioms` on all 143 theorems (library + frozen): each uses only `propext`, `Classical.choice`,
  `Quot.sound`. This includes the existence theorems, which use the vendored Brouwer/Kakutani in
  `Foundations/FixedPoint`.
- `leanchecker` on each of the six modules: exit 0.
- `nanoda_bin` 0.4.17 on a `leanexport` of all 143 theorems: 33,154 declarations, no typechecker errors
  (one pretty-printer message, "Unable to print axioms", not a check failure).

## Open items (not formalized)

- GS Lemma 3.1 (vN–M step) and the bounded-utility-range case.
- Falmagne's theorem (nonnegative BM polynomials ⇒ RUM); McFadden's logit-from-Gumbel.
- BCZ with global substitutability (`γ > 0`) and the spectral condition `φρ(G) < 1`.
- KG: existence of an optimal signal; the receiver's problem behind `v̂`.
- Esponda–Pouzo with compact Θ and infinite KL.
- Raised by the independent review of round 1 and 2 files: Kőszegi–Rabin `D` not required to be probability
  vectors and PPE existence assumed; Matějka–McKay Corollary 1 (symmetric prior ⇒ uniform marginal) and
  existence of an optimal RI rule.
