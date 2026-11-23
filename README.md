# EconLean

A learning project: formalizing canonical microeconomic theory in Lean 4 with
Mathlib. Every file is heavily commented for readers who know the economics
(MWG / Kreps level) but are new to Lean.

- `EconLean/Preferences/Basic.lean`: rational preferences, ≻ and ∼, MWG 1.B.1
- `EconLean/Preferences/Utility.lean`: utility representations, ordinal
  invariance, existence on finite sets
- `EconLean/Consumer/Budget.lean`: prices, cost, budget sets (convex, compact)
- `EconLean/Consumer/Demand.lean`: Walrasian demand, Walras' law, existence
- `EconLean/Consumer/Duality.lean`: indirect utility, expenditure, Hicksian
  demand, UMP/EMP duality
- `EconLean/Consumer/Envelope.lean`: Shephard's lemma, Roy's identity, Slutsky equation
- `EconLean/Consumer/RevealedPreference.lean`: WARP, compensated law of demand
- `ROADMAP.md`: what comes next, and related projects

## Blueprint: human-readable proofs
Every Lean theorem has a matching human-readable proof in the blueprint, written
to follow the Lean proof step by step and linked to it with `\lean{...}`.

- Web: https://geometrikz.github.io/econlib/blueprint/ (with dependency graph)
- PDF: https://geometrikz.github.io/econlib/blueprint.pdf
- Source: [`blueprint/src/chapters/`](blueprint/src/chapters), one file per area.
  How to add an entry: [`blueprint/README.md`](blueprint/README.md).
- [`docs/math_companion.md`](docs/math_companion.md): a Markdown companion for
  the consumer theory chapters, with a Mermaid dependency graph.

GitHub Actions builds the blueprint (web and PDF), checks that every `\lean{...}`
name exists (`lake exe checkdecls blueprint/lean_decls`), builds the API docs and
publishes them to GitHub Pages on every push to `main`. To build locally (optional):
```
pip install leanblueprint   # also needs graphviz and a TeX distribution with xelatex
leanblueprint web && leanblueprint serve
leanblueprint pdf
```

## Build
```
lake exe cache get   # downloads prebuilt Mathlib
lake build
```
Pinned to Lean v4.36.0 and Mathlib v4.36.0.
