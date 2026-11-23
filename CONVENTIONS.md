# Coding conventions for EconLean (econlib)

Every contributor (human or Claude thread) follows these so the build stays
warning-free.

## File layout
- One topic per file under `EconLean/<Area>/<Topic>.lean`
  (e.g. `EconLean/Consumer/Demand.lean`).
- Add each new file to the root `EconLean.lean` as `public import ...`.
- Everything lives in `namespace Econ`.

## Lean module system (required)
Mathlib uses Lean's module system, and a file that imports Mathlib without it
gets a warning per import. Every file has this shape:

```lean
/-
# Title
Economics overview and textbook references (MWG §...).
-/
module

public import Mathlib.Some.File
public import EconLean.Some.Other

@[expose] public section

namespace Econ
...
end Econ
```

- `module` must come before any import (comments may precede it).
- Use `public import` for every import.
- `@[expose] public section` makes all declarations public, with definitions
  unfolded for downstream files, which is what a library like this wants.

## Style
- This is a learning project: comment the economics and the Lean (what a tactic
  does, why a hypothesis is needed). Cite the textbook result being formalized.
- State only the hypotheses a theorem actually uses.
- No `sorry` on `main`. Check new main theorems with `#print axioms`; only
  `propext`, `Classical.choice` and `Quot.sound` should appear.
- Import narrowly (specific Mathlib files, not `Mathlib`), which keeps builds fast.
- The build must finish with no warnings (`lake build`).

## Blueprint: a human proof for every theorem (required)
Every change that adds or changes a Lean theorem, lemma or definition that a
reader would cite also adds or updates its blueprint entry, in the same change.
Details and a template: `blueprint/README.md`.
- Put it in the area's file under `blueprint/src/chapters/` (one file per area;
  a new area gets a new chapter file and an `\input` line in `content.tex`).
- Tag it `\lean{Full.Lean.Name}` (several names allowed, comma separated),
  `\leanok` on the statement once it compiles, and `\leanok` inside the proof
  once it has no `sorry`. Give it a `\label` and list what it relies on in
  `\uses{...}`.
- The written proof follows the Lean proof step by step: same case splits,
  same intermediate claims in the same order, same lemmas (name them). If the
  Lean proof changes, update the text.
- State the same hypotheses as Lean. If the Lean statement is weaker or
  stronger than the textbook one, say so in a sentence.
- `Audit/` statement files are not blueprinted.
- CI fails if a `\lean{...}` name does not exist (`checkdecls`). Before handing
  off, run `leanblueprint web` (or ask the integrator) and fix any LaTeX errors.

## Versions
Lean `v4.36.0`, Mathlib `v4.36.0` (see `lean-toolchain`, `lakefile.toml`).

## Commits (so they count as geoff's and show "Verified")
- Author every commit as `geometrikz <33253415+geometrikz@users.noreply.github.com>`
  (e.g. `git commit --author="geometrikz <33253415+geometrikz@users.noreply.github.com>"`).
  That email is linked to github.com/geometrikz, so commits count as contributions.
- Commit and push only from the cloud integrator session, and leave the committer
  identity and signing at the environment defaults (committer
  `Claude <noreply@anthropic.com>`, SSH-signed). GitHub verifies that signature, so
  commits show "Verified". Never override `user.name`/`user.email` with `git -c`,
  never set `commit.gpgsign=false`, and never push unsigned commits from a laptop.
- CI (`.github/workflows/commit_check.yml`) fails if a pushed commit is unverified
  or has a different author email.
