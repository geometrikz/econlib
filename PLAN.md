# Conventions for EconLean / econlib

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

## Versions
Lean `v4.36.0`, Mathlib `v4.36.0` (see `lean-toolchain`, `lakefile.toml`).
