#!/usr/bin/env bash
# Machine half of the verification protocol (step 2). Run from the repo root.
#   1. Challenge drift: regenerate the statement files and fail if they differ
#      from the committed (reviewed) ones, or if a theorem is not yet listed.
#   2. lake check: export the library (with all of its Mathlib dependencies)
#      and replay it through Lean's kernel; fails on sorry or any axiom other
#      than propext / Quot.sound / Classical.choice.
#   3. lake comparator: every theorem in comparator.json proves exactly the
#      statement in challenge/ (a separate project with the same module names), with permitted axioms, kernel-accepted.
# With PARANOID=1, steps 2 and 3 also run every independent checker bundled
# with Lean (leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron).
# That replays ~340k declarations several times: about 35 min on 4 cores, and
# nanoda needs more than 16 GB of RAM. Run it nightly / before milestones.
# Needs bubblewrap (`bwrap`) with unprivileged user namespaces.
set -euo pipefail
FLAG=""; [ "${PARANOID:-0}" = 1 ] && FLAG="--paranoid"
cd "$(dirname "$0")/.."

echo "== 1/3 challenge drift"
python3 verify/make_challenge.py >/dev/null
if ! git diff --quiet --exit-code -- challenge comparator.json \
   || [ -n "$(git ls-files --others --exclude-standard challenge)" ]; then
  git --no-pager diff --stat -- challenge comparator.json
  echo "FAIL: theorem statements changed or were added without updating the reviewed challenge."
  echo "      Run the adversarial statement review on the changed statements, then commit the"
  echo "      regenerated challenge/ and comparator.json."
  exit 1
fi

echo "== 2/3 lake check $FLAG (kernel replay, axiom audit)"
lake check $FLAG

echo "== 3/3 lake comparator $FLAG (statements match the reviewed challenge)"
# The challenge is trusted (reviewed) input, so it is built and exported outside
# the sandbox; the export lists exactly the constants lake comparator expects.
NAMES=$(python3 -c 'import json;print(" ".join(json.load(open("comparator.json"))["theorem_names"]))')
EXTRA="propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
mkdir -p .lake
(cd challenge && lake build EconLean >/dev/null && lake env leanexport EconLean -- Quot Quot.mk Quot.lift Quot.ind $NAMES $EXTRA) > .lake/challenge.ndjson
lake comparator $FLAG --challenge-from-export .lake/challenge.ndjson

echo "ALL MACHINE CHECKS PASSED"
