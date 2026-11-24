/-
# The Boston (immediate acceptance) mechanism is manipulable and unstable

Abdulkadiroğlu and Sönmez (2003), §3; Ergin and Sönmez (2006). Students report rank-order
lists of schools; each school (one seat here) has a strict priority order over students. The
**Boston mechanism** runs in rounds: in round `k` every still unassigned student applies to the
`k`-th school on her list; a school whose seat is still free admits its highest-priority
applicant of that round, permanently.

* `bostonRound`, `boston`: the mechanism, as a computable function.
* `boston_manipulable`: a three-student example in which a student obtains a school she
  strictly prefers by misreporting her ranking (truth-telling is not a dominant strategy,
  in contrast with student-proposing deferred acceptance, `daMatching_strategyproof`).
* `boston_not_stable`: in the same example, the truthful Boston outcome has **justified
  envy**: a student prefers another student's school and has higher priority there.
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace Econ

variable {n m : ℕ}

/-- One round (`k`) of the Boston mechanism, applied to the current assignment `μ`.
`pref s` is student `s`'s reported list, `prio c` school `c`'s priority list. -/
def bostonRound (pref : Fin n → List (Fin m)) (prio : Fin m → List (Fin n)) (k : ℕ)
    (μ : Fin n → Option (Fin m)) : Fin n → Option (Fin m) := fun s =>
  match μ s with
  | some c => some c
  | none =>
    match (pref s)[k]? with
    | none => none
    | some c =>
      if (∃ s', μ s' = some c) then none
      else if (prio c).find? (fun s' => μ s' = none ∧ (pref s')[k]? = some c) = some s then some c
      else none

/-- The **Boston mechanism**: run rounds `0, …, m − 1` from the empty assignment. -/
def boston (pref : Fin n → List (Fin m)) (prio : Fin m → List (Fin n)) : Fin n → Option (Fin m) :=
  (List.range m).foldl (fun μ k => bostonRound pref prio k μ) fun _ => none

/-- True preferences in the example: student `0` ranks schools `0 ≻ 1 ≻ 2`, student `1`
`0 ≻ 2 ≻ 1`, student `2` `1 ≻ 0 ≻ 2`. -/
def exTruePref : Fin 3 → List (Fin 3) := ![[0, 1, 2], [0, 2, 1], [1, 0, 2]]

/-- Priorities: school `0` ranks students `1, 0, 2`; school `1` ranks `0, 2, 1`; school `2`
ranks `0, 1, 2`. -/
def exPrio : Fin 3 → List (Fin 3) := ![[1, 0, 2], [0, 2, 1], [0, 1, 2]]

/-- Student `0`'s misreport: she ranks school `1` first. -/
def exManipPref : Fin 3 → List (Fin 3) := ![[1, 0, 2], [0, 2, 1], [1, 0, 2]]

/-- **The Boston mechanism is not strategy-proof** (Abdulkadiroğlu–Sönmez 2003). Reporting
truthfully, student `0` loses school `0` to student `1` in round `0` and finds school `1`
taken in round `1`, so she gets her last choice, school `2`. By ranking school `1` first she
gets it in round `0`, and she truly prefers it to school `2` (it comes earlier in her true
list). Preferences and priorities are compared by position in the lists. -/
theorem boston_manipulable :
    boston exTruePref exPrio 0 = some 2 ∧ boston exManipPref exPrio 0 = some 1 ∧
      (∀ s, exManipPref s ≠ exTruePref s → s = 0) ∧
      (exTruePref 0).idxOf 1 < (exTruePref 0).idxOf 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The Boston outcome need not be stable**: under truthful reports student `0` gets
school `2`, prefers school `1`, which student `2` gets, and has higher priority than
student `2` at school `1`. -/
theorem boston_not_stable :
    boston exTruePref exPrio 0 = some 2 ∧ boston exTruePref exPrio 2 = some 1 ∧
      (exTruePref 0).idxOf 1 < (exTruePref 0).idxOf 2 ∧ (exPrio 1).idxOf 0 < (exPrio 1).idxOf 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Econ
