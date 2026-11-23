/-
# Finite games of perfect information: backward induction and subgame perfection

MWG §9.B (Defs. 9.B.1–9.B.2, Props. 9.B.1–9.B.2), Kuhn (1953), Zermelo (1913). A finite
extensive-form game of perfect information is a finite tree: at each decision node one
player chooses among finitely many (at least one) moves, and each terminal node carries a
payoff vector. Every decision node starts a subgame.

* `GameTree I`: leaves with payoffs `I → ℝ`, or a node owned by `player` with moves
  `Fin (k+1)` leading to subtrees.
* `Profile t`: a pure strategy profile assigns a move to every decision node (also those
  off the path of play), so a profile of `t` restricts to every subgame.
* `outcome t s`: payoff vector reached when everyone follows `s`.
* `OnlyDeviates i t s s'`: `s'` differs from `s` only at nodes owned by `i` (`s'` is a
  unilateral deviation by `i`).
* `IsNashTree t s`, `IsSPE t s`: Nash equilibrium, and Nash equilibrium in every subgame
  (MWG Def. 9.B.2).
* `NoOneShotDeviation t s`: at every node, the mover cannot gain by changing only the move
  at that node and following `s` afterwards.

Main results:
* `isSPE_iff_noOneShotDeviation` (**one-shot deviation principle**, finite horizon).
* `exists_isSPE` (**Kuhn's theorem / backward induction**, MWG Prop. 9.B.1): every finite
  game of perfect information has a pure-strategy subgame perfect equilibrium.
* `zermelo`, `zermelo_draw`: in a finite two-player win/lose game one of the players has a
  winning strategy; with draws allowed (chess), either one player can force a win or both
  can guarantee at least a draw.

Scope: perfect information and no moves by nature (chance nodes); imperfect information,
behavioural strategies and Kuhn's equivalence theorem are not formalized.
* Witness (entry deterrence, MWG Ex. 9.B.1-style): "stay out / fight" is a Nash
  equilibrium that is not subgame perfect; "enter / accommodate" is the SPE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Econ

universe u

/-- A finite game tree of perfect information with players `I`. -/
inductive GameTree (I : Type u) : Type u
  /-- A terminal node with payoff vector `payoff`. -/
  | leaf (payoff : I → ℝ) : GameTree I
  /-- A decision node where `player` picks one of `k + 1` moves. -/
  | node (player : I) (k : ℕ) (next : Fin (k + 1) → GameTree I) : GameTree I

namespace GameTree

variable {I : Type u}

/-- A pure strategy profile: a move at every decision node. -/
def Profile : GameTree I → Type
  | leaf _ => Unit
  | node _ k next => Fin (k + 1) × ((a : Fin (k + 1)) → Profile (next a))

/-- The payoff vector reached when all players follow `s`. -/
def outcome : (t : GameTree I) → Profile t → I → ℝ
  | leaf p, _ => p
  | node _ _ next, s => outcome (next s.1) (s.2 s.1)

/-- `s'` differs from `s` only at decision nodes owned by `i`. -/
def OnlyDeviates (i : I) : (t : GameTree I) → Profile t → Profile t → Prop
  | leaf _, _, _ => True
  | node j _ next, s, s' => (j ≠ i → s.1 = s'.1) ∧ ∀ a, OnlyDeviates i (next a) (s.2 a) (s'.2 a)

/-- **Nash equilibrium** of the whole game: no player gains by a unilateral deviation. -/
def IsNashTree (t : GameTree I) (s : Profile t) : Prop :=
  ∀ i s', OnlyDeviates i t s s' → outcome t s' i ≤ outcome t s i

/-- **Subgame perfect equilibrium** (MWG Def. 9.B.2): `s` induces a Nash equilibrium in
every subgame. -/
def IsSPE : (t : GameTree I) → Profile t → Prop
  | leaf _, _ => True
  | node j k next, s => IsNashTree (node j k next) s ∧ ∀ a, IsSPE (next a) (s.2 a)

/-- No profitable **one-shot deviation**: at each node, the mover's prescribed move is
optimal given that everyone follows `s` afterwards. -/
def NoOneShotDeviation : (t : GameTree I) → Profile t → Prop
  | leaf _, _ => True
  | node j _ next, s =>
      (∀ a, outcome (next a) (s.2 a) j ≤ outcome (next s.1) (s.2 s.1) j) ∧
        ∀ a, NoOneShotDeviation (next a) (s.2 a)

theorem onlyDeviates_refl (i : I) : ∀ (t : GameTree I) (s : Profile t), OnlyDeviates i t s s
  | leaf _, _ => trivial
  | node _ _ next, s => ⟨fun _ => rfl, fun a => onlyDeviates_refl i (next a) (s.2 a)⟩

/-- No one-shot deviation ⟹ Nash: a deviation by `i` that changes many moves is undone
one node at a time, from the bottom up. -/
theorem NoOneShotDeviation.isNashTree :
    ∀ {t : GameTree I} {s : Profile t}, NoOneShotDeviation t s → IsNashTree t s
  | leaf _, _, _ => fun _ _ _ => le_rfl
  | node j k next, s, h => by
    intro i s' hdev
    obtain ⟨hroot, hsub⟩ := h
    obtain ⟨hmove, hdevs⟩ := hdev
    -- In the subgame after `s'`'s move, `s'` is a deviation by `i` from `s`.
    have hchild : outcome (next s'.1) (s'.2 s'.1) i ≤ outcome (next s'.1) (s.2 s'.1) i :=
      (hsub s'.1).isNashTree i _ (hdevs s'.1)
    show outcome (next s'.1) (s'.2 s'.1) i ≤ outcome (next s.1) (s.2 s.1) i
    by_cases hji : j = i
    · subst hji
      exact hchild.trans (hroot s'.1)
    · rw [← hmove hji] at hchild ⊢
      exact hchild

/-- **One-shot deviation principle** (finite horizon): a profile is subgame perfect iff no
player can gain by deviating at a single node. -/
theorem isSPE_iff_noOneShotDeviation :
    ∀ (t : GameTree I) (s : Profile t), IsSPE t s ↔ NoOneShotDeviation t s
  | leaf _, _ => Iff.rfl
  | node j k next, s => by
    constructor
    · rintro ⟨hnash, hsub⟩
      refine ⟨fun a => ?_, fun a => (isSPE_iff_noOneShotDeviation (next a) (s.2 a)).1 (hsub a)⟩
      -- The deviation "play `a` at the root, otherwise follow `s`" is unilateral for `j`.
      exact hnash j (a, s.2) ⟨fun h => absurd rfl h, fun b => onlyDeviates_refl j _ _⟩
    · intro h
      exact ⟨h.isNashTree, fun a => (isSPE_iff_noOneShotDeviation (next a) (s.2 a)).2 (h.2 a)⟩

/-- **Kuhn's theorem / backward induction** (MWG Prop. 9.B.1; Zermelo 1913): every finite
game of perfect information has a pure-strategy subgame perfect equilibrium. -/
theorem exists_isSPE : ∀ t : GameTree I, ∃ s, IsSPE t s
  | leaf _ => ⟨(), trivial⟩
  | node j k next => by
    -- Solve every subgame, then let the mover pick a best continuation.
    choose c hc using fun a => exists_isSPE (next a)
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
      (fun a => outcome (next a) (c a) j) ⟨0, Finset.mem_univ _⟩
    refine ⟨(a, c), (isSPE_iff_noOneShotDeviation _ _).2 ⟨fun b => ha b (Finset.mem_univ b),
      fun b => (isSPE_iff_noOneShotDeviation _ _).1 (hc b)⟩⟩

/-- Every SPE is a Nash equilibrium. -/
theorem IsSPE.isNashTree : ∀ {t : GameTree I} {s : Profile t}, IsSPE t s → IsNashTree t s
  | leaf _, _, _ => fun _ _ _ => le_rfl
  | node _ _ _, _, h => h.1

/-- `p` is the payoff vector of some leaf of `t`. -/
def IsLeafOf (p : I → ℝ) : GameTree I → Prop
  | leaf q => q = p
  | node _ _ next => ∃ a, IsLeafOf p (next a)

/-- Every outcome is the payoff vector of some leaf; in particular, if every leaf
satisfies `P`, so does every outcome. -/
theorem outcome_mem {P : (I → ℝ) → Prop} :
    ∀ (t : GameTree I), (∀ p, IsLeafOf p t → P p) → ∀ s, P (outcome t s) := by
  intro t
  induction t with
  | leaf p => intro h _; exact h p rfl
  | node j k next ih => intro h s; exact ih s.1 (fun p hp => h p ⟨s.1, hp⟩) _

/-- **Zermelo's theorem** for win/lose games. In a finite two-player game of perfect
information where at every leaf exactly one player wins (payoff `1` to the winner, `-1` to
the loser), one of the players has a strategy that wins against every strategy of the
other. -/
theorem zermelo (t : GameTree Bool)
    (hwl : ∀ p, IsLeafOf p t → (p true = 1 ∧ p false = -1) ∨
      (p true = -1 ∧ p false = 1)) :
    ∃ s : Profile t, (∀ s', OnlyDeviates false t s s' → outcome t s' true = 1) ∨
      (∀ s', OnlyDeviates true t s s' → outcome t s' false = 1) := by
  obtain ⟨s, hs⟩ := exists_isSPE t
  have hN := hs.isNashTree
  refine ⟨s, ?_⟩
  have hwl' := fun s => outcome_mem (P := fun p => (p true = 1 ∧ p false = -1) ∨
    (p true = -1 ∧ p false = 1)) t hwl s
  rcases hwl' s with h | h
  · -- Player `true` wins on the equilibrium path; no deviation by `false` can change that,
    -- since it would have to give `false` the payoff `1 > -1`.
    left
    intro s' hdev
    have hle := hN false s' hdev
    rcases hwl' s' with h' | h'
    · exact h'.1
    · linarith [h.2, h'.2]
  · right
    intro s' hdev
    have hle := hN true s' hdev
    rcases hwl' s' with h' | h'
    · linarith [h.1, h'.1]
    · exact h'.2

/-- **Zermelo's theorem with draws** (chess). In a finite two-player zero-sum game of
perfect information where every leaf is a win (`1`), a draw (`0`) or a loss (`-1`) for player
`true`, and `false` gets the negative: either `true` can force a win, or `false` can force a
win, or each player can guarantee at least a draw. -/
theorem zermelo_draw (t : GameTree Bool)
    (hl : ∀ p, IsLeafOf p t → p false = -p true ∧ (p true = 1 ∨ p true = 0 ∨ p true = -1)) :
    ∃ s : Profile t, (∀ s', OnlyDeviates false t s s' → outcome t s' true = 1) ∨
      (∀ s', OnlyDeviates true t s s' → outcome t s' false = 1) ∨
      ((∀ s', OnlyDeviates false t s s' → 0 ≤ outcome t s' true) ∧
        (∀ s', OnlyDeviates true t s s' → 0 ≤ outcome t s' false)) := by
  obtain ⟨s, hs⟩ := exists_isSPE t
  have hN := hs.isNashTree
  have hP := fun s => outcome_mem (P := fun p => p false = -p true ∧
    (p true = 1 ∨ p true = 0 ∨ p true = -1)) t hl s
  refine ⟨s, ?_⟩
  obtain ⟨hz, hv⟩ := hP s
  rcases hv with h1 | h0 | hm
  · left
    intro s' hdev
    have hle := hN false s' hdev
    obtain ⟨hz', hv'⟩ := hP s'
    rcases hv' with h | h | h <;> [exact h; (exfalso; linarith); (exfalso; linarith)]
  · right; right
    refine ⟨fun s' hdev => ?_, fun s' hdev => ?_⟩
    · have hle := hN false s' hdev
      have hz' := (hP s').1
      linarith
    · have hle := hN true s' hdev
      have hz' := (hP s').1
      linarith
  · right; left
    intro s' hdev
    have hle := hN true s' hdev
    obtain ⟨hz', hv'⟩ := hP s'
    rcases hv' with h | h | h
    · exfalso; linarith
    · exfalso; linarith
    · linarith

/-! ### Witness: entry deterrence

Player `true` (the entrant) chooses `0` = stay out, with payoffs `(entrant, incumbent) =
(0, 2)`, or `1` = enter. After entry, player `false` (the incumbent) chooses `0` = fight
`(-1, -1)` or `1` = accommodate `(1, 1)`. "Stay out, fight" is a Nash equilibrium but not
subgame perfect: fighting is an empty threat. "Enter, accommodate" is the SPE. -/

/-- The incumbent's decision after entry: fight (`0`) or accommodate (`1`). -/
def incumbentNode : GameTree Bool :=
  node false 1 fun b => leaf fun _ => if b = 0 then -1 else 1

/-- The entrant's two moves: stay out (`0`) or enter (`1`). -/
def entryNext : Fin 2 → GameTree Bool := ![leaf fun i => if i then 0 else 2, incumbentNode]

/-- The entry game. -/
def entryGame : GameTree Bool := node true 1 entryNext

/-- Stay out; fight if entry occurs. -/
def outFight : Profile entryGame :=
  (0, fun a => Fin.cases (motive := fun a => Profile (entryNext a)) ()
    (fun i => Fin.cases (motive := fun i : Fin 1 => Profile (entryNext i.succ))
      ((0 : Fin 2), fun _ => ()) (fun i => i.elim0) i) a)

/-- Enter; accommodate. -/
def inAccommodate : Profile entryGame :=
  (1, fun a => Fin.cases (motive := fun a => Profile (entryNext a)) ()
    (fun i => Fin.cases (motive := fun i : Fin 1 => Profile (entryNext i.succ))
      ((1 : Fin 2), fun _ => ()) (fun i => i.elim0) i) a)

example : IsNashTree entryGame outFight ∧ ¬ IsSPE entryGame outFight ∧
    IsSPE entryGame inAccommodate := by
  refine ⟨?_, ?_, ?_⟩
  · intro i s' hdev
    obtain ⟨a, s₂⟩ := s'
    obtain ⟨hroot, hsub⟩ := hdev
    cases i
    · -- The incumbent's moves are off the path: the outcome stays `(0, 2)`.
      have h0 : a = 0 := (hroot (by decide)).symm
      subst h0
      exact le_rfl
    · -- Entering against "fight" gives the entrant `-1 < 0`.
      have hf : (s₂ 1).1 = 0 := ((hsub 1).1 (by decide)).symm
      fin_cases a
      · exact le_rfl
      · change (if (s₂ 1).1 = 0 then (-1 : ℝ) else 1) ≤ 0
        simp only [hf, ↓reduceIte]
        norm_num
  · rw [isSPE_iff_noOneShotDeviation]
    rintro ⟨-, hsub⟩
    have := (hsub 1).1 1
    change (if (1 : Fin 2) = 0 then (-1 : ℝ) else 1) ≤ (if (0 : Fin 2) = 0 then (-1 : ℝ) else 1)
      at this
    norm_num at this
  · rw [isSPE_iff_noOneShotDeviation]
    refine ⟨fun a => ?_, fun a => ?_⟩
    · fin_cases a
      · change ((if true then 0 else 2 : ℝ)) ≤ (if (1 : Fin 2) = 0 then (-1 : ℝ) else 1)
        norm_num
      · exact le_rfl
    · fin_cases a
      · trivial
      · refine ⟨fun b => ?_, fun b => trivial⟩
        fin_cases b
        · change (if (0 : Fin 2) = 0 then (-1 : ℝ) else 1) ≤ (if (1 : Fin 2) = 0 then (-1 : ℝ) else 1)
          norm_num
        · exact le_rfl

end GameTree

end Econ
