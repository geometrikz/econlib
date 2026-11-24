/-
# Robinson's theorem: fictitious play solves zero-sum games

References. G. W. Brown (1951), "Iterative Solution of Games by Fictitious
Play"; J. Robinson (1951), "An Iterative Method of Solving a Game", *Annals of
Mathematics* 54(2), 296–301 (the proof followed here).

A zero-sum matrix game `A : I → J → ℝ`: the row player picks `k`, the column
player picks `l`, the row player receives `A k l` and the column player pays
it (`Games/ZeroSum.lean`). On a **fictitious-play path** (`IsFPPath`) both
players move simultaneously, and at every date `t` each best responds to the
other's past play: the row player's action maximizes its cumulative payoff
against the columns played so far (`rowPay`), and the column player's action
minimizes the row player's cumulative payoff against the rows played so far
(`colPay`). (At date `0` every action is a best response.)

**Robinson's theorem** (`robinson`): the exploitability of the empirical
frequencies,

    max_k (A q_t)_k − min_l (p_t A)_l,

with `p_t`, `q_t` the empirical frequencies of rows and columns in periods
`0, …, t−1` (`rowFreq`, `colFreq`), tends to `0` (`exploit`, which is
nonnegative, `exploit_nonneg`). Consequently:
* `eventually_isEpsSaddle`: for every `ε > 0`, the empirical frequencies are
  eventually an `ε`-saddle point (`ε`-equilibrium) of the game;
* `tendsto_max_min_value` (Robinson's own statement): the best payoff against
  `q_t`, `max_k (A q_t)_k`, and the least payoff against `p_t`,
  `min_l (p_t A)_l`, both converge to the value of the game; so does the
  empirical payoff `p_tᵀ A q_t` (`tendsto_payoff_value`).

**Proof (Robinson).** A *vector system* (`IsSystem`) for the submatrix on
rows `I'` and columns `J'` is a pair of cumulative-payoff vectors `U`, `V`
(with arbitrary initial values satisfying `max U(0) ≤ min V(0)`) updated by
best responses. Let `a` bound `|A|`.
* If every row and every column is a best response at some date in
  `[T − n, T]`, then `max U(T) − min V(T) ≤ 4an` (`gap_le_of_eligible`), by
  the identity `Σ_τ U(T)(i_τ) − Σ_τ V(T)(j_τ) = Σ_τ U(0)(i_τ) − Σ_τ V(0)(j_τ)`.
* If some row (column) is never a best response in `[s, s + n]`, the system
  is a vector system of the smaller submatrix there (`erase_step`,
  `erase_stepJ`, the latter by transposition, `IsSystem.transpose`).
* By induction on the size of the submatrix, for every `ε > 0`, eventually
  `max U(t) − min V(t) < εt` for every vector system (`eventually_good`).

Non-vacuity: a fictitious-play path exists (`fpRow`, `fpCol`,
`isFPPath_fp`). Brown's original *alternating* process is in
`AlternatingFP.lean`. The rate of convergence (Karlin's conjecture) is not
formalized. The frequencies need not converge to a particular equilibrium;
informally, `eventually_isEpsSaddle` says they approach the set of saddle
points (the distance-to-the-set statement is not formalized). The lemmas on
vector systems assume a global bound `|A k l| ≤ a`, which holds for the finite
games treated here.
-/
module

public import EconLean.Games.ZeroSum
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

@[expose] public section

noncomputable section

namespace Econ

namespace Robinson

open Finset Filter Topology

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-! ### Vector systems -/

/-- A vector system for the submatrix of `A` on rows `I'` and columns `J'`,
valid up to date `T`: `i τ` maximizes `U τ` over `I'`, `j τ` minimizes `V τ`
over `J'`, and the vectors are updated by the chosen column and row. -/
structure IsSystem (A : I → J → ℝ) (I' : Finset I) (J' : Finset J) (U : ℕ → I → ℝ)
    (V : ℕ → J → ℝ) (i : ℕ → I) (j : ℕ → J) (T : ℕ) : Prop where
  memI : ∀ τ < T, i τ ∈ I'
  bestI : ∀ τ < T, ∀ k ∈ I', U τ k ≤ U τ (i τ)
  memJ : ∀ τ < T, j τ ∈ J'
  bestJ : ∀ τ < T, ∀ l ∈ J', V τ (j τ) ≤ V τ l
  updU : ∀ τ < T, ∀ k, U (τ + 1) k = U τ k + A k (j τ)
  updV : ∀ τ < T, ∀ l, V (τ + 1) l = V τ l + A (i τ) l

/-- `max_{I'} U(t) − min_{J'} V(t)`. -/
def gap (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty) (hJ : J'.Nonempty)
    (U : ℕ → I → ℝ) (V : ℕ → J → ℝ) (t : ℕ) : ℝ :=
  I'.sup' hI (U t) - J'.inf' hJ (V t)

variable {A : I → J → ℝ} {I' : Finset I} {J' : Finset J} {U : ℕ → I → ℝ} {V : ℕ → J → ℝ}
  {i : ℕ → I} {j : ℕ → J} {T : ℕ} {a : ℝ}

omit [DecidableEq I] [DecidableEq J] in
theorem IsSystem.mono (h : IsSystem A I' J' U V i j T) {T' : ℕ} (hT : T' ≤ T) :
    IsSystem A I' J' U V i j T' :=
  ⟨fun τ hτ => h.memI τ (by omega), fun τ hτ => h.bestI τ (by omega),
    fun τ hτ => h.memJ τ (by omega), fun τ hτ => h.bestJ τ (by omega),
    fun τ hτ => h.updU τ (by omega), fun τ hτ => h.updV τ (by omega)⟩

omit [DecidableEq I] [DecidableEq J] in
theorem U_bounds (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a) {σ n : ℕ}
    (hσ : σ + n ≤ T) (k : I) : U σ k - a * n ≤ U (σ + n) k ∧ U (σ + n) k ≤ U σ k + a * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    have hu := h.updU (σ + n) (by omega) k
    have hA := abs_le.1 (ha k (j (σ + n)))
    rw [← add_assoc, hu]
    push_cast
    constructor <;> linarith [ih.1, ih.2, hA.1, hA.2]

omit [DecidableEq I] [DecidableEq J] in
theorem V_bounds (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a) {σ n : ℕ}
    (hσ : σ + n ≤ T) (l : J) : V σ l - a * n ≤ V (σ + n) l ∧ V (σ + n) l ≤ V σ l + a * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    have hv := h.updV (σ + n) (by omega) l
    have hA := abs_le.1 (ha (i (σ + n)) l)
    rw [← add_assoc, hv]
    push_cast
    constructor <;> linarith [ih.1, ih.2, hA.1, hA.2]

omit [DecidableEq I] [DecidableEq J] in
theorem gap_le (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a) (hI : I'.Nonempty)
    (hJ : J'.Nonempty) {σ n : ℕ} (hσ : σ + n ≤ T) :
    gap I' J' hI hJ U V (σ + n) ≤ gap I' J' hI hJ U V σ + 2 * a * n := by
  have h1 : I'.sup' hI (U (σ + n)) ≤ I'.sup' hI (U σ) + a * n :=
    sup'_le _ _ fun k hk => (U_bounds h ha hσ k).2.trans (by linarith [le_sup' (U σ) hk])
  have h2 : J'.inf' hJ (V σ) - a * n ≤ J'.inf' hJ (V (σ + n)) :=
    le_inf' _ _ fun l hl => le_trans (by linarith [inf'_le (V σ) hl]) (V_bounds h ha hσ l).1
  unfold gap; linarith

omit [DecidableEq I] [DecidableEq J] in
/-- A row that is a best response at `σ` is at most `2an` behind at `σ + n`. -/
theorem eligible_row (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a)
    (hI : I'.Nonempty) {σ n : ℕ} (hσ : σ + n ≤ T) {k : I} (he : U σ k = I'.sup' hI (U σ)) :
    I'.sup' hI (U (σ + n)) - U (σ + n) k ≤ 2 * a * n := by
  have h1 : I'.sup' hI (U (σ + n)) ≤ I'.sup' hI (U σ) + a * n :=
    sup'_le _ _ fun k' hk' => (U_bounds h ha hσ k').2.trans (by linarith [le_sup' (U σ) hk'])
  linarith [(U_bounds h ha hσ k).1]

omit [DecidableEq I] [DecidableEq J] in
theorem eligible_col (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a)
    (hJ : J'.Nonempty) {σ n : ℕ} (hσ : σ + n ≤ T) {l : J} (he : V σ l = J'.inf' hJ (V σ)) :
    V (σ + n) l - J'.inf' hJ (V (σ + n)) ≤ 2 * a * n := by
  have h2 : J'.inf' hJ (V σ) - a * n ≤ J'.inf' hJ (V (σ + n)) :=
    le_inf' _ _ fun l' hl' => le_trans (by linarith [inf'_le (V σ) hl']) (V_bounds h ha hσ l').1
  linarith [(V_bounds h ha hσ l).2]

omit [DecidableEq I] [DecidableEq J] in
theorem U_eq_sum (h : IsSystem A I' J' U V i j T) :
    ∀ n ≤ T, ∀ k, U n k = U 0 k + ∑ σ ∈ range n, A k (j σ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => intro hn k; rw [h.updU n (by omega), ih (by omega), sum_range_succ]; ring

omit [DecidableEq I] [DecidableEq J] in
theorem V_eq_sum (h : IsSystem A I' J' U V i j T) :
    ∀ n ≤ T, ∀ l, V n l = V 0 l + ∑ σ ∈ range n, A (i σ) l := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => intro hn l; rw [h.updV n (by omega), ih (by omega), sum_range_succ]; ring

omit [DecidableEq I] [DecidableEq J] in
/-- **Robinson's identity.** -/
theorem sum_identity (h : IsSystem A I' J' U V i j T) :
    ∑ τ ∈ range T, U T (i τ) - ∑ τ ∈ range T, V T (j τ) =
      ∑ τ ∈ range T, U 0 (i τ) - ∑ τ ∈ range T, V 0 (j τ) := by
  simp only [U_eq_sum h T le_rfl, V_eq_sum h T le_rfl, sum_add_distrib]
  have := sum_comm (s := range T) (t := range T) (f := fun τ σ => A (i τ) (j σ))
  linarith

omit [DecidableEq I] [DecidableEq J] in
/-- If every row and column is a best response at some date in `[T − n, T]`,
the gap at `T` is at most `4an`. -/
theorem gap_le_of_eligible (h : IsSystem A I' J' U V i j T) (ha : ∀ k l, |A k l| ≤ a)
    (hI : I'.Nonempty) (hJ : J'.Nonempty) (hT : 0 < T)
    (hinit : I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0)) {n : ℕ} (hn : n ≤ T)
    (hrow : ∀ k ∈ I', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ U σ k = I'.sup' hI (U σ))
    (hcol : ∀ l ∈ J', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ V σ l = J'.inf' hJ (V σ)) :
    gap I' J' hI hJ U V T ≤ 4 * a * n := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha hI.choose hJ.choose)
  have hk : ∀ k ∈ I', I'.sup' hI (U T) - 2 * a * n ≤ U T k := by
    intro k hk
    obtain ⟨σ, h1, h2, he⟩ := hrow k hk
    have := eligible_row h ha hI (n := T - σ) (by omega) he
    rw [show σ + (T - σ) = T by omega] at this
    have : (((T - σ : ℕ)) : ℝ) ≤ n := by exact_mod_cast (by omega : T - σ ≤ n)
    nlinarith
  have hl : ∀ l ∈ J', V T l ≤ J'.inf' hJ (V T) + 2 * a * n := by
    intro l hl
    obtain ⟨σ, h1, h2, he⟩ := hcol l hl
    have := eligible_col h ha hJ (n := T - σ) (by omega) he
    rw [show σ + (T - σ) = T by omega] at this
    have : (((T - σ : ℕ)) : ℝ) ≤ n := by exact_mod_cast (by omega : T - σ ≤ n)
    nlinarith
  have s1 : (T : ℝ) * (I'.sup' hI (U T) - 2 * a * n) ≤ ∑ τ ∈ range T, U T (i τ) := by
    have := sum_le_sum (s := range T) (f := fun _ => I'.sup' hI (U T) - 2 * a * n)
      (g := fun τ => U T (i τ)) fun τ hτ => hk (i τ) (h.memI τ (mem_range.1 hτ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have s2 : ∑ τ ∈ range T, V T (j τ) ≤ (T : ℝ) * (J'.inf' hJ (V T) + 2 * a * n) := by
    have := sum_le_sum (s := range T) (g := fun _ => J'.inf' hJ (V T) + 2 * a * n)
      (f := fun τ => V T (j τ)) fun τ hτ => hl (j τ) (h.memJ τ (mem_range.1 hτ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have s3 : ∑ τ ∈ range T, U 0 (i τ) ≤ (T : ℝ) * I'.sup' hI (U 0) := by
    have := sum_le_sum (s := range T) (g := fun _ => I'.sup' hI (U 0))
      (f := fun τ => U 0 (i τ)) fun τ hτ => le_sup' (U 0) (h.memI τ (mem_range.1 hτ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have s4 : (T : ℝ) * J'.inf' hJ (V 0) ≤ ∑ τ ∈ range T, V 0 (j τ) := by
    have := sum_le_sum (s := range T) (f := fun _ => J'.inf' hJ (V 0))
      (g := fun τ => V 0 (j τ)) fun τ hτ => inf'_le (V 0) (h.memJ τ (mem_range.1 hτ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have hid := sum_identity h
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have key : (T : ℝ) * (gap I' J' hI hJ U V T - 4 * a * n) ≤ 0 := by
    unfold gap; nlinarith
  by_contra hc
  rw [not_le] at hc
  linarith [mul_pos hT' (sub_pos.2 hc)]

/-- The property proved by induction: every system valid up to `t` with
`max U(0) ≤ min V(0)` has gap `< εt` at `t`. -/
def Good (A : I → J → ℝ) (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty)
    (hJ : J'.Nonempty) (ε : ℝ) (t : ℕ) : Prop :=
  ∀ (U : ℕ → I → ℝ) (V : ℕ → J → ℝ) (i : ℕ → I) (j : ℕ → J), IsSystem A I' J' U V i j t →
    I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0) → gap I' J' hI hJ U V t < ε * t

/-! ### Transposition and deletion of a never-used row or column -/

theorem sup'_neg {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    s.sup' hs (fun x => -f x) = -s.inf' hs f :=
  le_antisymm (sup'_le _ _ fun _ hx => neg_le_neg (inf'_le f hx))
    (neg_le.1 (le_inf' _ _ fun _ hx => neg_le.1 (le_sup' (fun x => -f x) hx)))

theorem inf'_neg {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    s.inf' hs (fun x => -f x) = -s.sup' hs f := by
  have := sup'_neg s hs (fun x => -f x)
  simp only [neg_neg] at this
  linarith

theorem inf'_add_const {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (c : ℝ) :
    s.inf' hs (fun x => f x + c) = s.inf' hs f + c := by
  obtain ⟨x, hx, hxe⟩ := exists_mem_eq_inf' hs f
  refine le_antisymm ?_ (le_inf' _ _ fun y hy => by linarith [inf'_le f hy])
  rw [hxe]; exact inf'_le (fun x => f x + c) hx

theorem sup'_erase_eq {s : Finset I} (hs : s.Nonempty) {f : I → ℝ} {k : I}
    (hk : f k < s.sup' hs f) (hs' : (s.erase k).Nonempty) :
    (s.erase k).sup' hs' f = s.sup' hs f := by
  refine le_antisymm (sup'_le _ _ fun x hx => le_sup' f (mem_of_mem_erase hx)) ?_
  obtain ⟨x, hx, hxe⟩ := exists_mem_eq_sup' hs f
  have hne : x ≠ k := by rintro rfl; rw [hxe] at hk; exact lt_irrefl _ hk
  rw [hxe]; exact le_sup' f (mem_erase.2 ⟨hne, hx⟩)

omit [DecidableEq I] [DecidableEq J] in
/-- The transposed system of the column player, for the game `−Aᵀ`. -/
theorem IsSystem.transpose (h : IsSystem A I' J' U V i j T) :
    IsSystem (fun l k => -A k l) J' I' (fun τ l => -V τ l) (fun τ k => -U τ k) j i T where
  memI := h.memJ
  bestI τ hτ l hl := neg_le_neg (h.bestJ τ hτ l hl)
  memJ := h.memI
  bestJ τ hτ k hk := neg_le_neg (h.bestI τ hτ k hk)
  updU τ hτ l := by rw [h.updV τ hτ l]; ring
  updV τ hτ k := by rw [h.updU τ hτ k]; ring

omit [DecidableEq I] [DecidableEq J] in
theorem gap_transpose (hI : I'.Nonempty) (hJ : J'.Nonempty) (t : ℕ) :
    gap J' I' hJ hI (fun τ l => -V τ l) (fun τ k => -U τ k) t = gap I' J' hI hJ U V t := by
  unfold gap; rw [sup'_neg, inf'_neg]; ring

omit [DecidableEq I] [DecidableEq J] in
theorem Good.transpose {hI : I'.Nonempty} {hJ : J'.Nonempty} {ε : ℝ} {t : ℕ}
    (h : Good A I' J' hI hJ ε t) : Good (fun l k => -A k l) J' I' hJ hI ε t := by
  intro U' V' i' j' hs hinit
  have hs' := hs.transpose
  simp only [neg_neg] at hs'
  have h0 := h _ _ _ _ hs' (by
    show I'.sup' hI (fun k => -V' 0 k) ≤ J'.inf' hJ (fun l => -U' 0 l)
    rw [sup'_neg, inf'_neg]; linarith)
  have e : gap I' J' hI hJ (fun τ k => -V' τ k) (fun τ l => -U' τ l) t =
      gap J' I' hJ hI U' V' t := by
    unfold gap; rw [sup'_neg, inf'_neg]; ring
  rwa [e] at h0

omit [DecidableEq J] in
/-- **Deleting a row that is never a best response.** -/
theorem erase_step (h : IsSystem A I' J' U V i j T) (hI : I'.Nonempty) (hJ : J'.Nonempty)
    {s n : ℕ} (hsn : s + n ≤ T) {k : I}
    (hnot : ∀ τ ≤ n, U (s + τ) k < I'.sup' hI (U (s + τ))) (hI' : (I'.erase k).Nonempty)
    {ε : ℝ} (hgood : Good A (I'.erase k) J' hI' hJ ε n) :
    gap I' J' hI hJ U V (s + n) < gap I' J' hI hJ U V s + ε * n := by
  set δ := gap I' J' hI hJ U V s
  have hsys : IsSystem A (I'.erase k) J' (fun τ => U (s + τ)) (fun τ l => V (s + τ) l + δ)
      (fun τ => i (s + τ)) (fun τ => j (s + τ)) n :=
    { memI := fun τ hτ => by
        refine mem_erase.2 ⟨fun he => ?_, h.memI _ (by omega)⟩
        have h1 := hnot τ hτ.le
        have h2 : I'.sup' hI (U (s + τ)) ≤ U (s + τ) (i (s + τ)) :=
          sup'_le _ _ (h.bestI _ (by omega))
        rw [he] at h2
        linarith
      bestI := fun τ hτ k' hk' => h.bestI _ (by omega) k' (mem_of_mem_erase hk')
      memJ := fun τ hτ => h.memJ _ (by omega)
      bestJ := fun τ hτ l hl => by linarith [h.bestJ (s + τ) (by omega) l hl]
      updU := fun τ hτ k' => by rw [← add_assoc]; exact h.updU _ (by omega) k'
      updV := fun τ hτ l => by
        rw [← add_assoc, h.updV _ (by omega) l]; ring }
  have h0 := hnot 0 (Nat.zero_le _)
  rw [add_zero] at h0
  have hinit : (I'.erase k).sup' hI' (U s) ≤ J'.inf' hJ (fun l => V s l + δ) := by
    rw [inf'_add_const, sup'_erase_eq hI h0 hI']
    simp only [δ, gap]; linarith
  have := hgood _ _ _ _ hsys hinit
  unfold gap at this
  dsimp only at this
  rw [inf'_add_const, sup'_erase_eq hI (hnot n le_rfl) hI'] at this
  unfold gap
  linarith

omit [DecidableEq I] in
/-- **Deleting a column that is never a best response** (by transposition). -/
theorem erase_stepJ (h : IsSystem A I' J' U V i j T) (hI : I'.Nonempty) (hJ : J'.Nonempty)
    {s n : ℕ} (hsn : s + n ≤ T) {l : J}
    (hnot : ∀ τ ≤ n, J'.inf' hJ (V (s + τ)) < V (s + τ) l) (hJ' : (J'.erase l).Nonempty)
    {ε : ℝ} (hgood : Good A I' (J'.erase l) hI hJ' ε n) :
    gap I' J' hI hJ U V (s + n) < gap I' J' hI hJ U V s + ε * n := by
  have ht := erase_step h.transpose hJ hI hsn (k := l) (fun τ hτ => by
    show -V (s + τ) l < J'.sup' hJ (fun l => -V (s + τ) l)
    rw [sup'_neg]; linarith [hnot τ hτ]) hJ' hgood.transpose
  rwa [gap_transpose, gap_transpose] at ht

/-! ### The induction -/

/-- **Robinson's lemma**: for every submatrix and every `ε > 0`, eventually
every vector system has gap `< εt`. -/
theorem eventually_good (ha : ∀ k l, |A k l| ≤ a) :
    ∀ (N : ℕ) (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty) (hJ : J'.Nonempty),
      I'.card + J'.card = N → ∀ ε > 0, ∀ᶠ t in atTop, Good A I' J' hI hJ ε t := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro I' J' hI hJ hN ε hε
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha hI.choose hJ.choose)
  have hε' : 0 < ε / 2 := by positivity
  have hrow : ∀ᶠ t in atTop, ∀ k ∈ I', ∀ h' : (I'.erase k).Nonempty,
      Good A (I'.erase k) J' h' hJ (ε / 2) t := by
    rw [eventually_all_finset]
    intro k hk
    by_cases hne : (I'.erase k).Nonempty
    · have hlt : (I'.erase k).card + J'.card < N := by
        rw [← hN, card_erase_of_mem hk]; have := hI.card_pos; omega
      filter_upwards [IH _ hlt (I'.erase k) J' hne hJ rfl (ε / 2) hε'] with t ht _ using ht
    · exact Eventually.of_forall fun t h' => absurd h' hne
  have hcol : ∀ᶠ t in atTop, ∀ l ∈ J', ∀ h' : (J'.erase l).Nonempty,
      Good A I' (J'.erase l) hI h' (ε / 2) t := by
    rw [eventually_all_finset]
    intro l hl
    by_cases hne : (J'.erase l).Nonempty
    · have hlt : I'.card + (J'.erase l).card < N := by
        rw [← hN, card_erase_of_mem hl]; have := hJ.card_pos; omega
      filter_upwards [IH _ hlt I' (J'.erase l) hI hne rfl (ε / 2) hε'] with t ht _ using ht
    · exact Eventually.of_forall fun t h' => absurd h' hne
  obtain ⟨tS, hrowS, hcolS, htS⟩ := (hrow.and (hcol.and (eventually_ge_atTop 1))).exists
  have htS' : (0 : ℝ) ≤ tS := Nat.cast_nonneg _
  -- every system has gap at most `4a tS + (ε/2) t`
  have key : ∀ (U : ℕ → I → ℝ) (V : ℕ → J → ℝ) (i : ℕ → I) (j : ℕ → J) (T : ℕ),
      IsSystem A I' J' U V i j T → I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0) →
      ∀ t ≤ T, gap I' J' hI hJ U V t ≤ 4 * a * tS + ε / 2 * t := by
    intro U V i j T h hinit t
    induction t using Nat.strong_induction_on with
    | _ t IHt =>
    intro htT
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    by_cases hlt : t < tS
    · have h1 := gap_le h ha hI hJ (σ := 0) (n := t) (by omega)
      rw [zero_add] at h1
      have h0 : gap I' J' hI hJ U V 0 ≤ 0 := by unfold gap; linarith
      have h2 : (t : ℝ) ≤ tS := by exact_mod_cast hlt.le
      nlinarith [mul_le_mul_of_nonneg_left h2 ha0, mul_nonneg hε'.le ht0]
    rw [not_lt] at hlt
    obtain ⟨s, rfl⟩ : ∃ s, t = s + tS := ⟨t - tS, by omega⟩
    have hs := IHt s (by omega) (by omega)
    push_cast
    by_cases hb : ∃ k ∈ I', ∀ τ ≤ tS, U (s + τ) k < I'.sup' hI (U (s + τ))
    · obtain ⟨k, hk, hnot⟩ := hb
      have hne : (I'.erase k).Nonempty := by
        refine ⟨i s, mem_erase.2 ⟨fun he => ?_, h.memI s (by omega)⟩⟩
        have h1 := hnot 0 (Nat.zero_le _)
        rw [add_zero] at h1
        have h2 : I'.sup' hI (U s) ≤ U s (i s) := sup'_le _ _ (h.bestI s (by omega))
        rw [he] at h2
        linarith
      have := erase_step h hI hJ (by omega : s + tS ≤ T) hnot hne (hrowS k hk hne)
      linarith
    by_cases hc : ∃ l ∈ J', ∀ τ ≤ tS, J'.inf' hJ (V (s + τ)) < V (s + τ) l
    · obtain ⟨l, hl, hnot⟩ := hc
      have hne : (J'.erase l).Nonempty := by
        refine ⟨j s, mem_erase.2 ⟨fun he => ?_, h.memJ s (by omega)⟩⟩
        have h1 := hnot 0 (Nat.zero_le _)
        rw [add_zero] at h1
        have h2 : V s (j s) ≤ J'.inf' hJ (V s) := le_inf' _ _ (h.bestJ s (by omega))
        rw [he] at h2
        linarith
      have := erase_stepJ h hI hJ (by omega : s + tS ≤ T) hnot hne (hcolS l hl hne)
      linarith
    -- every row and every column is a best response somewhere in the window
    have hrow' : ∀ k ∈ I', ∃ σ, s + tS - tS ≤ σ ∧ σ ≤ s + tS ∧ U σ k = I'.sup' hI (U σ) := by
      intro k hk
      by_contra hcon
      refine hb ⟨k, hk, fun τ hτ => lt_of_le_of_ne (le_sup' _ hk) fun heq => hcon ⟨s + τ,
        by omega, by omega, heq⟩⟩
    have hcol' : ∀ l ∈ J', ∃ σ, s + tS - tS ≤ σ ∧ σ ≤ s + tS ∧ V σ l = J'.inf' hJ (V σ) := by
      intro l hl
      by_contra hcon
      refine hc ⟨l, hl, fun τ hτ => lt_of_le_of_ne (inf'_le _ hl) fun heq => hcon ⟨s + τ,
        by omega, by omega, heq.symm⟩⟩
    have := gap_le_of_eligible (h.mono htT) ha hI hJ (by omega) hinit (n := tS) (by omega)
      hrow' hcol'
    nlinarith [mul_nonneg hε'.le ht0]
  -- conclude
  obtain ⟨T0, hT0⟩ := exists_nat_gt (8 * a * tS / ε)
  filter_upwards [eventually_gt_atTop T0] with t ht
  intro U V i j h hinit
  have h1 := key U V i j t h hinit t le_rfl
  have ht' : 8 * a * tS / ε < t := hT0.trans (by exact_mod_cast ht)
  rw [div_lt_iff₀ hε] at ht'
  linarith

/-! ### Fictitious play -/

variable [Fintype I] [Fintype J]

/-- Cumulative payoff of row `k` against the columns played before `t`. -/
def rowPay (A : I → J → ℝ) (j : ℕ → J) (t : ℕ) (k : I) : ℝ := ∑ τ ∈ range t, A k (j τ)

/-- Cumulative payoff (to the row player) of column `l` against the rows
played before `t`. -/
def colPay (A : I → J → ℝ) (i : ℕ → I) (t : ℕ) (l : J) : ℝ := ∑ τ ∈ range t, A (i τ) l

/-- A fictitious-play path of the zero-sum game `A`. -/
def IsFPPath (A : I → J → ℝ) (i : ℕ → I) (j : ℕ → J) : Prop :=
  ∀ t, (∀ k, rowPay A j t k ≤ rowPay A j t (i t)) ∧ ∀ l, colPay A i t (j t) ≤ colPay A i t l

omit [DecidableEq I] [DecidableEq J] in
theorem IsFPPath.isSystem (h : IsFPPath A i j) (T : ℕ) :
    IsSystem A univ univ (rowPay A j) (colPay A i) i j T where
  memI _ _ := mem_univ _
  bestI τ _ k _ := (h τ).1 k
  memJ _ _ := mem_univ _
  bestJ τ _ l _ := (h τ).2 l
  updU τ _ k := by simp [rowPay, sum_range_succ]
  updV τ _ l := by simp [colPay, sum_range_succ]

/-- Empirical frequency of row `k` in periods `0, …, t−1`. -/
def rowFreq (i : ℕ → I) (t : ℕ) (k : I) : ℝ := ((range t).filter fun τ => i τ = k).card / t

/-- Empirical frequency of column `l` in periods `0, …, t−1`. -/
def colFreq (j : ℕ → J) (t : ℕ) (l : J) : ℝ := ((range t).filter fun τ => j τ = l).card / t

variable [Nonempty I] [Nonempty J]

/-- Exploitability of the empirical play: the best payoff against the column
frequencies minus the least payoff against the row frequencies. -/
def exploit (A : I → J → ℝ) (i : ℕ → I) (j : ℕ → J) (t : ℕ) : ℝ :=
  (univ.sup' univ_nonempty (rowPay A j t) - univ.inf' univ_nonempty (colPay A i t)) / t

omit [DecidableEq I] [DecidableEq J] in
theorem exploit_nonneg (h : IsFPPath A i j) (t : ℕ) : 0 ≤ exploit A i j t := by
  unfold exploit
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  have hid := sum_identity (h.isSystem t)
  simp only [rowPay, colPay, range_zero, sum_empty, sum_const_zero, sub_zero] at hid
  have s1 : ∑ τ ∈ range t, rowPay A j t (i τ) ≤ t * univ.sup' univ_nonempty (rowPay A j t) := by
    have := sum_le_sum (s := range t) (g := fun _ => univ.sup' univ_nonempty (rowPay A j t))
      (f := fun τ => rowPay A j t (i τ)) fun τ _ => le_sup' (rowPay A j t) (mem_univ (i τ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have s2 : (t : ℝ) * univ.inf' univ_nonempty (colPay A i t) ≤
      ∑ τ ∈ range t, colPay A i t (j τ) := by
    have := sum_le_sum (s := range t) (f := fun _ => univ.inf' univ_nonempty (colPay A i t))
      (g := fun τ => colPay A i t (j τ)) fun τ _ => inf'_le (colPay A i t) (mem_univ (j τ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  simp only [rowPay, colPay] at s1 s2
  by_contra hc
  rw [not_le, sub_neg] at hc
  nlinarith

omit [DecidableEq I] [DecidableEq J] in
/-- **Robinson's theorem**: along any fictitious-play path of a zero-sum
game, the exploitability of the empirical frequencies tends to `0`. -/
theorem robinson (h : IsFPPath A i j) : Tendsto (exploit A i j) atTop (𝓝 0) := by
  classical
  set a : ℝ := ∑ k, ∑ l, |A k l|
  have ha : ∀ k l, |A k l| ≤ a := fun k l =>
    (single_le_sum (f := fun l => |A k l|) (fun _ _ => abs_nonneg _) (mem_univ l)).trans
      (single_le_sum (f := fun k => ∑ l, |A k l|) (fun _ _ => sum_nonneg fun _ _ =>
        abs_nonneg _) (mem_univ k))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_good ha _ univ univ univ_nonempty
    univ_nonempty rfl ε hε)
  refine ⟨max N 1, fun t ht => ?_⟩
  have h1 := hN t (le_of_max_le_left ht) _ _ _ _ (h.isSystem t)
    (by simp [rowPay, colPay])
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (exploit_nonneg h t), exploit, div_lt_iff₀ ht']
  exact h1

omit [Nonempty I] [Nonempty J] [DecidableEq I] [Fintype I] in
theorem rowPay_eq (A : I → J → ℝ) (j : ℕ → J) (t : ℕ) (k : I) :
    rowPay A j t k = t * ∑ l, A k l * colFreq j t l := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [rowPay]
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [rowPay, ← sum_fiberwise' (range t) j (fun l => A k l), mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_const, colFreq, nsmul_eq_mul]
  field_simp

omit [Nonempty I] [Nonempty J] [DecidableEq J] [Fintype J] in
theorem colPay_eq (A : I → J → ℝ) (i : ℕ → I) (t : ℕ) (l : J) :
    colPay A i t l = t * ∑ k, rowFreq i t k * A k l := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [colPay]
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [colPay, ← sum_fiberwise' (range t) i (fun k => A k l), mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_const, rowFreq, nsmul_eq_mul]
  field_simp

omit [Nonempty I] [Nonempty J] [DecidableEq J] in
theorem rowFreq_mem (i : ℕ → I) {t : ℕ} (ht : 0 < t) : rowFreq i t ∈ lotteries I := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun k => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  simp only [rowFreq, ← sum_div]
  rw [div_eq_one_iff_eq ht']
  have := card_eq_sum_card_fiberwise (f := i) (s := range t) (t := univ) (fun _ _ => mem_univ _)
  rw [card_range] at this
  exact_mod_cast this.symm

omit [Nonempty I] [Nonempty J] [DecidableEq I] in
theorem colFreq_mem (j : ℕ → J) {t : ℕ} (ht : 0 < t) : colFreq j t ∈ lotteries J := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun l => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  simp only [colFreq, ← sum_div]
  rw [div_eq_one_iff_eq ht']
  have := card_eq_sum_card_fiberwise (f := j) (s := range t) (t := univ) (fun _ _ => mem_univ _)
  rw [card_range] at this
  exact_mod_cast this.symm

omit [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J] in
theorem matrixPayoff_eq_left (A : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) :
    matrixPayoff A x y = ∑ k, x k * ∑ l, A k l * y l := by
  simp only [matrixPayoff, mul_sum]
  exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring

omit [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J] in
theorem matrixPayoff_eq_right (A : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) :
    matrixPayoff A x y = ∑ l, (∑ k, x k * A k l) * y l := by
  rw [matrixPayoff, sum_comm]
  simp only [sum_mul]

omit [DecidableEq I] [Nonempty J] in
/-- Against the column frequencies, no mixed strategy earns more than the best
row's average payoff `max_k rowPay_t(k) / t`. -/
theorem payoff_le_max (A : I → J → ℝ) (j : ℕ → J) {t : ℕ} (ht : 0 < t) {x : I → ℝ}
    (hx : x ∈ lotteries I) :
    matrixPayoff A x (colFreq j t) ≤ univ.sup' univ_nonempty (rowPay A j t) / t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hrow : ∀ k, ∑ l, A k l * colFreq j t l ≤ univ.sup' univ_nonempty (rowPay A j t) / t :=
    fun k => by
      rw [le_div_iff₀ ht', mul_comm, ← rowPay_eq]
      exact le_sup' (rowPay A j t) (mem_univ k)
  rw [matrixPayoff_eq_left]
  calc ∑ k, x k * ∑ l, A k l * colFreq j t l
      ≤ ∑ k, x k * (univ.sup' univ_nonempty (rowPay A j t) / t) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hrow k) (hx.1 k)
    _ = _ := by rw [← sum_mul, hx.2, one_mul]

omit [DecidableEq J] [Nonempty I] in
/-- Against the row frequencies, no mixed strategy pays less than the best
column's average `min_l colPay_t(l) / t`. -/
theorem min_le_payoff (A : I → J → ℝ) (i : ℕ → I) {t : ℕ} (ht : 0 < t) {y : J → ℝ}
    (hy : y ∈ lotteries J) :
    univ.inf' univ_nonempty (colPay A i t) / t ≤ matrixPayoff A (rowFreq i t) y := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hcol : ∀ l, univ.inf' univ_nonempty (colPay A i t) / t ≤ ∑ k, rowFreq i t k * A k l :=
    fun l => by
      rw [div_le_iff₀ ht', mul_comm, ← colPay_eq]
      exact inf'_le (colPay A i t) (mem_univ l)
  rw [matrixPayoff_eq_right]
  calc univ.inf' univ_nonempty (colPay A i t) / t
      = ∑ l, univ.inf' univ_nonempty (colPay A i t) / t * y l := by
        rw [← mul_sum, hy.2, mul_one]
    _ ≤ _ := sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hcol l) (hy.1 l)

/-- Any empirical frequencies are an `exploit`-saddle point (an identity, valid
for arbitrary sequences of play). -/
theorem isEpsSaddle_freq (A : I → J → ℝ) (i : ℕ → I) (j : ℕ → J) {t : ℕ} (ht : 0 < t) :
    (∀ x ∈ lotteries I, matrixPayoff A x (colFreq j t) ≤
      matrixPayoff A (rowFreq i t) (colFreq j t) + exploit A i j t) ∧
    ∀ y ∈ lotteries J, matrixPayoff A (rowFreq i t) (colFreq j t) - exploit A i j t ≤
      matrixPayoff A (rowFreq i t) y := by
  have hex : exploit A i j t = univ.sup' univ_nonempty (rowPay A j t) / t -
      univ.inf' univ_nonempty (colPay A i t) / t := by simp only [exploit, sub_div]
  have h1 := payoff_le_max A j ht (rowFreq_mem i ht)
  have h2 := min_le_payoff A i ht (colFreq_mem j ht)
  rw [hex]
  exact ⟨fun x hx => by linarith [payoff_le_max A j ht hx],
    fun y hy => by linarith [min_le_payoff A i ht hy]⟩

/-- **The empirical frequencies are eventually an `ε`-equilibrium.** -/
theorem eventually_isEpsSaddle (h : IsFPPath A i j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, rowFreq i t ∈ lotteries I ∧ colFreq j t ∈ lotteries J ∧
      (∀ x ∈ lotteries I, matrixPayoff A x (colFreq j t) ≤
        matrixPayoff A (rowFreq i t) (colFreq j t) + ε) ∧
      ∀ y ∈ lotteries J, matrixPayoff A (rowFreq i t) (colFreq j t) - ε ≤
        matrixPayoff A (rowFreq i t) y := by
  filter_upwards [(robinson h).eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with t h1 ht
  obtain ⟨h2, h3⟩ := isEpsSaddle_freq A i j ht
  exact ⟨rowFreq_mem i ht, colFreq_mem j ht, fun x hx => by linarith [h2 x hx],
    fun y hy => by linarith [h3 y hy]⟩

/-- **The empirical payoff converges to the value of the game.** -/
theorem tendsto_payoff_value (h : IsFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => matrixPayoff A (rowFreq i t) (colFreq j t)) atTop (𝓝 v) := by
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := hv
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((robinson h).eventually (gt_mem_nhds hε) |>.and (eventually_gt_atTop 0))
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hN t ht
  obtain ⟨h3, h4⟩ := isEpsSaddle_freq A i j h2
  have a1 := hxv _ (colFreq_mem j h2)
  have a2 := hyv _ (rowFreq_mem i h2)
  have b1 := h3 x hx
  have b2 := h4 y hy
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Robinson's theorem in her form**: the best row's average payoff
`max_k U(t)_k / t` and the best column's `min_l V(t)_l / t` both converge to the
value of the game. -/
theorem tendsto_max_min_value (h : IsFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => univ.sup' univ_nonempty (rowPay A j t) / t) atTop (𝓝 v) ∧
    Tendsto (fun t => univ.inf' univ_nonempty (colPay A i t) / t) atTop (𝓝 v) := by
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := hv
  have hex : ∀ t, exploit A i j t = univ.sup' univ_nonempty (rowPay A j t) / t -
      univ.inf' univ_nonempty (colPay A i t) / t := fun t => by simp only [exploit, sub_div]
  -- `v ≤ max/t`, `min/t ≤ v` and `max/t − min/t = exploit → 0`
  have hlo : ∀ᶠ t in atTop, v ≤ univ.sup' univ_nonempty (rowPay A j t) / t ∧
      univ.inf' univ_nonempty (colPay A i t) / t ≤ v := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact ⟨(hxv _ (colFreq_mem j ht)).trans (payoff_le_max A j ht hx),
      (min_le_payoff A i ht hy).trans (hyv _ (rowFreq_mem i ht))⟩
  have hr := robinson h
  constructor
  · have hup : Tendsto (fun t => v + exploit A i j t) atTop (𝓝 v) := by
      simpa using hr.const_add v
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hlo] with t ht using ht.1
    · filter_upwards [hlo] with t ht
      rw [hex]; linarith [ht.2]
  · have hdn : Tendsto (fun t => v - exploit A i j t) atTop (𝓝 v) := by
      simpa using hr.const_sub v
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdn tendsto_const_nhds ?_ ?_
    · filter_upwards [hlo] with t ht
      rw [hex]; linarith [ht.1]
    · filter_upwards [hlo] with t ht using ht.2

/-! ### Existence of fictitious-play paths -/

/-- A maximizer of `f`. -/
def argmaxI (f : I → ℝ) : I := (exists_max_image univ f univ_nonempty).choose

/-- A minimizer of `f`. -/
def argminJ (f : J → ℝ) : J := (exists_min_image univ f univ_nonempty).choose

omit [DecidableEq I] [DecidableEq J] [Nonempty J] [Fintype J] in
theorem le_argmaxI (f : I → ℝ) (k : I) : f k ≤ f (argmaxI f) :=
  (exists_max_image univ f univ_nonempty).choose_spec.2 k (mem_univ k)

omit [DecidableEq I] [DecidableEq J] [Nonempty I] [Fintype I] in
theorem argminJ_le (f : J → ℝ) (l : J) : f (argminJ f) ≤ f l :=
  (exists_min_image univ f univ_nonempty).choose_spec.2 l (mem_univ l)

/-- Cumulative payoff vectors along the canonical fictitious-play path. -/
def fpState (A : I → J → ℝ) : ℕ → (I → ℝ) × (J → ℝ)
  | 0 => (0, 0)
  | t + 1 => ((fun k => (fpState A t).1 k + A k (argminJ (fpState A t).2)),
      (fun l => (fpState A t).2 l + A (argmaxI (fpState A t).1) l))

/-- The canonical fictitious-play path. -/
def fpRow (A : I → J → ℝ) (t : ℕ) : I := argmaxI (fpState A t).1

def fpCol (A : I → J → ℝ) (t : ℕ) : J := argminJ (fpState A t).2

omit [DecidableEq I] [DecidableEq J] in
theorem fpState_eq (A : I → J → ℝ) (t : ℕ) :
    fpState A t = (rowPay A (fpCol A) t, colPay A (fpRow A) t) := by
  induction t with
  | zero => ext <;> simp [fpState, rowPay, colPay]
  | succ t ih =>
    simp only [fpState, ih, Prod.mk.injEq]
    constructor <;> funext x <;> simp [rowPay, colPay, sum_range_succ, fpRow, fpCol, ih]

omit [DecidableEq I] [DecidableEq J] in
/-- Non-vacuity: fictitious-play paths exist. -/
theorem isFPPath_fp (A : I → J → ℝ) : IsFPPath A (fpRow A) (fpCol A) := by
  intro t
  have e := fpState_eq A t
  refine ⟨fun k => ?_, fun l => ?_⟩
  · have := le_argmaxI (fpState A t).1 k
    rw [e] at this
    simpa [fpRow, e] using this
  · have := argminJ_le (fpState A t).2 l
    rw [e] at this
    simpa [fpCol, e] using this

end Robinson

end Econ
