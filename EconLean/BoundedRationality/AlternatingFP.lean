/-
# Brown's alternating fictitious play

References. G. W. Brown (1951), "Iterative Solution of Games by Fictitious
Play"; J. Robinson (1951), "An Iterative Method of Solving a Game", *Annals of
Mathematics* 54(2) (whose proof is adapted here; she notes it covers Brown's
alternating process).

In Brown's original process the players move in turn: at date `t` the row
player best responds to the columns played at dates `0, …, t−1`, and then the
column player best responds to the rows played at dates `0, …, t`, including
the one just chosen (`IsAltFPPath`). This is not a simultaneous
fictitious-play path (`Robinson.lean`), and there is no evident way to
rewrite it as one (informal remark, not formalized), but the
column player's choice is a best response to the rows before `t` up to an
error of at most `2a`, where `a` bounds `|A|`.

**Results.**
* `IsSystemS`, `eventually_goodS` (Robinson's lemma with slack): Robinson's
  induction goes through for vector systems in which the chosen row and
  column are only `δ`-best responses, for any fixed `δ ≥ 0`: for every
  `ε > 0`, eventually `max U(t) − min V(t) < εt`.
* `IsAltFPPath.isSystemS`: an alternating path is a vector system with slack
  `2a`.
* `robinson_alt`: along an alternating fictitious-play path the
  exploitability of the empirical frequencies tends to `0`; hence
  `eventually_isEpsSaddle_alt` (eventually an `ε`-saddle point),
  `tendsto_payoff_value_alt` and `tendsto_max_min_value_alt` (convergence to
  the value of the game).
* Non-vacuity: alternating paths exist (`altRow`, `altCol`,
  `isAltFPPath_alt`).
-/
module

public import EconLean.BoundedRationality.Robinson

@[expose] public section

noncomputable section

namespace Econ

namespace Robinson

open Finset Filter Topology

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-! ### Vector systems with slack -/

/-- A vector system in which the chosen row and column are `δ`-best
responses. -/
structure IsSystemS (A : I → J → ℝ) (I' : Finset I) (J' : Finset J) (U : ℕ → I → ℝ)
    (V : ℕ → J → ℝ) (i : ℕ → I) (j : ℕ → J) (T : ℕ) (δ : ℝ) : Prop where
  memI : ∀ τ < T, i τ ∈ I'
  bestI : ∀ τ < T, ∀ k ∈ I', U τ k ≤ U τ (i τ) + δ
  memJ : ∀ τ < T, j τ ∈ J'
  bestJ : ∀ τ < T, ∀ l ∈ J', V τ (j τ) ≤ V τ l + δ
  updU : ∀ τ < T, ∀ k, U (τ + 1) k = U τ k + A k (j τ)
  updV : ∀ τ < T, ∀ l, V (τ + 1) l = V τ l + A (i τ) l

variable {A : I → J → ℝ} {I' : Finset I} {J' : Finset J} {U : ℕ → I → ℝ} {V : ℕ → J → ℝ}
  {i : ℕ → I} {j : ℕ → J} {T : ℕ} {a δ : ℝ}

omit [DecidableEq I] [DecidableEq J] in
/-- An exact vector system is a system with slack `0`. -/
theorem IsSystem.isSystemS (h : IsSystem A I' J' U V i j T) : IsSystemS A I' J' U V i j T 0 :=
  ⟨h.memI, fun τ hτ k hk => by rw [add_zero]; exact h.bestI τ hτ k hk, h.memJ,
    fun τ hτ l hl => by rw [add_zero]; exact h.bestJ τ hτ l hl, h.updU, h.updV⟩

omit [DecidableEq I] [DecidableEq J] in
theorem IsSystemS.mono (h : IsSystemS A I' J' U V i j T δ) {T' : ℕ} (hT : T' ≤ T) :
    IsSystemS A I' J' U V i j T' δ :=
  ⟨fun τ hτ => h.memI τ (by omega), fun τ hτ => h.bestI τ (by omega),
    fun τ hτ => h.memJ τ (by omega), fun τ hτ => h.bestJ τ (by omega),
    fun τ hτ => h.updU τ (by omega), fun τ hτ => h.updV τ (by omega)⟩

omit [DecidableEq I] [DecidableEq J] in
theorem U_boundsS (h : IsSystemS A I' J' U V i j T δ) (ha : ∀ k l, |A k l| ≤ a) {σ n : ℕ}
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
theorem V_boundsS (h : IsSystemS A I' J' U V i j T δ) (ha : ∀ k l, |A k l| ≤ a) {σ n : ℕ}
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
theorem gap_leS (h : IsSystemS A I' J' U V i j T δ) (ha : ∀ k l, |A k l| ≤ a)
    (hI : I'.Nonempty) (hJ : J'.Nonempty) {σ n : ℕ} (hσ : σ + n ≤ T) :
    gap I' J' hI hJ U V (σ + n) ≤ gap I' J' hI hJ U V σ + 2 * a * n := by
  have h1 : I'.sup' hI (U (σ + n)) ≤ I'.sup' hI (U σ) + a * n :=
    sup'_le _ _ fun k hk => (U_boundsS h ha hσ k).2.trans (by linarith [le_sup' (U σ) hk])
  have h2 : J'.inf' hJ (V σ) - a * n ≤ J'.inf' hJ (V (σ + n)) :=
    le_inf' _ _ fun l hl => le_trans (by linarith [inf'_le (V σ) hl]) (V_boundsS h ha hσ l).1
  unfold gap; linarith

omit [DecidableEq I] [DecidableEq J] in
theorem U_eq_sumS (h : IsSystemS A I' J' U V i j T δ) :
    ∀ n ≤ T, ∀ k, U n k = U 0 k + ∑ σ ∈ range n, A k (j σ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => intro hn k; rw [h.updU n (by omega), ih (by omega), sum_range_succ]; ring

omit [DecidableEq I] [DecidableEq J] in
theorem V_eq_sumS (h : IsSystemS A I' J' U V i j T δ) :
    ∀ n ≤ T, ∀ l, V n l = V 0 l + ∑ σ ∈ range n, A (i σ) l := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => intro hn l; rw [h.updV n (by omega), ih (by omega), sum_range_succ]; ring

omit [DecidableEq I] [DecidableEq J] in
/-- Robinson's identity (it does not use the best-response conditions). -/
theorem sum_identityS (h : IsSystemS A I' J' U V i j T δ) :
    ∑ τ ∈ range T, U T (i τ) - ∑ τ ∈ range T, V T (j τ) =
      ∑ τ ∈ range T, U 0 (i τ) - ∑ τ ∈ range T, V 0 (j τ) := by
  simp only [U_eq_sumS h T le_rfl, V_eq_sumS h T le_rfl, sum_add_distrib]
  have := sum_comm (s := range T) (t := range T) (f := fun τ σ => A (i τ) (j σ))
  linarith

omit [DecidableEq I] [DecidableEq J] in
/-- If every row and column is a `δ`-best response at some date in
`[T − n, T]`, the gap at `T` is at most `4an + 2δ`. -/
theorem gap_le_of_eligibleS (h : IsSystemS A I' J' U V i j T δ) (ha : ∀ k l, |A k l| ≤ a)
    (hI : I'.Nonempty) (hJ : J'.Nonempty) (hT : 0 < T)
    (hinit : I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0)) {n : ℕ} (hn : n ≤ T)
    (hrow : ∀ k ∈ I', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ I'.sup' hI (U σ) ≤ U σ k + δ)
    (hcol : ∀ l ∈ J', ∃ σ, T - n ≤ σ ∧ σ ≤ T ∧ V σ l ≤ J'.inf' hJ (V σ) + δ) :
    gap I' J' hI hJ U V T ≤ 4 * a * n + 2 * δ := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha hI.choose hJ.choose)
  have hk : ∀ k ∈ I', I'.sup' hI (U T) - 2 * a * n - δ ≤ U T k := by
    intro k hk
    obtain ⟨σ, h1, h2, he⟩ := hrow k hk
    have hσ : σ + (T - σ) = T := by omega
    have b1 : I'.sup' hI (U T) ≤ I'.sup' hI (U σ) + a * (T - σ : ℕ) := by
      rw [← hσ]
      exact sup'_le _ _ fun k' hk' => (U_boundsS h ha (n := T - σ) (by omega) k').2.trans
        (by rw [hσ]; linarith [le_sup' (U σ) hk'])
    have b2 := (U_boundsS h ha (σ := σ) (n := T - σ) (by omega) k).1
    rw [hσ] at b2
    have : (((T - σ : ℕ)) : ℝ) ≤ n := by exact_mod_cast (by omega : T - σ ≤ n)
    nlinarith
  have hl : ∀ l ∈ J', V T l ≤ J'.inf' hJ (V T) + 2 * a * n + δ := by
    intro l hl
    obtain ⟨σ, h1, h2, he⟩ := hcol l hl
    have hσ : σ + (T - σ) = T := by omega
    have b1 : J'.inf' hJ (V σ) - a * (T - σ : ℕ) ≤ J'.inf' hJ (V T) := by
      rw [← hσ]
      exact le_inf' _ _ fun l' hl' => le_trans (by rw [hσ]; linarith [inf'_le (V σ) hl'])
        (V_boundsS h ha (n := T - σ) (by omega) l').1
    have b2 := (V_boundsS h ha (σ := σ) (n := T - σ) (by omega) l).2
    rw [hσ] at b2
    have : (((T - σ : ℕ)) : ℝ) ≤ n := by exact_mod_cast (by omega : T - σ ≤ n)
    nlinarith
  have s1 : (T : ℝ) * (I'.sup' hI (U T) - 2 * a * n - δ) ≤ ∑ τ ∈ range T, U T (i τ) := by
    have := sum_le_sum (s := range T) (f := fun _ => I'.sup' hI (U T) - 2 * a * n - δ)
      (g := fun τ => U T (i τ)) fun τ hτ => hk (i τ) (h.memI τ (mem_range.1 hτ))
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have s2 : ∑ τ ∈ range T, V T (j τ) ≤ (T : ℝ) * (J'.inf' hJ (V T) + 2 * a * n + δ) := by
    have := sum_le_sum (s := range T) (g := fun _ => J'.inf' hJ (V T) + 2 * a * n + δ)
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
  have hid := sum_identityS h
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have key : (T : ℝ) * (gap I' J' hI hJ U V T - 4 * a * n - 2 * δ) ≤ 0 := by
    unfold gap; nlinarith
  by_contra hc
  rw [not_le] at hc
  linarith [mul_pos hT' (sub_pos.2 (show 4 * a * n + 2 * δ < gap I' J' hI hJ U V T from hc))]

/-- The induction property with slack `δ`. -/
def GoodS (A : I → J → ℝ) (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty)
    (hJ : J'.Nonempty) (δ ε : ℝ) (t : ℕ) : Prop :=
  ∀ (U : ℕ → I → ℝ) (V : ℕ → J → ℝ) (i : ℕ → I) (j : ℕ → J), IsSystemS A I' J' U V i j t δ →
    I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0) → gap I' J' hI hJ U V t < ε * t

omit [DecidableEq I] [DecidableEq J] in
theorem IsSystemS.transpose (h : IsSystemS A I' J' U V i j T δ) :
    IsSystemS (fun l k => -A k l) J' I' (fun τ l => -V τ l) (fun τ k => -U τ k) j i T δ where
  memI := h.memJ
  bestI τ hτ l hl := by linarith [h.bestJ τ hτ l hl]
  memJ := h.memI
  bestJ τ hτ k hk := by linarith [h.bestI τ hτ k hk]
  updU τ hτ l := by rw [h.updV τ hτ l]; ring
  updV τ hτ k := by rw [h.updU τ hτ k]; ring

omit [DecidableEq I] [DecidableEq J] in
theorem GoodS.transpose {hI : I'.Nonempty} {hJ : J'.Nonempty} {ε : ℝ} {t : ℕ}
    (h : GoodS A I' J' hI hJ δ ε t) : GoodS (fun l k => -A k l) J' I' hJ hI δ ε t := by
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
/-- Deleting a row that is never a `δ`-best response. -/
theorem erase_stepS (h : IsSystemS A I' J' U V i j T δ) (hδ : 0 ≤ δ) (hI : I'.Nonempty)
    (hJ : J'.Nonempty) {s n : ℕ} (hsn : s + n ≤ T) {k : I}
    (hnot : ∀ τ ≤ n, U (s + τ) k + δ < I'.sup' hI (U (s + τ))) (hI' : (I'.erase k).Nonempty)
    {ε : ℝ} (hgood : GoodS A (I'.erase k) J' hI' hJ δ ε n) :
    gap I' J' hI hJ U V (s + n) < gap I' J' hI hJ U V s + ε * n := by
  set d := gap I' J' hI hJ U V s
  have hsys : IsSystemS A (I'.erase k) J' (fun τ => U (s + τ)) (fun τ l => V (s + τ) l + d)
      (fun τ => i (s + τ)) (fun τ => j (s + τ)) n δ :=
    { memI := fun τ hτ => by
        refine mem_erase.2 ⟨fun he => ?_, h.memI _ (by omega)⟩
        have h1 := hnot τ hτ.le
        have h2 : I'.sup' hI (U (s + τ)) ≤ U (s + τ) (i (s + τ)) + δ :=
          sup'_le _ _ (h.bestI _ (by omega))
        rw [he] at h2
        linarith
      bestI := fun τ hτ k' hk' => h.bestI _ (by omega) k' (mem_of_mem_erase hk')
      memJ := fun τ hτ => h.memJ _ (by omega)
      bestJ := fun τ hτ l hl => by linarith [h.bestJ (s + τ) (by omega) l hl]
      updU := fun τ hτ k' => by rw [← add_assoc]; exact h.updU _ (by omega) k'
      updV := fun τ hτ l => by
        rw [← add_assoc, h.updV _ (by omega) l]; ring }
  have hlt : ∀ τ ≤ n, U (s + τ) k < I'.sup' hI (U (s + τ)) := fun τ hτ => by
    linarith [hnot τ hτ]
  have h0 := hlt 0 (Nat.zero_le _)
  rw [add_zero] at h0
  have hinit : (I'.erase k).sup' hI' (U s) ≤ J'.inf' hJ (fun l => V s l + d) := by
    rw [inf'_add_const, sup'_erase_eq hI h0 hI']
    simp only [d, gap]; linarith
  have := hgood _ _ _ _ hsys hinit
  unfold gap at this
  dsimp only at this
  rw [inf'_add_const, sup'_erase_eq hI (hlt n le_rfl) hI'] at this
  unfold gap
  linarith

omit [DecidableEq I] in
/-- Deleting a column that is never a `δ`-best response. -/
theorem erase_stepJS (h : IsSystemS A I' J' U V i j T δ) (hδ : 0 ≤ δ) (hI : I'.Nonempty)
    (hJ : J'.Nonempty) {s n : ℕ} (hsn : s + n ≤ T) {l : J}
    (hnot : ∀ τ ≤ n, J'.inf' hJ (V (s + τ)) + δ < V (s + τ) l) (hJ' : (J'.erase l).Nonempty)
    {ε : ℝ} (hgood : GoodS A I' (J'.erase l) hI hJ' δ ε n) :
    gap I' J' hI hJ U V (s + n) < gap I' J' hI hJ U V s + ε * n := by
  have ht := erase_stepS h.transpose hδ hJ hI hsn (k := l) (fun τ hτ => by
    show -V (s + τ) l + δ < J'.sup' hJ (fun l => -V (s + τ) l)
    rw [sup'_neg]; linarith [hnot τ hτ]) hJ' hgood.transpose
  rwa [gap_transpose, gap_transpose] at ht

/-- **Robinson's lemma with slack**: for every submatrix, every `δ ≥ 0` and
every `ε > 0`, eventually every `δ`-vector system has gap `< εt`. -/
theorem eventually_goodS (ha : ∀ k l, |A k l| ≤ a) (hδ : 0 ≤ δ) :
    ∀ (N : ℕ) (I' : Finset I) (J' : Finset J) (hI : I'.Nonempty) (hJ : J'.Nonempty),
      I'.card + J'.card = N → ∀ ε > 0, ∀ᶠ t in atTop, GoodS A I' J' hI hJ δ ε t := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro I' J' hI hJ hN ε hε
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha hI.choose hJ.choose)
  have hε' : 0 < ε / 2 := by positivity
  have hrow : ∀ᶠ t in atTop, ∀ k ∈ I', ∀ h' : (I'.erase k).Nonempty,
      GoodS A (I'.erase k) J' h' hJ δ (ε / 2) t := by
    rw [eventually_all_finset]
    intro k hk
    by_cases hne : (I'.erase k).Nonempty
    · have hlt : (I'.erase k).card + J'.card < N := by
        rw [← hN, card_erase_of_mem hk]; have := hI.card_pos; omega
      filter_upwards [IH _ hlt (I'.erase k) J' hne hJ rfl (ε / 2) hε'] with t ht _ using ht
    · exact Eventually.of_forall fun t h' => absurd h' hne
  have hcol : ∀ᶠ t in atTop, ∀ l ∈ J', ∀ h' : (J'.erase l).Nonempty,
      GoodS A I' (J'.erase l) hI h' δ (ε / 2) t := by
    rw [eventually_all_finset]
    intro l hl
    by_cases hne : (J'.erase l).Nonempty
    · have hlt : I'.card + (J'.erase l).card < N := by
        rw [← hN, card_erase_of_mem hl]; have := hJ.card_pos; omega
      filter_upwards [IH _ hlt I' (J'.erase l) hI hne rfl (ε / 2) hε'] with t ht _ using ht
    · exact Eventually.of_forall fun t h' => absurd h' hne
  obtain ⟨tS, hrowS, hcolS, htS⟩ := (hrow.and (hcol.and (eventually_ge_atTop 1))).exists
  have htS' : (0 : ℝ) ≤ tS := Nat.cast_nonneg _
  have key : ∀ (U : ℕ → I → ℝ) (V : ℕ → J → ℝ) (i : ℕ → I) (j : ℕ → J) (T : ℕ),
      IsSystemS A I' J' U V i j T δ → I'.sup' hI (U 0) ≤ J'.inf' hJ (V 0) →
      ∀ t ≤ T, gap I' J' hI hJ U V t ≤ 4 * a * tS + 2 * δ + ε / 2 * t := by
    intro U V i j T h hinit t
    induction t using Nat.strong_induction_on with
    | _ t IHt =>
    intro htT
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    by_cases hlt : t < tS
    · have h1 := gap_leS h ha hI hJ (σ := 0) (n := t) (by omega)
      rw [zero_add] at h1
      have h0 : gap I' J' hI hJ U V 0 ≤ 0 := by unfold gap; linarith
      have h2 : (t : ℝ) ≤ tS := by exact_mod_cast hlt.le
      nlinarith [mul_le_mul_of_nonneg_left h2 ha0, mul_nonneg hε'.le ht0]
    rw [not_lt] at hlt
    obtain ⟨s, rfl⟩ : ∃ s, t = s + tS := ⟨t - tS, by omega⟩
    have hs := IHt s (by omega) (by omega)
    push_cast
    by_cases hb : ∃ k ∈ I', ∀ τ ≤ tS, U (s + τ) k + δ < I'.sup' hI (U (s + τ))
    · obtain ⟨k, hk, hnot⟩ := hb
      have hne : (I'.erase k).Nonempty := by
        refine ⟨i s, mem_erase.2 ⟨fun he => ?_, h.memI s (by omega)⟩⟩
        have h1 := hnot 0 (Nat.zero_le _)
        rw [add_zero] at h1
        have h2 : I'.sup' hI (U s) ≤ U s (i s) + δ := sup'_le _ _ (h.bestI s (by omega))
        rw [he] at h2
        linarith
      have := erase_stepS h hδ hI hJ (by omega : s + tS ≤ T) hnot hne (hrowS k hk hne)
      linarith
    by_cases hc : ∃ l ∈ J', ∀ τ ≤ tS, J'.inf' hJ (V (s + τ)) + δ < V (s + τ) l
    · obtain ⟨l, hl, hnot⟩ := hc
      have hne : (J'.erase l).Nonempty := by
        refine ⟨j s, mem_erase.2 ⟨fun he => ?_, h.memJ s (by omega)⟩⟩
        have h1 := hnot 0 (Nat.zero_le _)
        rw [add_zero] at h1
        have h2 : V s (j s) ≤ J'.inf' hJ (V s) + δ := by
          have := le_inf' (s := J') hJ (f := fun l => V s l + δ) (a := V s (j s))
            (fun l hl => h.bestJ s (by omega) l hl)
          rwa [inf'_add_const] at this
        rw [he] at h2
        linarith
      have := erase_stepJS h hδ hI hJ (by omega : s + tS ≤ T) hnot hne (hcolS l hl hne)
      linarith
    have hrow' : ∀ k ∈ I', ∃ σ, s + tS - tS ≤ σ ∧ σ ≤ s + tS ∧
        I'.sup' hI (U σ) ≤ U σ k + δ := by
      intro k hk
      by_contra hcon
      refine hb ⟨k, hk, fun τ hτ => lt_of_not_ge fun hge => hcon ⟨s + τ,
        by omega, by omega, hge⟩⟩
    have hcol' : ∀ l ∈ J', ∃ σ, s + tS - tS ≤ σ ∧ σ ≤ s + tS ∧
        V σ l ≤ J'.inf' hJ (V σ) + δ := by
      intro l hl
      by_contra hcon
      refine hc ⟨l, hl, fun τ hτ => lt_of_not_ge fun hge => hcon ⟨s + τ,
        by omega, by omega, hge⟩⟩
    have := gap_le_of_eligibleS (h.mono htT) ha hI hJ (by omega) hinit (n := tS) (by omega)
      hrow' hcol'
    nlinarith [mul_nonneg hε'.le ht0]
  obtain ⟨T0, hT0⟩ := exists_nat_gt ((8 * a * tS + 4 * δ) / ε)
  filter_upwards [eventually_gt_atTop T0] with t ht
  intro U V i j h hinit
  have h1 := key U V i j t h hinit t le_rfl
  have ht' : (8 * a * tS + 4 * δ) / ε < t := hT0.trans (by exact_mod_cast ht)
  rw [div_lt_iff₀ hε] at ht'
  linarith

/-! ### Alternating fictitious play -/

variable [Fintype I] [Fintype J]

/-- **Brown's alternating fictitious play**: the row player best responds to
the columns before `t`, then the column player to the rows up to and including
`t`. -/
def IsAltFPPath (A : I → J → ℝ) (i : ℕ → I) (j : ℕ → J) : Prop :=
  ∀ t, (∀ k, rowPay A j t k ≤ rowPay A j t (i t)) ∧
    ∀ l, colPay A i (t + 1) (j t) ≤ colPay A i (t + 1) l

omit [DecidableEq I] [DecidableEq J] in
/-- An alternating path is a vector system with slack `2a`. -/
theorem IsAltFPPath.isSystemS (h : IsAltFPPath A i j) (ha : ∀ k l, |A k l| ≤ a) (T : ℕ) :
    IsSystemS A univ univ (rowPay A j) (colPay A i) i j T (2 * a) where
  memI _ _ := mem_univ _
  bestI τ _ k _ := by
    have := (h τ).1 k
    have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha k (j τ))
    linarith
  memJ _ _ := mem_univ _
  bestJ τ _ l _ := by
    have h1 := (h τ).2 l
    simp only [colPay, sum_range_succ] at h1
    have h2 := abs_le.1 (ha (i τ) l)
    have h3 := abs_le.1 (ha (i τ) (j τ))
    simp only [colPay]
    linarith
  updU τ _ k := by simp [rowPay, sum_range_succ]
  updV τ _ l := by simp [colPay, sum_range_succ]

variable [Nonempty I] [Nonempty J]

omit [DecidableEq I] [DecidableEq J] in
/-- Exploitability is nonnegative for any sequences of play. -/
theorem exploit_nonneg' (A : I → J → ℝ) (i : ℕ → I) (j : ℕ → J) (t : ℕ) :
    0 ≤ exploit A i j t := by
  unfold exploit
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  have hid : ∑ τ ∈ range t, rowPay A j t (i τ) = ∑ τ ∈ range t, colPay A i t (j τ) := by
    simp only [rowPay, colPay]; exact sum_comm
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
  by_contra hc
  rw [not_le, sub_neg] at hc
  nlinarith

omit [DecidableEq I] [DecidableEq J] in
/-- **Robinson's theorem for Brown's alternating process.** -/
theorem robinson_alt (h : IsAltFPPath A i j) : Tendsto (exploit A i j) atTop (𝓝 0) := by
  classical
  set a : ℝ := ∑ k, ∑ l, |A k l|
  have ha : ∀ k l, |A k l| ≤ a := fun k l =>
    (single_le_sum (f := fun l => |A k l|) (fun _ _ => abs_nonneg _) (mem_univ l)).trans
      (single_le_sum (f := fun k => ∑ l, |A k l|) (fun _ _ => sum_nonneg fun _ _ =>
        abs_nonneg _) (mem_univ k))
  have ha0 : 0 ≤ a := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_goodS ha (by linarith : 0 ≤ 2 * a) _ univ
    univ univ_nonempty univ_nonempty rfl ε hε)
  refine ⟨max N 1, fun t ht => ?_⟩
  have h1 := hN t (le_of_max_le_left ht) _ _ _ _ (h.isSystemS ha t)
    (by simp [rowPay, colPay])
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (exploit_nonneg' A i j t), exploit, div_lt_iff₀ ht']
  exact h1

/-- **The empirical frequencies of alternating play are eventually an
`ε`-equilibrium.** -/
theorem eventually_isEpsSaddle_alt (h : IsAltFPPath A i j) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, rowFreq i t ∈ lotteries I ∧ colFreq j t ∈ lotteries J ∧
      (∀ x ∈ lotteries I, matrixPayoff A x (colFreq j t) ≤
        matrixPayoff A (rowFreq i t) (colFreq j t) + ε) ∧
      ∀ y ∈ lotteries J, matrixPayoff A (rowFreq i t) (colFreq j t) - ε ≤
        matrixPayoff A (rowFreq i t) y := by
  filter_upwards [(robinson_alt h).eventually (gt_mem_nhds hε), eventually_gt_atTop 0]
    with t h1 ht
  obtain ⟨h2, h3⟩ := isEpsSaddle_freq A i j ht
  exact ⟨rowFreq_mem i ht, colFreq_mem j ht, fun x hx => by linarith [h2 x hx],
    fun y hy => by linarith [h3 y hy]⟩

/-- **Alternating play: the empirical payoff converges to the value.** -/
theorem tendsto_payoff_value_alt (h : IsAltFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => matrixPayoff A (rowFreq i t) (colFreq j t)) atTop (𝓝 v) := by
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := hv
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((robinson_alt h).eventually (gt_mem_nhds hε) |>.and (eventually_gt_atTop 0))
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hN t ht
  obtain ⟨h3, h4⟩ := isEpsSaddle_freq A i j h2
  have a1 := hxv _ (colFreq_mem j h2)
  have a2 := hyv _ (rowFreq_mem i h2)
  have b1 := h3 x hx
  have b2 := h4 y hy
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Alternating play: max and min average payoffs converge to the value.** -/
theorem tendsto_max_min_value_alt (h : IsAltFPPath A i j) {v : ℝ} (hv : IsValue A v) :
    Tendsto (fun t => univ.sup' univ_nonempty (rowPay A j t) / t) atTop (𝓝 v) ∧
    Tendsto (fun t => univ.inf' univ_nonempty (colPay A i t) / t) atTop (𝓝 v) := by
  obtain ⟨⟨x, hx, hxv⟩, ⟨y, hy, hyv⟩⟩ := hv
  have hex : ∀ t, exploit A i j t = univ.sup' univ_nonempty (rowPay A j t) / t -
      univ.inf' univ_nonempty (colPay A i t) / t := fun t => by simp only [exploit, sub_div]
  have hlo : ∀ᶠ t in atTop, v ≤ univ.sup' univ_nonempty (rowPay A j t) / t ∧
      univ.inf' univ_nonempty (colPay A i t) / t ≤ v := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact ⟨(hxv _ (colFreq_mem j ht)).trans (payoff_le_max A j ht hx),
      (min_le_payoff A i ht hy).trans (hyv _ (rowFreq_mem i ht))⟩
  have hr := robinson_alt h
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

/-! ### Existence of alternating paths -/

/-- Cumulative payoff vectors along the canonical alternating path. -/
def altState (A : I → J → ℝ) : ℕ → (I → ℝ) × (J → ℝ)
  | 0 => (0, 0)
  | t + 1 =>
    let k := argmaxI (altState A t).1
    let V' := fun l => (altState A t).2 l + A k l
    ((fun k' => (altState A t).1 k' + A k' (argminJ V')), V')

/-- The canonical alternating path. -/
def altRow (A : I → J → ℝ) (t : ℕ) : I := argmaxI (altState A t).1

def altCol (A : I → J → ℝ) (t : ℕ) : J :=
  argminJ fun l => (altState A t).2 l + A (altRow A t) l

omit [DecidableEq I] [DecidableEq J] in
theorem altState_eq (A : I → J → ℝ) (t : ℕ) :
    altState A t = (rowPay A (altCol A) t, colPay A (altRow A) t) := by
  induction t with
  | zero => ext <;> simp [altState, rowPay, colPay]
  | succ t ih =>
    simp only [altState, Prod.mk.injEq]
    constructor <;> funext x <;>
      simp [rowPay, colPay, sum_range_succ, altRow, altCol, ih]

omit [DecidableEq I] [DecidableEq J] in
/-- Non-vacuity: alternating fictitious-play paths exist. -/
theorem isAltFPPath_alt (A : I → J → ℝ) : IsAltFPPath A (altRow A) (altCol A) := by
  intro t
  have e := altState_eq A t
  refine ⟨fun k => ?_, fun l => ?_⟩
  · have := le_argmaxI (altState A t).1 k
    rw [e] at this
    simpa [altRow, e] using this
  · have := argminJ_le (fun l => (altState A t).2 l + A (altRow A t) l) l
    rw [e] at this
    simpa [altCol, e, colPay, sum_range_succ] using this

end Robinson

end Econ
