/-
# The housing market: top trading cycles and the core (Shapley–Scarf 1974; Roth–Postlewaite 1977)

Shapley and Scarf (1974); Roth and Postlewaite (1977); Roth (1982), *Economics Letters* 9,
127–132; Roth and Sotomayor, *Two-Sided Matching*. Each agent `i : N` owns one house (house `i`) and has strict
preferences over all houses, given by a utility `u i : N → ℝ`. Strictness (`u i` injective) is a hypothesis of
the core, uniqueness, strategy-proofness and efficiency theorems; existence of a TTC allocation does not need it. An allocation
is a permutation `σ`: agent `i` receives house `σ i`.

**Top trading cycles (TTC)**: every remaining agent points to the owner of her favourite
remaining house; there is at least one cycle; agents on cycles trade along them and leave;
repeat. We describe a TTC outcome by its stages: `IsTTC u σ` says there is a stage
`r : N → ℕ` such that every agent trades within her own stage (`r (σ i) = r i`) and receives her
favourite among the houses still present at her stage (owners of stage `≥ r i`).

* `ttc_exists`: a TTC allocation exists (the cycle-removal algorithm, by induction on the set
  of remaining agents).
* `ttc_in_strictCore`: a TTC allocation is in the **strict core**: no coalition can
  reallocate its own houses so that every member is weakly better off and one is strictly
  better off (Roth–Postlewaite 1977).
* `strictCore_eq_ttc`: every allocation in the strict core equals the TTC allocation; so the
  strict core is a single allocation and the TTC allocation is unique (Roth–Postlewaite 1977).
* `strictCore_nonempty`: with strict preferences the strict core is exactly one allocation
  (Roth–Postlewaite 1977; Shapley–Scarf 1974 proved the weak core is nonempty, also with
  indifferences, which is not formalized here).

* `strictCore_agree_below`: agents who trade before stage `K` keep their TTC houses in the
  strict core of any profile `u'` that equals `u` on every agent of stage `< K`.
* `ttc_strategyproof`: TTC is strategy-proof (Roth 1982).
* `ttc_pareto`: TTC is Pareto efficient (a consequence of the core result, Shapley–Scarf 1974;
  Roth–Postlewaite 1977).
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Econ

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `σ` is a **top trading cycles** allocation for utilities `u`: there is a stage function
`r` such that trades stay within a stage and each agent gets her favourite house among the
owners of the same or a later stage. -/
def IsTTC (u : N → N → ℝ) (σ : Equiv.Perm N) : Prop :=
  ∃ r : N → ℕ, (∀ i, r (σ i) = r i) ∧ ∀ i j, r i ≤ r j → u i j ≤ u i (σ i)

/-- The coalition `S` **weakly blocks** the allocation `σ` by the reallocation `τ` of its own
houses: every member is weakly better off and some member strictly better off. -/
def WeaklyBlocks (u : N → N → ℝ) (σ : Equiv.Perm N) (S : Finset N) (τ : Equiv.Perm N) :
    Prop :=
  (∀ i ∈ S, τ i ∈ S) ∧ (∀ i ∈ S, u i (σ i) ≤ u i (τ i)) ∧ ∃ i ∈ S, u i (σ i) < u i (τ i)

/-- The **strict core**: allocations that no coalition weakly blocks. -/
def InStrictCore (u : N → N → ℝ) (σ : Equiv.Perm N) : Prop :=
  ∀ S τ, ¬ WeaklyBlocks u σ S τ

omit [Fintype N] in
/-- If `τ` maps the finite set `S` into itself, it maps it onto itself. -/
lemma perm_image_eq_of_mapsTo {τ : Equiv.Perm N} {L : Finset N} (h : ∀ i ∈ L, τ i ∈ L) :
    L.image τ = L :=
  eq_of_subset_of_card_le (fun _ hx => by
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx; exact h y hy)
    (card_image_of_injective _ τ.injective).ge

omit [Fintype N] in
/-- **TTC allocations are in the strict core** (Roth–Postlewaite 1977). -/
theorem ttc_in_strictCore {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ : Equiv.Perm N} (hσ : IsTTC u σ) : InStrictCore u σ := by
  obtain ⟨r, hr, htop⟩ := hσ
  rintro S τ ⟨hS, hweak, i₀, hi₀, hstrict⟩
  -- every member of `S` gets the same house under `τ` as under `σ`, stage by stage
  have key : ∀ k, ∀ i ∈ S, r i = k → τ i = σ i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hi hik
      set L := S.filter fun s => r s < k
      have hτσ : ∀ l ∈ L, τ l = σ l := fun l hl =>
        ih (r l) (mem_filter.1 hl).2 l (mem_filter.1 hl).1 rfl
      have hL : ∀ l ∈ L, τ l ∈ L := fun l hl => by
        refine mem_filter.2 ⟨hS l (mem_filter.1 hl).1, ?_⟩
        rw [hτσ l hl, hr]; exact (mem_filter.1 hl).2
      have hge : k ≤ r (τ i) := by
        by_contra hlt
        push Not at hlt
        have hmem : τ i ∈ L := mem_filter.2 ⟨hS i hi, hlt⟩
        rw [← perm_image_eq_of_mapsTo hL] at hmem
        obtain ⟨l, hl, hli⟩ := mem_image.1 hmem
        have := τ.injective hli
        subst this
        exact absurd (mem_filter.1 hl).2 (by omega)
      exact hu i (le_antisymm (htop i _ (hik ▸ hge)) (hweak i hi))
  exact absurd (key _ i₀ hi₀ rfl ▸ hstrict) (lt_irrefl _)

/-- **The strict core is the TTC allocation** (Roth–Postlewaite 1977): any allocation in the
strict core coincides with any TTC allocation. -/
theorem strictCore_eq_ttc {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ π : Equiv.Perm N} (hσ : IsTTC u σ) (hπ : InStrictCore u π) : π = σ := by
  obtain ⟨r, hr, htop⟩ := hσ
  have key : ∀ k, ∀ i, r i = k → π i = σ i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik
      -- stage `≥ k` houses: π cannot give `i` a house of an earlier stage
      have hge : ∀ j, r j = k → k ≤ r (π j) := by
        intro j hj
        by_contra hlt
        push Not at hlt
        obtain ⟨m, hm⟩ : ∃ m, σ m = π j := ⟨σ.symm (π j), by simp⟩
        have hrm : r m = r (π j) := by rw [← hr m, hm]
        have hπm : π m = σ m := ih (r m) (by omega) m rfl
        have hmj : m = j := π.injective (hπm.trans hm)
        subst hmj
        omega
      -- the coalition of stages `≤ k` would block `π` by `σ` otherwise
      have hweak : ∀ j, r j ≤ k → u j (π j) ≤ u j (σ j) := by
        intro j hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · rw [ih (r j) hlt j rfl]
        · exact htop j _ (heq ▸ hge j heq)
      by_contra hne
      have hlt : u i (π i) < u i (σ i) :=
        lt_of_le_of_ne (hweak i hik.le) fun h => hne (hu i h)
      apply hπ (univ.filter fun j => r j ≤ k) σ
      refine ⟨fun j hj => mem_filter.2 ⟨mem_univ _, ?_⟩, fun j hj => hweak j (mem_filter.1 hj).2,
        i, mem_filter.2 ⟨mem_univ _, hik.le⟩, hlt⟩
      rw [hr]; exact (mem_filter.1 hj).2
  exact Equiv.ext fun i => key _ i rfl

/-- Two TTC allocations coincide. -/
theorem ttc_unique {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ σ' : Equiv.Perm N} (hσ : IsTTC u σ) (hσ' : IsTTC u σ') : σ' = σ :=
  strictCore_eq_ttc hu hσ (ttc_in_strictCore hu hσ')

/-- **Agreement below a stage.** Let `σ` be a TTC allocation for `u` with stage function `r`,
and `π` a strict-core allocation for other utilities `u'` that agree with `u` for every agent
of stage below `K`. Then `π` and `σ` agree on every agent of stage below `K`: the early cycles
of TTC do not depend on the preferences of agents who trade later. -/
theorem strictCore_agree_below {u u' : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {σ π : Equiv.Perm N} {r : N → ℕ} (hr : ∀ i, r (σ i) = r i)
    (htop : ∀ i j, r i ≤ r j → u i j ≤ u i (σ i)) (hπ : InStrictCore u' π) {K : ℕ}
    (hagree : ∀ j, r j < K → u' j = u j) : ∀ j, r j < K → π j = σ j := by
  have key : ∀ k, k < K → ∀ i, r i = k → π i = σ i := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkK i hik
      have hge : ∀ j, r j = k → k ≤ r (π j) := by
        intro j hj
        by_contra hlt
        push Not at hlt
        obtain ⟨m, hm⟩ : ∃ m, σ m = π j := ⟨σ.symm (π j), by simp⟩
        have hrm : r m = r (π j) := by rw [← hr m, hm]
        have hπm : π m = σ m := ih (r m) (by omega) (by omega) m rfl
        have hmj : m = j := π.injective (hπm.trans hm)
        subst hmj
        omega
      have hweak : ∀ j, r j ≤ k → u' j (π j) ≤ u' j (σ j) := by
        intro j hj
        rw [hagree j (by omega)]
        rcases lt_or_eq_of_le hj with hlt | heq
        · rw [ih (r j) hlt (by omega) j rfl]
        · exact htop j _ (heq ▸ hge j heq)
      by_contra hne
      have hlt : u' i (π i) < u' i (σ i) := by
        refine lt_of_le_of_ne (hweak i hik.le) fun h => hne (hu i ?_)
        rwa [hagree i (by omega)] at h
      apply hπ (univ.filter fun j => r j ≤ k) σ
      refine ⟨fun j hj => mem_filter.2 ⟨mem_univ _, ?_⟩, fun j hj => hweak j (mem_filter.1 hj).2,
        i, mem_filter.2 ⟨mem_univ _, hik.le⟩, hlt⟩
      rw [hr]; exact (mem_filter.1 hj).2
  exact fun j hj => key _ hj j rfl

/-- **TTC is strategy-proof** (Roth 1982). If agent `i` reports `u' i` instead of her true
utility `u i` (everyone else reporting truthfully), the TTC allocation `σ'` for the reports
gives her a house she does not strictly prefer to her truthful TTC house. Both profiles
are strict (the misreport `u' i` is any strict ranking). -/
theorem ttc_strategyproof {u u' : N → N → ℝ} (hu : ∀ i, Function.Injective (u i))
    {i : N} (hu' : Function.Injective (u' i)) (hother : ∀ j, j ≠ i → u' j = u j)
    {σ σ' : Equiv.Perm N} (hσ : IsTTC u σ) (hσ' : IsTTC u' σ') : u i (σ' i) ≤ u i (σ i) := by
  obtain ⟨r, hr, htop⟩ := hσ
  have hu'all : ∀ j, Function.Injective (u' j) := fun j => by
    by_cases hj : j = i
    · subst hj; exact hu'
    · rw [hother j hj]; exact hu j
  have hcore := ttc_in_strictCore hu'all hσ'
  have hagr := strictCore_agree_below hu hr htop hcore (K := r i)
    (fun j hj => hother j fun h => by subst h; omega)
  -- `i`'s house under `σ'` is not one of the houses traded before her stage
  apply htop i
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ : ∃ m, σ m = σ' i := ⟨σ.symm (σ' i), by simp⟩
  have hrm : r m = r (σ' i) := by rw [← hr m, hm]
  have hmi : m = i := σ'.injective ((hagr m (by omega)).trans hm)
  subst hmi
  omega

/-- **TTC is Pareto efficient** (from the core property, Shapley–Scarf 1974;
Roth–Postlewaite 1977): no allocation makes every agent weakly and some agent
strictly better off. -/
theorem ttc_pareto {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i)) {σ : Equiv.Perm N}
    (hσ : IsTTC u σ) (π : Equiv.Perm N) :
    ¬ ((∀ j, u j (σ j) ≤ u j (π j)) ∧ ∃ j, u j (σ j) < u j (π j)) := by
  rintro ⟨hweak, j, hj⟩
  exact ttc_in_strictCore hu hσ univ π
    ⟨fun _ _ => mem_univ _, fun k _ => hweak k, j, mem_univ _, hj⟩

/-- Every map of a finite type into itself has a cycle inside any nonempty invariant set:
a nonempty `C ⊆ R` on which `f` is a bijection. -/
lemma exists_cycle (f : N → N) {R : Finset N} (hR : R.Nonempty) (hf : ∀ i ∈ R, f i ∈ R) :
    ∃ C : Finset N, C.Nonempty ∧ C ⊆ R ∧ (∀ x ∈ C, f x ∈ C) ∧ Set.InjOn f C := by
  obtain ⟨i₀, hi₀⟩ := hR
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => f^[n] i₀
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
  set p := f^[a] i₀
  set d := b - a
  have hd : 0 < d := by omega
  have hper : f^[d] p = p := by
    show f^[b - a] (f^[a] i₀) = f^[a] i₀
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, ← he]
  have hiterR : ∀ n, ∀ x ∈ R, f^[n] x ∈ R := by
    intro n; induction n with
    | zero => exact fun x hx => hx
    | succ n ih => intro x hx; rw [Function.iterate_succ_apply']; exact hf _ (ih x hx)
  refine ⟨(range d).image fun k => f^[k] p, ⟨p, mem_image.2 ⟨0, mem_range.2 hd, rfl⟩⟩,
    fun x hx => ?_, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · obtain ⟨k, _, rfl⟩ := mem_image.1 hx; exact hiterR k p (hiterR a i₀ hi₀)
  · obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    rw [mem_range] at hk
    rw [← Function.iterate_succ_apply' f k p]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with h | h
    · exact mem_image.2 ⟨k + 1, mem_range.2 h, rfl⟩
    · rw [h, hper]; exact mem_image.2 ⟨0, mem_range.2 hd, rfl⟩
  · -- `f^[d - 1]` inverts `f` on the cycle
    have back : ∀ z ∈ ((range d).image fun k => f^[k] p : Finset N), f^[d - 1] (f z) = z := by
      intro z hz
      obtain ⟨k, _, rfl⟩ := mem_image.1 hz
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hd,
        ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hper]
    rw [← back x hx, ← back y hy, hxy]

/-- The stage-by-stage TTC algorithm on a set `R` of remaining agents: there are a stage
function and an assignment, injective on `R`, under which every agent in `R` trades inside `R`
within her stage and gets her favourite house in `R` among stages at least hers. -/
lemma ttc_exists_on {u : N → N → ℝ} (R : Finset N) :
    ∃ σ : N → N, ∃ r : N → ℕ, (∀ i ∈ R, σ i ∈ R ∧ r (σ i) = r i ∧
      ∀ j ∈ R, r i ≤ r j → u i j ≤ u i (σ i)) ∧ Set.InjOn σ R := by
  induction R using Finset.strongInduction with
  | H R ih =>
    rcases R.eq_empty_or_nonempty with rfl | hR
    · exact ⟨id, fun _ => 0, fun i hi => absurd hi (notMem_empty i), fun _ hx => absurd hx (notMem_empty _)⟩
    -- each agent's favourite house in `R`
    have htop : ∀ i, ∃ j ∈ R, ∀ k ∈ R, u i k ≤ u i j := fun i => exists_max_image R (u i) hR
    choose top htopR htopmax using htop
    obtain ⟨C, hCne, hCR, hCmaps, hCinj⟩ := exists_cycle top hR fun i _ => htopR i
    obtain ⟨σ', r', h', hinj'⟩ := ih (R \ C) (sdiff_ssubset hCR hCne)
    classical
    refine ⟨fun i => if i ∈ C then top i else σ' i, fun i => if i ∈ C then 0 else r' i + 1,
      fun i hi => ?_, fun x hx y hy hxy => ?_⟩
    · by_cases hiC : i ∈ C
      · simp only [hiC, ↓reduceIte, hCmaps i hiC]
        exact ⟨htopR i, trivial, fun j hj _ => htopmax i j hj⟩
      · have hiR' : i ∈ R \ C := mem_sdiff.2 ⟨hi, hiC⟩
        obtain ⟨hm, hrr, hmax⟩ := h' i hiR'
        have hσC : σ' i ∉ C := (mem_sdiff.1 hm).2
        simp only [hiC, hσC, ↓reduceIte, hrr]
        refine ⟨(mem_sdiff.1 hm).1, trivial, fun j hj hle => ?_⟩
        by_cases hjC : j ∈ C
        · simp only [hjC, ↓reduceIte] at hle; omega
        · simp only [hjC, ↓reduceIte] at hle
          exact hmax j (mem_sdiff.2 ⟨hj, hjC⟩) (by omega)
    · simp only [Finset.mem_coe] at hx hy
      by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C <;> simp only [hxC, hyC, ↓reduceIte] at hxy
      · exact hCinj hxC hyC hxy
      · exact absurd (show σ' y ∈ C by rw [← hxy]; exact hCmaps x hxC)
          (mem_sdiff.1 (h' y (mem_sdiff.2 ⟨hy, hyC⟩)).1).2
      · exact absurd (show σ' x ∈ C by rw [hxy]; exact hCmaps y hyC)
          (mem_sdiff.1 (h' x (mem_sdiff.2 ⟨hx, hxC⟩)).1).2
      · exact hinj' (mem_sdiff.2 ⟨hx, hxC⟩) (mem_sdiff.2 ⟨hy, hyC⟩) hxy

/-- **Existence of the TTC allocation.** -/
theorem ttc_exists (u : N → N → ℝ) : ∃ σ : Equiv.Perm N, IsTTC u σ := by
  obtain ⟨σ, r, h, hinj⟩ := ttc_exists_on (u := u) (univ : Finset N)
  have hi : Function.Injective σ := fun x y hxy => hinj (by simp) (by simp) hxy
  refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hi), r, fun i => (h i (mem_univ _)).2.1,
    fun i j hij => (h i (mem_univ _)).2.2 j (mem_univ _) hij⟩

/-- **Roth–Postlewaite (1977)**: with strict preferences the strict core is nonempty and consists
of exactly one allocation, the TTC allocation (this implies the Shapley–Scarf (1974) theorem
that the core is nonempty, in the strict-preference case). -/
theorem strictCore_nonempty {u : N → N → ℝ} (hu : ∀ i, Function.Injective (u i)) :
    ∃ σ : Equiv.Perm N, InStrictCore u σ ∧ ∀ π, InStrictCore u π → π = σ := by
  obtain ⟨σ, hσ⟩ := ttc_exists u
  exact ⟨σ, ttc_in_strictCore hu hσ, fun π hπ => strictCore_eq_ttc hu hσ hπ⟩

/-- Witness: two agents who each prefer the other's house. Swapping is the TTC allocation (one
stage), hence the unique strict-core allocation; staying put is weakly blocked by the pair. -/
example : IsTTC (N := Fin 2) (fun i j => if i = j then 0 else 1) (Equiv.swap 0 1) ∧
    ∀ π, InStrictCore (N := Fin 2) (fun i j => if i = j then 0 else 1) π → π = Equiv.swap 0 1 := by
  have hu : ∀ i : Fin 2, Function.Injective fun j : Fin 2 => if i = j then (0 : ℝ) else 1 := by
    intro i a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all
  have httc : IsTTC (N := Fin 2) (fun i j => if i = j then 0 else 1) (Equiv.swap 0 1) :=
    ⟨fun _ => 0, fun _ => rfl, fun i j _ => by fin_cases i <;> fin_cases j <;> simp⟩
  exact ⟨httc, fun π hπ => strictCore_eq_ttc hu httc hπ⟩

/-- Witness (continued): staying put is weakly blocked by the pair. -/
example : ¬ InStrictCore (N := Fin 2) (fun i j => if i = j then 0 else 1) (Equiv.refl _) := by
  intro h
  refine h univ (Equiv.swap 0 1) ⟨fun _ _ => mem_univ _, fun i _ => ?_, 0, mem_univ _, ?_⟩
  · fin_cases i <;> simp
  · simp

/-- Witness with two stages: agent `0` likes her own house best and leaves at stage `0`;
agents `1` and `2` both like house `0` best but it is gone, so at stage `1` they swap. The
swap of `1` and `2` is the TTC allocation and the unique strict-core allocation. -/
example : IsTTC (N := Fin 3) ![![2, 0, 1], ![2, 0, 1], ![2, 1, 0]] (Equiv.swap 1 2) ∧
    ∀ π, InStrictCore (N := Fin 3) ![![2, 0, 1], ![2, 0, 1], ![2, 1, 0]] π → π = Equiv.swap 1 2 := by
  have hu : ∀ i : Fin 3, Function.Injective ((![![2, 0, 1], ![2, 0, 1], ![2, 1, 0]] : Fin 3 → Fin 3 → ℝ) i) := by
    intro i a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;> first | rfl | norm_num at h
  have httc : IsTTC (N := Fin 3) ![![2, 0, 1], ![2, 0, 1], ![2, 1, 0]] (Equiv.swap 1 2) := by
    refine ⟨![0, 1, 1], fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> decide
    · fin_cases i <;> fin_cases j <;> simp_all [Equiv.swap_apply_of_ne_of_ne]
  exact ⟨httc, fun π hπ => strictCore_eq_ttc hu httc hπ⟩

end Econ
