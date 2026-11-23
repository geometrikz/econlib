/-
# Optimal selling mechanism with finitely many types (Myerson; Riley–Zeckhauser)

MWG §23.F (optimal auction for one buyer), discrete-type form (Myerson 1981; Elkind 2007).
A seller faces one buyer whose type is `θ j` with probability `f j`, `j < n`, with
`θ 0 ≤ θ 1 ≤ ⋯`. A direct mechanism sells with probability `q j` at payment `p j`.
The **virtual weight** of type `j` is

  `w j = f j θ j − (θ (j+1) − θ j) · ∑_{k > j} f k`,

i.e. `f j` times the discrete virtual value `θ j − (θ (j+1) − θ j)(1 − F j)/f j`.

Main results:
* `revenue_eq_virtual_sub`: the exact revenue identity
  `∑ f p = ∑ q w − ∑ f · (U − ∑_{i<k} Δθ_i q_i)`, where `U` is the information rent.
* `revenue_le_virtual` (the discrete Myerson bound): every IC and IR mechanism earns at most
  `∑ q w`.
* `postedPrice_revenue`: a posted price `θ m` attains the bound with equality.
* `postedPrice_isOptimal` (Riley–Zeckhauser): with nondecreasing types, if the virtual
  weights cross zero once, from below, at `m`, then the posted price `θ m` is an optimal
  mechanism among all IC and IR mechanisms with `q ∈ [0, 1]`; randomisation does not help.
* `postedPrice_isOptimal_of_regular` (Myerson): under regularity (nondecreasing virtual
  values, `IsRegularDiscrete`) the single crossing holds, so some posted price is optimal.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Econ

open Finset

variable (n : ℕ) (θ f : ℕ → ℝ)

/-- The probability mass of types strictly above `j`. -/
def upperMass (j : ℕ) : ℝ := ∑ k ∈ Ico (j + 1) n, f k

/-- The **virtual weight** `f j × (virtual value of type j)`. -/
def virtualWeight (j : ℕ) : ℝ := f j * θ j - (θ (j + 1) - θ j) * upperMass n f j

/-- Incentive compatibility of the direct mechanism `(q, p)` on types `0, …, n − 1`. -/
def IsICDiscrete (q p : ℕ → ℝ) : Prop :=
  ∀ j < n, ∀ k < n, θ j * q k - p k ≤ θ j * q j - p j

/-- Individual rationality: every type gets a nonnegative payoff. -/
def IsIRDiscrete (q p : ℕ → ℝ) : Prop := ∀ j < n, 0 ≤ θ j * q j - p j

/-- The rent lower bound `∑_{i<k} (θ (i+1) − θ i) q i` implied by downward IC. -/
def rentFloor (q : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, (θ (i + 1) - θ i) * q i

variable {n θ f}

/-- Exchange of summation: `∑_{k<n} f k ∑_{i<k} g i = ∑_{i<n} g i ∑_{i<k<n} f k`. -/
lemma sum_mul_sum_range_lt (g : ℕ → ℝ) :
    ∑ k ∈ range n, f k * ∑ i ∈ range k, g i = ∑ i ∈ range n, g i * upperMass n f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, upperMass, Ico_self, sum_empty, mul_zero,
      add_zero, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [upperMass, upperMass, sum_Ico_succ_top (Nat.succ_le_of_lt (mem_range.1 hi))]
    ring

/-- **Revenue identity.** Expected revenue equals the expected virtual surplus minus the
expected excess of each type's rent over the floor implied by downward IC. -/
theorem revenue_eq_virtual_sub (q p : ℕ → ℝ) :
    ∑ k ∈ range n, f k * p k = ∑ j ∈ range n, q j * virtualWeight n θ f j -
      ∑ k ∈ range n, f k * ((θ k * q k - p k) - rentFloor θ q k) := by
  have h := sum_mul_sum_range_lt (n := n) (f := f) fun i => (θ (i + 1) - θ i) * q i
  simp only [rentFloor, mul_sub, sum_sub_distrib, h, virtualWeight]
  have e1 : ∑ x ∈ range n, q x * (f x * θ x) = ∑ x ∈ range n, f x * (θ x * q x) :=
    sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x ∈ range n, q x * ((θ (x + 1) - θ x) * upperMass n f x) =
      ∑ i ∈ range n, (θ (i + 1) - θ i) * q i * upperMass n f i :=
    sum_congr rfl fun _ _ => by ring
  linarith

/-- Downward IC and IR of the lowest type give `U k ≥ rentFloor k`. -/
lemma rentFloor_le {q p : ℕ → ℝ} (hIC : IsICDiscrete n θ q p) (hIR : IsIRDiscrete n θ q p) :
    ∀ k < n, rentFloor θ q k ≤ θ k * q k - p k := by
  intro k
  induction k with
  | zero => intro h; simpa [rentFloor] using hIR 0 h
  | succ k ih =>
    intro hk
    have h1 := ih (Nat.lt_of_succ_lt hk)
    have h2 := hIC (k + 1) hk k (Nat.lt_of_succ_lt hk)
    rw [rentFloor, sum_range_succ, ← rentFloor]
    linarith

/-- **Myerson's revenue bound** (discrete types). Every IC and IR mechanism earns at most the
expected virtual surplus `∑ q w`. -/
theorem revenue_le_virtual (hf : ∀ k < n, 0 ≤ f k) {q p : ℕ → ℝ}
    (hIC : IsICDiscrete n θ q p) (hIR : IsIRDiscrete n θ q p) :
    ∑ k ∈ range n, f k * p k ≤ ∑ j ∈ range n, q j * virtualWeight n θ f j := by
  rw [revenue_eq_virtual_sub]
  have : 0 ≤ ∑ k ∈ range n, f k * ((θ k * q k - p k) - rentFloor θ q k) :=
    sum_nonneg fun k hk => mul_nonneg (hf k (mem_range.1 hk))
      (sub_nonneg.2 (rentFloor_le hIC hIR k (mem_range.1 hk)))
  linarith

/-- The posted-price mechanism at price `θ m`: types `j ≥ m` buy for sure and pay `θ m`. -/
def postedQ (m j : ℕ) : ℝ := if m ≤ j then 1 else 0

/-- Payments of the posted-price mechanism. -/
def postedP (θ : ℕ → ℝ) (m j : ℕ) : ℝ := if m ≤ j then θ m else 0

variable (θ) in
/-- The rent of the posted-price mechanism equals the IC floor (no monotonicity needed). -/
lemma postedPrice_rent_eq (m k : ℕ) :
    θ k * postedQ m k - postedP θ m k = rentFloor θ (postedQ m) k := by
  induction k with
  | zero =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [postedQ, postedP, rentFloor]
    · simp [postedQ, postedP, rentFloor, Nat.pos_iff_ne_zero.1 hm]
  | succ k ih =>
    rw [rentFloor, sum_range_succ, ← rentFloor, ← ih]
    simp only [postedQ, postedP]
    by_cases h1 : m ≤ k
    · simp only [h1, Nat.le_succ_of_le h1, ↓reduceIte]; ring
    · by_cases h2 : m ≤ k + 1
      · have : m = k + 1 := le_antisymm h2 (Nat.succ_le_of_lt (not_le.1 h1))
        subst this
        simp
      · simp [h1, h2]

/-- **The posted price attains the Myerson bound** (no rent above the IC floor). -/
theorem postedPrice_revenue (m : ℕ) :
    ∑ k ∈ range n, f k * postedP θ m k =
      ∑ j ∈ range n, postedQ m j * virtualWeight n θ f j := by
  rw [revenue_eq_virtual_sub]
  have : ∑ k ∈ range n, f k * ((θ k * postedQ m k - postedP θ m k) -
      rentFloor θ (postedQ m) k) = 0 :=
    sum_eq_zero fun k _ => by rw [postedPrice_rent_eq, sub_self, mul_zero]
  rw [this, sub_zero]

/-- The posted price is IC and IR when types are nondecreasing. -/
theorem postedPrice_IC_IR (hθ : MonotoneOn θ (Set.Iio n)) (m : ℕ) :
    IsICDiscrete n θ (postedQ m) (postedP θ m) ∧ IsIRDiscrete n θ (postedQ m) (postedP θ m) := by
  constructor
  · intro j hj k hkn
    simp only [postedQ, postedP]
    by_cases hk : m ≤ k <;> by_cases hjm : m ≤ j <;> simp only [hk, hjm, ↓reduceIte]
    · exact le_rfl
    · -- `j < m ≤ k`: buying would give `θ j − θ m ≤ 0`.
      have : θ j ≤ θ m := hθ hj (lt_of_le_of_lt hk hkn) (not_le.1 hjm).le
      linarith
    · -- `k < m ≤ j`: not buying gives `0 ≤ θ j − θ m`.
      have : θ m ≤ θ j := hθ (lt_of_le_of_lt hjm hj) hj hjm
      linarith
    · exact le_rfl
  · intro j hj
    simp only [postedQ, postedP]
    by_cases hjm : m ≤ j
    · simp only [hjm, ↓reduceIte]
      have : θ m ≤ θ j := hθ (lt_of_le_of_lt hjm hj) hj hjm
      linarith
    · simp [hjm]

/-- **Revenue bound by the posted price** (Riley–Zeckhauser 1983; Myerson 1981). If the
virtual weights are `≤ 0` below `m` and `≥ 0` from `m` on (single crossing; regularity implies
it, see `postedPrice_isOptimal_of_regular`), no IC and IR mechanism with sale probabilities in `[0, 1]` earns more than the
posted price `θ m`. (That the posted price is itself feasible needs nondecreasing types: see
`postedPrice_isOptimal`.) -/
theorem postedPrice_optimal (hf : ∀ k < n, 0 ≤ f k) (m : ℕ)
    (hlow : ∀ j < n, j < m → virtualWeight n θ f j ≤ 0)
    (hhigh : ∀ j < n, m ≤ j → 0 ≤ virtualWeight n θ f j)
    {q p : ℕ → ℝ} (hq : ∀ j < n, 0 ≤ q j ∧ q j ≤ 1)
    (hIC : IsICDiscrete n θ q p) (hIR : IsIRDiscrete n θ q p) :
    ∑ k ∈ range n, f k * p k ≤ ∑ k ∈ range n, f k * postedP θ m k := by
  refine (revenue_le_virtual hf hIC hIR).trans ?_
  rw [postedPrice_revenue]
  refine sum_le_sum fun j hj => ?_
  have hjn := mem_range.1 hj
  simp only [postedQ]
  by_cases hjm : m ≤ j
  · simp only [hjm, ↓reduceIte, one_mul]
    exact mul_le_of_le_one_left (hhigh j hjn hjm) (hq j hjn).2
  · simp only [hjm, ↓reduceIte, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hq j hjn).1 (hlow j hjn (not_le.1 hjm))

/-- **The posted price is an optimal mechanism.** With nondecreasing types and virtual weights
crossing zero once at `m`, the posted price `θ m` is itself IC and IR and earns at least as much
as every IC and IR mechanism with sale probabilities in `[0, 1]`. -/
theorem postedPrice_isOptimal (hθ : MonotoneOn θ (Set.Iio n)) (hf : ∀ k < n, 0 ≤ f k) (m : ℕ)
    (hlow : ∀ j < n, j < m → virtualWeight n θ f j ≤ 0)
    (hhigh : ∀ j < n, m ≤ j → 0 ≤ virtualWeight n θ f j) :
    IsICDiscrete n θ (postedQ m) (postedP θ m) ∧ IsIRDiscrete n θ (postedQ m) (postedP θ m) ∧
      ∀ q p : ℕ → ℝ, (∀ j < n, 0 ≤ q j ∧ q j ≤ 1) → IsICDiscrete n θ q p →
        IsIRDiscrete n θ q p →
        ∑ k ∈ range n, f k * p k ≤ ∑ k ∈ range n, f k * postedP θ m k :=
  ⟨(postedPrice_IC_IR hθ m).1, (postedPrice_IC_IR hθ m).2,
    fun _ _ hq hIC hIR => postedPrice_optimal hf m hlow hhigh hq hIC hIR⟩

/-- **Regularity** (Myerson 1981), discrete form: the virtual values `w j / f j` are
nondecreasing in the type. -/
def IsRegularDiscrete (n : ℕ) (θ f : ℕ → ℝ) : Prop :=
  MonotoneOn (fun j => virtualWeight n θ f j / f j) (Set.Iio n)

/-- **Optimal mechanism under regularity** (Myerson 1981; Riley–Zeckhauser 1983). With
nondecreasing types, positive probabilities and regular virtual values, some posted price
`θ m` (`m ≤ n`; `m = n` means not selling) is IC, IR and earns at least as much as every IC
and IR mechanism with sale probabilities in `[0, 1]`. The cutoff `m` is the first type with
nonnegative virtual value. -/
theorem postedPrice_isOptimal_of_regular (hθ : MonotoneOn θ (Set.Iio n))
    (hf : ∀ k < n, 0 < f k) (hreg : IsRegularDiscrete n θ f) :
    ∃ m ≤ n, IsICDiscrete n θ (postedQ m) (postedP θ m) ∧
      IsIRDiscrete n θ (postedQ m) (postedP θ m) ∧
      ∀ q p : ℕ → ℝ, (∀ j < n, 0 ≤ q j ∧ q j ≤ 1) → IsICDiscrete n θ q p →
        IsIRDiscrete n θ q p →
        ∑ k ∈ range n, f k * p k ≤ ∑ k ∈ range n, f k * postedP θ m k := by
  classical
  have hex : ∃ j, n ≤ j ∨ 0 ≤ virtualWeight n θ f j / f j := ⟨n, Or.inl le_rfl⟩
  set m := Nat.find hex
  have hm : n ≤ m ∨ 0 ≤ virtualWeight n θ f m / f m := Nat.find_spec hex
  have hmn : m ≤ n := Nat.find_min' hex (Or.inl le_rfl)
  have hlow : ∀ j < n, j < m → virtualWeight n θ f j ≤ 0 := by
    intro j hj hjm
    have h := Nat.find_min hex hjm
    push Not at h
    have := (div_neg_iff.1 h.2)
    rcases this with h' | h'
    · exact absurd h'.2 (not_lt.2 (hf j hj).le)
    · exact h'.1.le
  have hhigh : ∀ j < n, m ≤ j → 0 ≤ virtualWeight n θ f j := by
    intro j hj hmj
    have hm' : 0 ≤ virtualWeight n θ f m / f m := hm.resolve_left (by omega)
    have := hreg (show m ∈ Set.Iio n from lt_of_le_of_lt hmj hj) hj hmj
    have h2 : 0 ≤ virtualWeight n θ f j / f j := hm'.trans this
    exact (div_nonneg_iff.1 h2).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 (hf j hj))
  exact ⟨m, hmn, postedPrice_isOptimal hθ (fun k hk => (hf k hk).le) m hlow hhigh⟩

/-- **Witness.** Three equally likely values `1, 2, 3`: the virtual weights are
`−1/3, 1/3, 1`, crossing zero at `m = 1`, so the posted price `2` is optimal. -/
example : virtualWeight 3 (fun j => (j : ℝ) + 1) (fun _ => 1 / 3) 0 = -1 / 3 ∧
    virtualWeight 3 (fun j => (j : ℝ) + 1) (fun _ => 1 / 3) 1 = 1 / 3 ∧
    virtualWeight 3 (fun j => (j : ℝ) + 1) (fun _ => 1 / 3) 2 = 1 := by
  simp only [virtualWeight, upperMass]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> norm_num

/-- The same three-type distribution is regular: the virtual values are `−1, 1, 3`. -/
example : IsRegularDiscrete 3 (fun j => (j : ℝ) + 1) (fun _ => 1 / 3) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  simp only [virtualWeight, upperMass]
  interval_cases a <;> interval_cases b <;> simp at hab ⊢ <;> norm_num [Finset.sum_Ico_eq_sum_range]

end Econ
