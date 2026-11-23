/-
# The Goodman-Bacon decomposition of two-way fixed effects

Goodman-Bacon (2021), "Difference-in-differences with variation in treatment
timing", *Journal of Econometrics* 225, Theorem 1 and eq. (10).

**The economics.** In a balanced group × period panel, the TWFE coefficient on a
treatment `D` is a weighted average of the TWFE coefficients obtained from every
*pair* of groups, with nonnegative weights proportional to the variance of the
pair's (time-demeaned) treatment difference (`goodman_bacon`). For staggered
adoption each pair's treatment difference is an indicator of a set of periods
(the periods when exactly one of the two groups is treated), and then the pair
coefficient is a simple 2×2 difference in differences: the average outcome gap
in those periods minus the average gap in the others (`pairCoef_indicator`).
For an early-vs-late pair this compares the window where only the early group
is treated with both the pre-period (late group as control) and the post-period
(early group as control); the latter comparison is the "forbidden" one that
can make TWFE misleading with dynamic effects.

**Encoding.** Group-level cells with equal weights, as in `Causal.TWFE` (where
the TWFE regression `IsTWFE` and the double-demeaned treatment `eps` live). The
pair coefficient `pairCoef D Y g h` is defined by its closed form and shown to be
the TWFE coefficient of the two-group panel (`pairCoef_eq_twfe`).

**Documented deviation.** Goodman-Bacon weights pairs by group sizes `n_k n_l`
as well as the variance of treatment; with equal cell weights those factors are
equal across pairs and drop out.
-/
module

public import EconLean.Econometrics.Causal.TWFE

@[expose] public section

namespace Econ.Causal.TWFE

open Finset

variable {G T : Type*} [Fintype G] [Fintype T]

/-- Time-demeaned within group: `ẋ_{g,t} = x_{g,t} − x̄_{g,·}`. -/
noncomputable def dm (x : G → T → ℝ) (g : G) (t : T) : ℝ := x g t - rowMean x g

/-- Pair numerator `Σ_t (Ḋ_g − Ḋ_h)(Ẏ_g − Ẏ_h)`. -/
noncomputable def pairNum (D Y : G → T → ℝ) (g h : G) : ℝ :=
  ∑ t, (dm D g t - dm D h t) * (dm Y g t - dm Y h t)

/-- Pair treatment variation `Σ_t (Ḋ_g − Ḋ_h)²`. -/
noncomputable def pairVar (D : G → T → ℝ) (g h : G) : ℝ :=
  ∑ t, (dm D g t - dm D h t) ^ 2

/-- The two-group TWFE coefficient (closed form). -/
noncomputable def pairCoef (D Y : G → T → ℝ) (g h : G) : ℝ :=
  pairNum D Y g h / pairVar D g h

/-- Bacon weight of the ordered pair `(g, h)`. -/
noncomputable def baconWeight (D : G → T → ℝ) (g h : G) : ℝ :=
  pairVar D g h / ∑ g', ∑ h', pairVar D g' h'

/-- **The TWFE coefficient in closed form** (Frisch–Waugh–Lovell):
`b = Σ ε Y / Σ ε D` for any least-squares fit. -/
theorem isTWFE_coef [DecidableEq G] [DecidableEq T] [Nonempty G] [Nonempty T]
    {Y D : G → T → ℝ} {a : G → ℝ} {l : T → ℝ} {b : ℝ} (hmin : IsTWFE Y D a l b)
    (hden : ∑ g, ∑ t, eps D g t * D g t ≠ 0) :
    b = (∑ g, ∑ t, eps D g t * Y g t) / ∑ g, ∑ t, eps D g t * D g t := by
  have hne := (isTWFE_iff_normalEq Y D a l b).mp hmin
  have h_er : ∑ g, ∑ t, eps D g t * resid Y D a l b g t = 0 := by
    have := sum_resid_mul_eq_zero hne (fun g => -rowMean D g)
      (fun t => grandMean D - colMean D t) 1
    rw [← this]
    exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by simp only [eps]; ring
  have hsplit : ∑ g, ∑ t, eps D g t * Y g t
      = ∑ g, ∑ t, eps D g t * (a g + l t) + b * ∑ g, ∑ t, eps D g t * D g t
        + ∑ g, ∑ t, eps D g t * resid Y D a l b g t := by
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun g _ => sum_congr rfl fun t _ => by simp only [resid]; ring
  rw [hsplit, sum_eps_mul_additive, h_er, eq_div_iff hden]
  ring

/-- `ε_{g,t} = Ḋ_{g,t} − (1/|G|) Σ_h Ḋ_{h,t}`. -/
lemma eps_eq_dm (D : G → T → ℝ) (g : G) (t : T) :
    eps D g t = dm D g t - (∑ h, dm D h t) / Fintype.card G := by
  have hg : grandMean D = (∑ h, rowMean D h) / Fintype.card G := by
    simp only [grandMean, rowMean, ← sum_div, div_div, mul_comm (Fintype.card T : ℝ)]
  simp only [eps, dm, colMean, sum_sub_distrib, sub_div, hg]
  ring

omit [Fintype T] in
/-- Covariance as a sum over pairs: `Σ_g (a_g − ā) b_g = Σ_{g,h} (a_g − a_h)(b_g − b_h) / (2|G|)`. -/
lemma sum_centered_mul_eq_pairs [Nonempty G] (a b : G → ℝ) :
    ∑ g, (a g - (∑ h, a h) / Fintype.card G) * b g
      = (∑ g, ∑ h, (a g - a h) * (b g - b h)) / (2 * Fintype.card G) := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hR : ∑ g, ∑ h, (a g - a h) * (b g - b h)
      = 2 * Fintype.card G * ∑ g, a g * b g - 2 * (∑ g, a g) * ∑ g, b g := by
    simp only [sub_mul, mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul, sum_const, card_univ,
      nsmul_eq_mul]
    rw [show ∑ x, a x * ((Fintype.card G : ℝ) * b x) = (Fintype.card G : ℝ) * ∑ x, a x * b x
      by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring]
    ring
  rw [hR, eq_div_iff (by positivity)]
  simp only [sub_mul, sum_sub_distrib]
  rw [← mul_sum]
  field_simp

omit [Fintype G] in
lemma pairNum_self (D : G → T → ℝ) (g h : G) : pairNum D D g h = pairVar D g h := by
  simp only [pairNum, pairVar, sq]

omit [Fintype G] in
lemma pairVar_nonneg (D : G → T → ℝ) (g h : G) : 0 ≤ pairVar D g h :=
  sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype G] in
/-- A pair with no treatment variation contributes nothing. -/
lemma pairNum_eq_zero_of_pairVar (D Y : G → T → ℝ) {g h : G} (hv : pairVar D g h = 0) :
    pairNum D Y g h = 0 := by
  have hz : ∀ t, dm D g t - dm D h t = 0 := fun t => by
    have := (sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (dm D g t - dm D h t)).mp hv t
      (mem_univ t)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  simp [pairNum, hz]

/-- Bacon weights are nonnegative and sum to one. -/
theorem baconWeight_nonneg (D : G → T → ℝ) (g h : G) : 0 ≤ baconWeight D g h :=
  div_nonneg (pairVar_nonneg D g h) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    pairVar_nonneg D _ _)

theorem sum_baconWeight (D : G → T → ℝ) (hv : ∑ g, ∑ h, pairVar D g h ≠ 0) :
    ∑ g, ∑ h, baconWeight D g h = 1 := by
  simp only [baconWeight, ← sum_div]
  exact div_self hv

variable [Nonempty G] [Nonempty T]

/-- `Σ ε Y = Σ_{g,h} pairNum(g, h) / (2|G|)`. -/
theorem sum_eps_mul_eq_pairs (D Y : G → T → ℝ) :
    ∑ g, ∑ t, eps D g t * Y g t = (∑ g, ∑ h, pairNum D Y g h) / (2 * Fintype.card G) := by
  have h1 : ∑ g, ∑ t, eps D g t * Y g t = ∑ g, ∑ t, eps D g t * dm Y g t := by
    have : ∀ g, ∑ t, eps D g t * rowMean Y g = 0 := fun g => by
      rw [← sum_mul, sum_eps_row, zero_mul]
    simp only [dm, mul_sub, sum_sub_distrib, this, sub_zero]
  rw [h1, sum_comm]
  simp only [eps_eq_dm, sum_centered_mul_eq_pairs, ← sum_div, pairNum]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl fun g _ => sum_comm

/-- **Goodman-Bacon decomposition** (Goodman-Bacon 2021, Thm 1; equal cell
weights). Any TWFE coefficient is the Bacon-weighted average of the two-group
TWFE coefficients over all (ordered) pairs of groups. -/
theorem goodman_bacon [DecidableEq G] [DecidableEq T] {Y D : G → T → ℝ} {a : G → ℝ}
    {l : T → ℝ} {b : ℝ} (hmin : IsTWFE Y D a l b) (hden : ∑ g, ∑ t, eps D g t * D g t ≠ 0) :
    b = ∑ g, ∑ h, baconWeight D g h * pairCoef D Y g h := by
  have hN : (2 * Fintype.card G : ℝ) ≠ 0 := by
    have : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    positivity
  have hdenD := sum_eps_mul_eq_pairs D D
  simp only [pairNum_self] at hdenD
  have hV : ∑ g, ∑ h, pairVar D g h ≠ 0 := by
    intro h0; rw [hdenD, h0, zero_div] at hden; exact hden rfl
  rw [isTWFE_coef hmin hden, sum_eps_mul_eq_pairs, hdenD, div_div_div_cancel_right₀ hN]
  have hterm : ∀ g h, baconWeight D g h * pairCoef D Y g h
      = pairNum D Y g h / ∑ g', ∑ h', pairVar D g' h' := by
    intro g h
    by_cases hv : pairVar D g h = 0
    · simp [baconWeight, pairCoef, hv, pairNum_eq_zero_of_pairVar D Y hv]
    · simp only [baconWeight, pairCoef]
      field_simp
  simp only [hterm, ← sum_div]

omit [Fintype G] [Nonempty G] in
/-- **The pair coefficient is the two-group TWFE coefficient**: running the TWFE
regression on the panel made of groups `g` and `h` alone gives `pairCoef D Y g h`. -/
theorem pairCoef_eq_twfe [DecidableEq T] (D Y : G → T → ℝ) (g h : G) {a : Fin 2 → ℝ}
    {l : T → ℝ} {b : ℝ} (hmin : IsTWFE (![Y g, Y h]) (![D g, D h]) a l b)
    (hv : pairVar D g h ≠ 0) : b = pairCoef D Y g h := by
  have hsym : ∀ (x : G → T → ℝ), pairNum D x h g = pairNum D x g h := fun x => by
    simp only [pairNum]; exact sum_congr rfl fun t _ => by ring
  have hpair : ∀ (x : G → T → ℝ), ∑ i, ∑ j, pairNum (![D g, D h]) (![x g, x h]) i j
      = 2 * pairNum D x g h := by
    intro x
    simp only [Fin.sum_univ_two]
    have e : ∀ i j : Fin 2, pairNum (![D g, D h]) (![x g, x h]) i j
        = pairNum D x (![g, h] i) (![g, h] j) := by
      intro i j; fin_cases i <;> fin_cases j <;> rfl
    simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hsym]
    simp only [pairNum, sub_self, zero_mul, sum_const_zero]
    ring
  have hden : ∑ i, ∑ t, eps (![D g, D h]) i t * (![D g, D h]) i t ≠ 0 := by
    rw [sum_eps_mul_eq_pairs, hpair D, pairNum_self]
    simpa using hv
  rw [isTWFE_coef hmin hden, sum_eps_mul_eq_pairs, sum_eps_mul_eq_pairs, hpair Y, hpair D,
    pairNum_self, pairCoef]
  simp only [Fintype.card_fin]
  field_simp

omit [Fintype G] [Nonempty G] [Nonempty T] in
/-- **Each pair coefficient is a 2×2 DiD** (Goodman-Bacon eq. (10)). If the
treatment difference between `g` and `h` is the indicator of a set `P` of periods
(true for any two groups under staggered adoption: `P` is the set of periods when
exactly one of them is treated, signed), then the pair coefficient is the average
outcome gap `Y_g − Y_h` over `P` minus its average over the other periods. -/
theorem pairCoef_indicator [DecidableEq T] (D Y : G → T → ℝ) (g h : G) (P : Finset T)
    (hP : 0 < P.card) (hPc : 0 < Pᶜ.card)
    (hD : ∀ t, D g t - D h t = if t ∈ P then 1 else 0) :
    pairCoef D Y g h = (∑ t ∈ P, (Y g t - Y h t)) / P.card
      - (∑ t ∈ Pᶜ, (Y g t - Y h t)) / Pᶜ.card := by
  set z : T → ℝ := fun t => Y g t - Y h t
  set p : ℝ := (P.card : ℝ)
  set q : ℝ := (Pᶜ.card : ℝ)
  have hm : (Fintype.card T : ℝ) = p + q := by
    simp only [p, q]; rw [← Nat.cast_add, Finset.card_add_card_compl]
  have hp : 0 < p := by simp only [p]; exact_mod_cast hP
  have hq : 0 < q := by simp only [q]; exact_mod_cast hPc
  have hsplit : ∀ f : T → ℝ, ∑ t, f t = ∑ t ∈ P, f t + ∑ t ∈ Pᶜ, f t := fun f =>
    (Finset.sum_add_sum_compl P f).symm
  have hdD : ∀ t, dm D g t - dm D h t = (if t ∈ P then 1 else 0) - p / (p + q) := by
    intro t
    have : rowMean D g - rowMean D h = p / (p + q) := by
      simp only [rowMean, ← sub_div, ← sum_sub_distrib, hD, hm]
      rw [Finset.sum_ite_mem, Finset.univ_inter, sum_const, nsmul_eq_mul, mul_one]
    simp only [dm]; rw [← hD t]; linarith
  have hdY : ∀ t, dm Y g t - dm Y h t = z t - (∑ s, z s) / (p + q) := by
    intro t
    simp only [dm, rowMean, z, ← hm, sum_sub_distrib, sub_div]; ring
  have hlin : ∀ (S : Finset T) (α β : ℝ), ∑ t ∈ S, α * (z t - β)
      = α * (∑ t ∈ S, z t - S.card * β) := fun S α β => by
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hin : ∀ (f : ℝ → ℝ), ∑ t ∈ P, f (if t ∈ P then 1 else 0) = ∑ t ∈ P, f 1 :=
    fun f => sum_congr rfl fun t ht => by simp [ht]
  have hout : ∀ (f : ℝ → ℝ), ∑ t ∈ Pᶜ, f (if t ∈ P then 1 else 0) = ∑ t ∈ Pᶜ, f 0 :=
    fun f => sum_congr rfl fun t ht => by simp [Finset.mem_compl.mp ht]
  have hZ : ∑ s, z s = ∑ t ∈ P, z t + ∑ t ∈ Pᶜ, z t := hsplit z
  have hnum : pairNum D Y g h = (q * ∑ t ∈ P, z t - p * ∑ t ∈ Pᶜ, z t) / (p + q) := by
    simp only [pairNum, hdD, hdY]
    rw [hsplit]
    have e1 : ∑ t ∈ P, ((if t ∈ P then (1 : ℝ) else 0) - p / (p + q)) *
        (z t - (∑ s, z s) / (p + q)) = ∑ t ∈ P, (1 - p / (p + q)) * (z t - (∑ s, z s) / (p + q)) :=
      sum_congr rfl fun t ht => by simp [ht]
    have e2 : ∑ t ∈ Pᶜ, ((if t ∈ P then (1 : ℝ) else 0) - p / (p + q)) *
        (z t - (∑ s, z s) / (p + q)) = ∑ t ∈ Pᶜ, (0 - p / (p + q)) * (z t - (∑ s, z s) / (p + q)) :=
      sum_congr rfl fun t ht => by simp [Finset.mem_compl.mp ht]
    rw [e1, e2, hlin, hlin, hZ]
    simp only [p, q]
    field_simp
    ring
  have hvar : pairVar D g h = p * q / (p + q) := by
    simp only [pairVar, hdD]
    rw [hsplit, hin (fun x => (x - p / (p + q)) ^ 2), hout (fun x => (x - p / (p + q)) ^ 2),
      sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp only [p, q]
    field_simp
    ring
  rw [pairCoef, hnum, hvar]
  field_simp

omit [Fintype G] [Nonempty G] [Nonempty T] in
/-- **The two comparisons inside a timing pair** (Goodman-Bacon 2021, eq. (10)):
if the periods outside the treated-only window `P` split into a pre-window `A`
and a post-window `B`, the pair coefficient is the weighted average
`s·(ΔȲ_P − ΔȲ_A) + (1 − s)·(ΔȲ_P − ΔȲ_B)` with `s = |A| / (|A| + |B|)`. For an
early-vs-late pair, the first comparison uses the late group as control before it
is treated; the second uses the already-treated early group as control (the
"forbidden" comparison). -/
theorem pairCoef_split [DecidableEq T] (D Y : G → T → ℝ) (g h : G) (P A B : Finset T)
    (hP : 0 < P.card) (hA : 0 < A.card) (hB : 0 < B.card) (hAB : Disjoint A B)
    (hPc : Pᶜ = A ∪ B) (hD : ∀ t, D g t - D h t = if t ∈ P then 1 else 0) :
    pairCoef D Y g h =
      (A.card / (A.card + B.card) : ℝ) * ((∑ t ∈ P, (Y g t - Y h t)) / P.card
          - (∑ t ∈ A, (Y g t - Y h t)) / A.card)
        + (B.card / (A.card + B.card) : ℝ) * ((∑ t ∈ P, (Y g t - Y h t)) / P.card
          - (∑ t ∈ B, (Y g t - Y h t)) / B.card) := by
  have hcard : (Pᶜ.card : ℝ) = A.card + B.card := by
    rw [hPc, card_union_of_disjoint hAB, Nat.cast_add]
  have hPc0 : 0 < Pᶜ.card := by rw [hPc, card_union_of_disjoint hAB]; omega
  rw [pairCoef_indicator D Y g h P hP hPc0 hD, hcard, hPc, sum_union hAB]
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB
  field_simp
  ring

namespace Example

/-- **Non-vacuity and the "forbidden comparison"** in the staggered example of
`Causal.TWFE.Example` (early group `0` treated in periods 1–2, late group `1` in
period 2): the hypotheses of `goodman_bacon` and `pairCoef_indicator` hold (the
treatment difference is the indicator of period 1), and the decomposition
reproduces the TWFE coefficient `−1/2`, which equals the 2×2 comparison of
period 1 against periods 0 and 2 (the latter using the already-treated early
group as a control). -/
theorem bacon_witness :
    (∑ g, ∑ t, eps D g t * D g t ≠ 0) ∧
    (∀ t, D 0 t - D 1 t = if t ∈ ({1} : Finset (Fin 3)) then 1 else 0) ∧
    ∑ g, ∑ h, baconWeight D g h * pairCoef D Y g h = -1 / 2 := by
  refine ⟨by rw [den]; norm_num, fun t => by fin_cases t <;> simp [D], ?_⟩
  exact (goodman_bacon isTWFE_example (by rw [den]; norm_num)).symm

end Example

end Econ.Causal.TWFE
