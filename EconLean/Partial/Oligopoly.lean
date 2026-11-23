/-
# Oligopoly: Bertrand, Cournot, Stackelberg

MWG §12.C (Prop. 12.C.1, the Cournot model and its competitive limit); Stackelberg leadership
(MWG Example 9.D.1).

Main results:
* `bertrand_isNash_iff` (MWG Prop. 12.C.1, the Bertrand paradox): two firms with the same
  constant marginal cost `c` and a continuous, nonincreasing, nonnegative demand `x` with
  `x(c) > 0`. The unique pure-strategy Nash equilibrium of price competition is `p₁ = p₂ = c`:
  firms make zero profit.
* `cournot_isEq_iff` (MWG §12.C): with linear inverse demand `P(Q) = a − bQ`, `a > c`,
  `b > 0`, and `n` firms of marginal cost `c` choosing quantities `qᵢ ≥ 0`, the unique Cournot
  equilibrium is symmetric with `qᵢ = (a − c) / ((n + 1) b)`.
* `cournot_price` and `cournot_price_tendsto` (MWG §12.C): the equilibrium price
  is `(a + n c) / (n + 1)`, strictly above `c`, and it converges to the competitive price `c`
  as `n → ∞`.
* `stackelberg_leader_optimal`: in the Stackelberg duopoly (leader moves first, the follower
  best-responds), the leader's optimal output is `(a − c)/(2b)`, the follower's is
  `(a − c)/(4b)`, and the leader earns `(a − c)²/(8b)`, more than the symmetric Cournot
  duopoly profit `(a − c)²/(9b)` (the last conjunct is the bare comparison with that number).
-/
module

public import EconLean.Games.Strategic
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Econ

open Function Filter Topology Finset

/-! ### Bertrand -/

/-- Profit of a firm charging `a` when its rival charges `b`: the lower price takes the whole
market `x(a)`, equal prices split it. -/
noncomputable def bertrandShare (c : ℝ) (x : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a < b then (a - c) * x a else if a = b then (a - c) * x a / 2 else 0

/-- The Bertrand duopoly as a strategic game: players `true`, `false`, strategies are prices. -/
noncomputable def bertrandProfit (c : ℝ) (x : ℝ → ℝ) (i : Bool) (p : Bool → ℝ) : ℝ :=
  bertrandShare c x (p i) (p (!i))

lemma bertrandProfit_update (c : ℝ) (x : ℝ → ℝ) (i : Bool) (p : Bool → ℝ) (t : ℝ) :
    bertrandProfit c x i (update p i t) = bertrandShare c x t (p (!i)) := by
  simp [bertrandProfit]

/-- Just above marginal cost, a firm makes a strictly positive profit (demand is positive at
cost and continuous). -/
lemma bertrand_exists_pos {c : ℝ} {x : ℝ → ℝ} (hx : Continuous x) (hxc : 0 < x c) {b : ℝ}
    (hb : c < b) : ∃ t, c < t ∧ t < b ∧ 0 < (t - c) * x t := by
  have h1 : ∀ᶠ t in 𝓝[>] c, 0 < x t :=
    nhdsWithin_le_nhds ((hx.tendsto c).eventually (lt_mem_nhds hxc))
  have h2 : ∀ᶠ t in 𝓝[>] c, t < b := nhdsWithin_le_nhds (gt_mem_nhds hb)
  obtain ⟨t, ⟨h1, h2⟩, h3⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  exact ⟨t, h3, h2, mul_pos (sub_pos.2 h3) h1⟩

/-- **The Bertrand paradox** (MWG Prop. 12.C.1). With identical constant marginal cost `c`
and a continuous, nonincreasing, nonnegative demand with `x(c) > 0` (linear demand with a
choke price above `c` qualifies), the unique pure-strategy Nash equilibrium of the Bertrand
duopoly is marginal-cost pricing. -/
theorem bertrand_isNash_iff {c : ℝ} {x : ℝ → ℝ} (hx : Continuous x) (hanti : Antitone x)
    (hx0 : ∀ p, 0 ≤ x p) (hxc : 0 < x c) (p : Bool → ℝ) :
    IsNash (bertrandProfit c x) p ↔ p = fun _ => c := by
  constructor
  · intro h
    have hdev : ∀ i t, bertrandShare c x t (p (!i)) ≤ bertrandShare c x (p i) (p (!i)) :=
      fun i t => by
        have := h i t
        rwa [bertrandProfit_update] at this
    -- Profits are nonnegative: pricing above the rival sells nothing.
    have hnn : ∀ i, 0 ≤ bertrandShare c x (p i) (p (!i)) := fun i => by
      have := hdev i (p (!i) + 1)
      simpa [bertrandShare, show ¬ p (!i) + 1 < p (!i) by linarith,
        show p (!i) + 1 ≠ p (!i) by linarith] using this
    -- Facing a rival above cost, a firm earns a strictly positive profit.
    have hposprof : ∀ i, c < p (!i) → 0 < bertrandShare c x (p i) (p (!i)) := fun i hb => by
      obtain ⟨t, -, htb, hpos⟩ := bertrand_exists_pos hx hxc hb
      have := hdev i t
      have e : bertrandShare c x t (p (!i)) = (t - c) * x t := by simp [bertrandShare, htb]
      linarith
    -- A positive profit means pricing above cost, weakly below the rival.
    have hshape : ∀ i, 0 < bertrandShare c x (p i) (p (!i)) → c < p i ∧ p i ≤ p (!i) :=
      fun i hp => by
        unfold bertrandShare at hp
        split_ifs at hp with h1 h2
        · refine ⟨?_, h1.le⟩
          by_contra hc; push Not at hc; nlinarith [hx0 (p i)]
        · refine ⟨?_, h2.le⟩
          by_contra hc; push Not at hc; nlinarith [hx0 (p i)]
        · exact absurd hp (lt_irrefl 0)
    -- No price below cost.
    have hge : ∀ i, c ≤ p i := by
      intro i
      by_contra hlt
      push Not at hlt
      have hxi : 0 < x (p i) := lt_of_lt_of_le hxc (hanti hlt.le)
      have hlt' : p (!i) < p i := by
        have := hnn i
        unfold bertrandShare at this
        split_ifs at this with h1 h2
        · nlinarith
        · nlinarith
        · push Not at h1; exact lt_of_le_of_ne h1 (Ne.symm h2)
      have hlt2 : p (!i) < c := hlt'.trans hlt
      have hx2 : 0 < x (p (!i)) := lt_of_lt_of_le hxc (hanti hlt2.le)
      have := hnn (!i)
      rw [Bool.not_not] at this
      simp only [bertrandShare, hlt', ↓reduceIte] at this
      nlinarith
    -- No price above cost.
    have hle : ∀ i, p i ≤ c := by
      intro j
      by_contra hgt
      push Not at hgt
      have h1 := hshape (!j) (hposprof (!j) (by rwa [Bool.not_not]))
      rw [Bool.not_not] at h1
      have h2 := hshape j (hposprof j h1.1)
      have heq : p j = p (!j) := le_antisymm h2.2 h1.2
      have hpj := hposprof j h1.1
      rw [← heq] at hpj
      simp only [bertrandShare, lt_irrefl, ↓reduceIte] at hpj
      -- Undercutting to `t` slightly below `p j` gives almost the whole-market profit.
      set g : ℝ → ℝ := fun t => (t - c) * x t
      have hbound : ∀ t, c < t → t < p j → g t ≤ g (p j) / 2 := fun t _ hta => by
        have := hdev j t
        rw [← heq] at this
        simpa [bertrandShare, hta, g] using this
      have hg : Continuous g := (continuous_id.sub continuous_const).mul hx
      have hlim : g (p j) ≤ g (p j) / 2 := by
        refine le_of_tendsto (x := 𝓝[<] (p j)) ((hg.tendsto (p j)).mono_left nhdsWithin_le_nhds) ?_
        have hc' : ∀ᶠ t in 𝓝[<] (p j), c < t := nhdsWithin_le_nhds (lt_mem_nhds h2.1)
        filter_upwards [hc', self_mem_nhdsWithin] with t hct hta using hbound t hct hta
      have : 0 < g (p j) := by simp only [g]; linarith
      linarith
    funext i
    exact le_antisymm (hle i) (hge i)
  · rintro rfl i t
    rw [bertrandProfit_update]
    simp only [bertrandProfit, bertrandShare, lt_irrefl, ↓reduceIte, sub_self, zero_mul,
      zero_div]
    split_ifs with h1 h2
    · nlinarith [hx0 t]
    · rw [h2, sub_self, zero_mul, zero_div]
    · exact le_rfl

/-! ### Cournot -/

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Profit of firm `i` in the Cournot oligopoly with inverse demand `a − bQ` and marginal
cost `c`. -/
def cournotProfit (a b c : ℝ) (i : I) (q : I → ℝ) : ℝ := q i * (a - b * ∑ j, q j - c)

/-- **Cournot equilibrium**: nonnegative outputs, and no firm gains by changing its own output
to any `t ≥ 0`. -/
def IsCournotEq (a b c : ℝ) (q : I → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∀ i t, 0 ≤ t → cournotProfit a b c i (update q i t) ≤ cournotProfit a b c i q

omit [Fintype I] in
lemma cournot_sum_update [Fintype I] (q : I → ℝ) (i : I) (t : ℝ) :
    ∑ j, update q i t j = ∑ j, q j + (t - q i) := by
  have : ∀ j, update q i t j = q j + if j = i then t - q i else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp only [this, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]

/-- The Cournot quantity with `n` firms. -/
noncomputable def cournotQ (a b c : ℝ) (n : ℕ) : ℝ := (a - c) / ((n + 1) * b)

/-- **Cournot equilibrium with linear demand** (MWG §12.C). The unique Cournot equilibrium
is symmetric, each firm producing `(a − c) / ((n + 1) b)`. -/
theorem cournot_isEq_iff {a b c : ℝ} (hb : 0 < b) (hac : c < a) (q : I → ℝ) :
    IsCournotEq a b c q ↔ ∀ i, q i = cournotQ a b c (Fintype.card I) := by
  set n := Fintype.card I
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  -- The deviation payoff of firm `i`: with `A = a − c − b (Q − qᵢ)`, `π(t) = t (A − b t)`.
  have hprof : ∀ i t, cournotProfit a b c i (update q i t) =
      t * ((a - c - b * (∑ j, q j - q i)) - b * t) := by
    intro i t
    simp only [cournotProfit, update_self, cournot_sum_update]
    ring
  have hown : ∀ i, cournotProfit a b c i q = q i * ((a - c - b * (∑ j, q j - q i)) - b * q i) := by
    intro i; simp only [cournotProfit]; ring
  constructor
  · rintro ⟨hq0, hdev⟩
    set Q := ∑ j, q j
    -- Each firm is at its best response.
    have hbr : ∀ i, (0 < a - c - b * (Q - q i) → b * q i = a - c - b * Q) ∧
        (a - c - b * (Q - q i) ≤ 0 → q i = 0) := by
      intro i
      set A := a - c - b * (Q - q i) with hAdef
      have hd : ∀ t, 0 ≤ t → t * (A - b * t) ≤ q i * (A - b * q i) := fun t ht => by
        have := hdev i t ht; rwa [hprof, hown] at this
      constructor
      · intro hA
        have := hd (A / (2 * b)) (by positivity)
        have hsq : b * (q i - A / (2 * b)) ^ 2 ≤ 0 := by
          have e : b * (q i - A / (2 * b)) ^ 2 = A / (2 * b) * (A - b * (A / (2 * b))) -
              q i * (A - b * q i) := by field_simp; ring
          linarith
        have : q i - A / (2 * b) = 0 := by
          have h0 : (q i - A / (2 * b)) ^ 2 ≤ 0 := by
            by_contra hc; push Not at hc; nlinarith
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h0 (sq_nonneg _))
        have hqi : q i = A / (2 * b) := by linarith
        have h2 : 2 * b * q i = A := by rw [hqi]; field_simp
        rw [hAdef] at h2
        linarith
      · intro hA
        have h0 := hd 0 le_rfl
        simp only [zero_mul] at h0
        have h1 : q i ^ 2 ≤ 0 := by nlinarith [hq0 i, mul_nonpos_of_nonneg_of_nonpos (hq0 i) hA]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h1 (sq_nonneg _))
    -- No firm is at a corner.
    have hint : ∀ i, 0 < a - c - b * (Q - q i) := by
      intro i
      by_contra hA
      push Not at hA
      have hQ : a - c ≤ b * Q := by have := (hbr i).2 hA; rw [this] at hA; linarith
      have hQpos : 0 < Q := by
        by_contra h; push Not at h; nlinarith
      obtain ⟨j, hj⟩ : ∃ j, 0 < q j := by
        by_contra h; push Not at h
        exact absurd (sum_nonpos fun j _ => h j) (not_le.2 hQpos)
      by_cases hAj : 0 < a - c - b * (Q - q j)
      · have := (hbr j).1 hAj; nlinarith
      · have := (hbr j).2 (not_lt.1 hAj); linarith
    have hfoc : ∀ i, b * q i = a - c - b * Q := fun i => (hbr i).1 (hint i)
    have hsum : b * Q = n * (a - c - b * Q) := by
      have e : b * Q = ∑ j, b * q j := by simp only [Q, mul_sum]
      conv_lhs => rw [e]
      simp only [hfoc, sum_const, card_univ, nsmul_eq_mul, n]
    intro i
    have hQ : b * Q = n * (a - c) / (n + 1) := by field_simp; linarith
    have := hfoc i
    simp only [cournotQ]
    field_simp
    rw [hQ] at this
    field_simp at this
    linarith
  · intro hq
    set qs := cournotQ a b c n
    have hqs : 0 ≤ qs := by simp only [qs, cournotQ]; exact div_nonneg (by linarith) (by positivity)
    refine ⟨fun i => (hq i).symm ▸ hqs, fun i t _ => ?_⟩
    have hQ : ∑ j, q j = n * qs := by simp [hq, n]
    rw [hprof, hown, hQ, hq i]
    have hA : a - c - b * (n * qs - qs) = 2 * b * qs := by
      simp only [qs, cournotQ]; field_simp; ring
    rw [hA]
    nlinarith [sq_nonneg (t - qs)]

/-- **The Cournot price** with `n` firms is `(a + n c)/(n + 1)`. -/
theorem cournot_price {a b c : ℝ} (hb : 0 < b) (n : ℕ) :
    a - b * (n * cournotQ a b c n) = (a + n * c) / (n + 1) := by
  simp only [cournotQ]; field_simp; ring

/-- The Cournot price exceeds marginal cost when `a > c`. -/
theorem cournot_price_gt {a c : ℝ} (hac : c < a) (n : ℕ) : c < (a + n * c) / (n + 1) := by
  rw [lt_div_iff₀ (by positivity)]; linarith

/-- **Cournot converges to competition** (MWG §12.C): as the number of firms grows, the
Cournot price tends to marginal cost. -/
theorem cournot_price_tendsto (a c : ℝ) :
    Tendsto (fun n : ℕ => (a + n * c) / (n + 1)) atTop (𝓝 c) := by
  have e : ∀ n : ℕ, (a + n * c) / (n + 1) = c + (a - c) / ((n : ℝ) + 1) := fun n => by
    field_simp; ring
  simp only [e]
  have : Tendsto (fun n : ℕ => (a - c) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (a - c) |>.comp (tendsto_add_atTop_nat 1) |>.congr
      fun n => by simp
  simpa using this.const_add c

/-! ### Stackelberg -/

/-- The follower's best response to the leader's output `q₁`. -/
noncomputable def stackelbergBR (a b c q₁ : ℝ) : ℝ := max 0 ((a - c - b * q₁) / (2 * b))

/-- The follower's best response is optimal. -/
theorem stackelbergBR_optimal {a b c q₁ : ℝ} (hb : 0 < b) (t : ℝ) (ht : 0 ≤ t) :
    t * (a - b * (q₁ + t) - c) ≤
      stackelbergBR a b c q₁ * (a - b * (q₁ + stackelbergBR a b c q₁) - c) := by
  simp only [stackelbergBR]
  rcases le_total 0 ((a - c - b * q₁) / (2 * b)) with h | h
  · rw [max_eq_right h]
    have e : (a - c - b * q₁) / (2 * b) * (a - b * (q₁ + (a - c - b * q₁) / (2 * b)) - c) -
        t * (a - b * (q₁ + t) - c) = b * (t - (a - c - b * q₁) / (2 * b)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (t - (a - c - b * q₁) / (2 * b))]
  · rw [max_eq_left h]
    have : a - c - b * q₁ ≤ 0 := by
      by_contra hc; push Not at hc
      have := div_pos hc (by positivity : (0 : ℝ) < 2 * b); linarith
    have : a - b * (q₁ + t) - c ≤ 0 := by nlinarith
    rw [zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ht this

/-- The leader's profit when the follower best-responds. -/
noncomputable def stackelbergLeader (a b c q₁ : ℝ) : ℝ :=
  q₁ * (a - b * (q₁ + stackelbergBR a b c q₁) - c)

/-- **The Stackelberg outcome.** The leader's optimal output is `(a − c)/(2b)`; the follower
then produces `(a − c)/(4b)`; the leader earns `(a − c)²/(8b)`, strictly more than
`(a − c)²/(9b)`, the profit of each firm in the symmetric Cournot duopoly (the last conjunct is
just this numerical comparison). -/
theorem stackelberg_leader_optimal {a b c : ℝ} (hb : 0 < b) (hac : c < a) :
    (∀ q₁, 0 ≤ q₁ → stackelbergLeader a b c q₁ ≤ stackelbergLeader a b c ((a - c) / (2 * b))) ∧
      stackelbergBR a b c ((a - c) / (2 * b)) = (a - c) / (4 * b) ∧
      stackelbergLeader a b c ((a - c) / (2 * b)) = (a - c) ^ 2 / (8 * b) ∧
      (a - c) ^ 2 / (9 * b) < (a - c) ^ 2 / (8 * b) := by
  have hbr : stackelbergBR a b c ((a - c) / (2 * b)) = (a - c) / (4 * b) := by
    simp only [stackelbergBR]
    rw [max_eq_right (by apply div_nonneg <;> [skip; positivity]; field_simp; linarith)]
    field_simp; ring
  have hval : stackelbergLeader a b c ((a - c) / (2 * b)) = (a - c) ^ 2 / (8 * b) := by
    simp only [stackelbergLeader, hbr]; field_simp; ring
  refine ⟨fun q₁ hq₁ => ?_, hbr, hval, ?_⟩
  · rw [hval]
    simp only [stackelbergLeader, stackelbergBR]
    rcases le_total 0 ((a - c - b * q₁) / (2 * b)) with h | h
    · rw [max_eq_right h]
      rw [le_div_iff₀ (by positivity)]
      have e : q₁ * (a - b * (q₁ + (a - c - b * q₁) / (2 * b)) - c) * (8 * b) =
          4 * b * q₁ * (a - c - b * q₁) := by field_simp; ring
      rw [e]
      nlinarith [sq_nonneg (2 * b * q₁ - (a - c))]
    · rw [max_eq_left h, add_zero]
      have : a - c - b * q₁ ≤ 0 := by
        by_contra hc; push Not at hc
        have := div_pos hc (by positivity : (0 : ℝ) < 2 * b); linarith
      have : q₁ * (a - b * q₁ - c) ≤ 0 := by nlinarith
      have : 0 ≤ (a - c) ^ 2 / (8 * b) := by positivity
      linarith
  · have : 0 < (a - c) ^ 2 := by nlinarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

end Econ
