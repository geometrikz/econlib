/-
# Logit quantal response equilibrium

Reference. R. McKelvey and T. Palfrey (1995), "Quantal Response Equilibria
for Normal Form Games", *GEB* 10(1).

**The model.** In a finite game, a mixed profile `σ` (a probability vector
`σ i` over each player's actions) is a **logit QRE** with precision `λ ≥ 0`
if every player's mixed strategy is the logit response to the expected
payoffs it faces:

    σ i b = exp(λ Uᵢ(b, σ₋ᵢ)) / Σ_c exp(λ Uᵢ(c, σ₋ᵢ)).

`λ = 0` is uniform randomization; `λ → ∞` approaches best responses.

**Results.**
* `qre_lambda_zero`: at `λ = 0` the unique QRE is uniform play;
* `isNash_of_tendsto_qre` (**McKelvey–Palfrey, Theorem 2**): every limit of
  logit QRE as `λ → ∞` is a (mixed) Nash equilibrium;
* `qre2x2_exists`, `exists_isLogitQRE_2x2`: existence of a logit QRE in
  every two-player, two-action game, from the intermediate value theorem;
  `isLogitQRE_of_qre2x2` shows the `(p, q)` parametrization gives a logit QRE
  in the general sense;
* `uniform_isLogitQRE_zero`: uniform play is a logit QRE at `λ = 0`.

**Scope.** McKelvey–Palfrey prove existence for every finite game from
Brouwer's fixed point theorem, which Mathlib does not have yet (see the
`BrouwerSimplex` discussion in `GE/Existence.lean`); here existence is proved
only in the 2×2 case.
-/
module

public import EconLean.BoundedRationality.LevelK
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace Econ

namespace BoundedRationality

open Finset Filter Topology Real

variable {I : Type*} [Fintype I] [DecidableEq I] (G : FiniteGame I)

/-- A mixed profile: a probability vector over each player's actions. -/
def IsMixedProfile (σ : ∀ i, G.A i → ℝ) : Prop :=
  ∀ i, (∀ b, 0 ≤ σ i b) ∧ ∑ b, σ i b = 1

/-- The point mass on action `b`. -/
def pointMass {α : Type} [DecidableEq α] (b : α) : α → ℝ := fun x => if x = b then 1 else 0

/-- Probability of pure profile `a` under independent mixing `σ`. -/
def profileProb (σ : ∀ i, G.A i → ℝ) (a : ∀ i, G.A i) : ℝ := ∏ j, σ j (a j)

/-- Expected payoff to player `i` of pure action `b` when the others mix
according to `σ`. -/
def U (σ : ∀ i, G.A i → ℝ) (i : I) (b : G.A i) : ℝ :=
  ∑ a : (∀ i, G.A i), profileProb G (Function.update σ i (pointMass b)) a * G.u i a

/-- Logit response: `exp(λ Uᵢ(b)) / Σ_c exp(λ Uᵢ(c))`. -/
noncomputable def logitResponse (lam : ℝ) (σ : ∀ i, G.A i → ℝ) (i : I) (b : G.A i) : ℝ :=
  exp (lam * U G σ i b) / ∑ c, exp (lam * U G σ i c)

/-- A logit quantal response equilibrium with precision `λ`. -/
def IsLogitQRE (lam : ℝ) (σ : ∀ i, G.A i → ℝ) : Prop :=
  ∀ i b, σ i b = logitResponse G lam σ i b

/-- A mixed Nash equilibrium: every action played with positive probability
is a best response. -/
def IsMixedNash (σ : ∀ i, G.A i → ℝ) : Prop :=
  IsMixedProfile G σ ∧ ∀ i b, 0 < σ i b → ∀ c, U G σ i c ≤ U G σ i b

variable [∀ i, Nonempty (G.A i)]

theorem sum_exp_pos (lam : ℝ) (σ : ∀ i, G.A i → ℝ) (i : I) :
    0 < ∑ c, exp (lam * U G σ i c) :=
  sum_pos (fun _ _ => exp_pos _) univ_nonempty

/-- A logit QRE is a mixed profile with full support. -/
theorem IsLogitQRE.isMixedProfile {lam : ℝ} {σ : ∀ i, G.A i → ℝ} (h : IsLogitQRE G lam σ) :
    IsMixedProfile G σ := by
  intro i
  refine ⟨fun b => by rw [h i b]; exact (div_pos (exp_pos _) (sum_exp_pos G lam σ i)).le, ?_⟩
  simp_rw [h i, logitResponse]
  rw [← sum_div, div_self (sum_exp_pos G lam σ i).ne']

omit [∀ i, Nonempty (G.A i)] in
/-- **At `λ = 0` a logit QRE is uniform play.** -/
theorem qre_lambda_zero {σ : ∀ i, G.A i → ℝ} (h : IsLogitQRE G 0 σ) (i : I) (b : G.A i) :
    σ i b = 1 / Fintype.card (G.A i) := by
  rw [h i b, logitResponse]
  simp

/-! ### The limit `λ → ∞` -/

omit [∀ i, Nonempty (G.A i)] in
/-- Expected payoffs are continuous in the opponents' mixed strategies. -/
theorem tendsto_U {σs : ℕ → ∀ i, G.A i → ℝ} {σ : ∀ i, G.A i → ℝ}
    (h : ∀ i b, Tendsto (fun n => σs n i b) atTop (𝓝 (σ i b))) (i : I) (b : G.A i) :
    Tendsto (fun n => U G (σs n) i b) atTop (𝓝 (U G σ i b)) := by
  unfold U profileProb
  refine tendsto_finsetSum _ fun a _ => (tendsto_finsetProd _ fun j _ => ?_).mul_const _
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; exact tendsto_const_nhds
  · simp only [Function.update_of_ne hj]; exact h j (a j)

/-- The logit probability of `b` is at most `exp(−λ (Uᵢ(c) − Uᵢ(b)))` for any
other action `c`. -/
theorem logitResponse_le (lam : ℝ) (σ : ∀ i, G.A i → ℝ) (i : I) (b c : G.A i) :
    logitResponse G lam σ i b ≤ exp (-(lam * (U G σ i c - U G σ i b))) := by
  unfold logitResponse
  rw [div_le_iff₀ (sum_exp_pos G lam σ i)]
  calc exp (lam * U G σ i b)
      = exp (-(lam * (U G σ i c - U G σ i b))) * exp (lam * U G σ i c) := by
        rw [← exp_add]; ring_nf
    _ ≤ exp (-(lam * (U G σ i c - U G σ i b))) * ∑ c, exp (lam * U G σ i c) := by
        apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
        exact single_le_sum (f := fun c => exp (lam * U G σ i c)) (fun c _ => (exp_pos _).le)
          (mem_univ c)

/-- **McKelvey–Palfrey (1995), Theorem 2: limits of logit QRE are Nash.** If
`λₙ → ∞`, each `σₙ` is a logit QRE at precision `λₙ`, and `σₙ → σ`, then `σ`
is a mixed Nash equilibrium. -/
theorem isNash_of_tendsto_qre {lams : ℕ → ℝ} (hlam : Tendsto lams atTop atTop)
    {σs : ℕ → ∀ i, G.A i → ℝ} (hqre : ∀ n, IsLogitQRE G (lams n) (σs n))
    {σ : ∀ i, G.A i → ℝ} (hconv : ∀ i b, Tendsto (fun n => σs n i b) atTop (𝓝 (σ i b))) :
    IsMixedNash G σ := by
  constructor
  · -- limits of probability vectors are probability vectors
    intro i
    refine ⟨fun b => ge_of_tendsto' (hconv i b) fun n => ((hqre n).isMixedProfile G i).1 b, ?_⟩
    have hs : Tendsto (fun n => ∑ b, σs n i b) atTop (𝓝 (∑ b, σ i b)) :=
      tendsto_finsetSum _ fun b _ => hconv i b
    have h1 : (fun n => ∑ b, σs n i b) = fun _ => (1 : ℝ) :=
      funext fun n => ((hqre n).isMixedProfile G i).2
    rw [h1] at hs
    exact tendsto_nhds_unique hs tendsto_const_nhds
  · intro i b hb c
    by_contra hlt
    push Not at hlt
    -- the payoff gap `Uᵢ(c) − Uᵢ(b)` converges to a positive number
    set δ := U G σ i c - U G σ i b with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hgap : Tendsto (fun n => U G (σs n) i c - U G (σs n) i b) atTop (𝓝 δ) :=
      (tendsto_U G hconv i c).sub (tendsto_U G hconv i b)
    have hev : ∀ᶠ n in atTop, δ / 2 < U G (σs n) i c - U G (σs n) i b :=
      hgap.eventually (lt_mem_nhds (by linarith))
    have hlpos : ∀ᶠ n in atTop, 0 ≤ lams n := hlam.eventually (eventually_ge_atTop 0)
    -- so `σₙ i b ≤ exp(−λₙ δ/2) → 0`
    have hbound : ∀ᶠ n in atTop, σs n i b ≤ exp (-(lams n * (δ / 2))) := by
      filter_upwards [hev, hlpos] with n h1 h2
      rw [hqre n i b]
      refine (logitResponse_le G (lams n) (σs n) i b c).trans ?_
      apply exp_le_exp.2
      have := mul_le_mul_of_nonneg_left h1.le h2
      linarith
    have hzero : Tendsto (fun n => exp (-(lams n * (δ / 2)))) atTop (𝓝 0) := by
      apply tendsto_exp_atBot.comp
      apply tendsto_neg_atTop_atBot.comp
      exact hlam.atTop_mul_const (by linarith)
    have hle : σ i b ≤ 0 := le_of_tendsto_of_tendsto (hconv i b) hzero hbound
    linarith

/-! ### Existence in 2×2 games -/

/-- The logistic function `1 / (1 + e^{−x})`: the logit probability of the
first of two actions when its payoff advantage is `x`. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + exp (-x))

theorem logistic_pos (x : ℝ) : 0 < logistic x := by
  unfold logistic; have := exp_pos (-x); positivity

theorem logistic_lt_one (x : ℝ) : logistic x < 1 := by
  unfold logistic
  rw [div_lt_one (by have := exp_pos (-x); linarith)]
  linarith [exp_pos (-x)]

theorem continuous_logistic : Continuous logistic := by
  unfold logistic
  exact continuous_const.div (continuous_const.add (continuous_exp.comp continuous_neg))
    fun x => by have := exp_pos (-x); linarith

/-- Row player's payoff advantage of action 0 over action 1 when the column
player plays action 0 with probability `q` (payoff matrix `R row col`). -/
def rowAdv (R : Fin 2 → Fin 2 → ℝ) (q : ℝ) : ℝ :=
  q * (R 0 0 - R 1 0) + (1 - q) * (R 0 1 - R 1 1)

/-- Column player's payoff advantage of action 0 over action 1 when the row
player plays action 0 with probability `p` (payoff matrix `C row col`). -/
def colAdv (C : Fin 2 → Fin 2 → ℝ) (p : ℝ) : ℝ :=
  p * (C 0 0 - C 0 1) + (1 - p) * (C 1 0 - C 1 1)

/-- A logit QRE of the 2×2 game `(R, C)`: `p`, `q` are the probabilities of
each player's first action, and each is the logit response to the other. -/
def IsQRE2x2 (lam : ℝ) (R C : Fin 2 → Fin 2 → ℝ) (p q : ℝ) : Prop :=
  p = logistic (lam * rowAdv R q) ∧ q = logistic (lam * colAdv C p)

/-- **Existence of logit QRE in every 2×2 game** (any `λ`), by the
intermediate value theorem. -/
theorem qre2x2_exists (lam : ℝ) (R C : Fin 2 → Fin 2 → ℝ) :
    ∃ p q, p ∈ Set.Ioo (0 : ℝ) 1 ∧ q ∈ Set.Ioo (0 : ℝ) 1 ∧ IsQRE2x2 lam R C p q := by
  -- `F p = row's response to column's response to p`; find a fixed point.
  set F : ℝ → ℝ := fun p => logistic (lam * rowAdv R (logistic (lam * colAdv C p))) with hF
  have hFc : Continuous F := by
    apply continuous_logistic.comp
    unfold rowAdv
    apply continuous_const.mul
    have hq : Continuous fun p => logistic (lam * colAdv C p) := by
      apply continuous_logistic.comp
      unfold colAdv
      fun_prop
    fun_prop
  have hcont : ContinuousOn (fun p => F p - p) (Set.Icc 0 1) :=
    (hFc.sub continuous_id).continuousOn
  have h0 : 0 ≤ F 0 - 0 := by simp only [sub_zero]; exact (logistic_pos _).le
  have h1 : F 1 - 1 ≤ 0 := by linarith [logistic_lt_one (lam * rowAdv R (logistic (lam * colAdv C 1)))]
  obtain ⟨p, hp, hfix⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont ⟨h1, h0⟩
  have hfix' : F p = p := by simp only at hfix; linarith
  refine ⟨p, logistic (lam * colAdv C p), ?_, ⟨logistic_pos _, logistic_lt_one _⟩, ?_, rfl⟩
  · rw [← hfix']; exact ⟨logistic_pos _, logistic_lt_one _⟩
  · exact hfix'.symm

/-! ### The 2×2 parametrization is the general concept -/

/-- The 2×2 game with row payoffs `R` and column payoffs `C`, as a finite game
(player `0` = row, player `1` = column). -/
abbrev game2x2 (R C : Fin 2 → Fin 2 → ℝ) : FiniteGame (Fin 2) where
  A := fun _ => Fin 2
  fintype := fun _ => inferInstance
  decEq := fun _ => inferInstance
  u := fun i a => if i = 0 then R (a 0) (a 1) else C (a 0) (a 1)

/-- The mixed profile in which row plays action `0` with probability `p` and
column plays action `0` with probability `q`. -/
def profile2x2 (R C : Fin 2 → Fin 2 → ℝ) (p q : ℝ) : ∀ i, (game2x2 R C).A i → ℝ :=
  fun i b => if i = 0 then (if b = 0 then p else 1 - p) else (if b = 0 then q else 1 - q)

theorem sum_fin2_arrow (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ a, f a = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, finTwoArrowEquiv]
  ring

theorem U_row (R C : Fin 2 → Fin 2 → ℝ) (p q : ℝ) (b : Fin 2) :
    U (game2x2 R C) (profile2x2 R C p q) 0 b = q * R b 0 + (1 - q) * R b 1 := by
  unfold U profileProb
  rw [sum_fin2_arrow]
  fin_cases b <;> simp [Fin.prod_univ_two, profile2x2, pointMass, Function.update]

theorem U_col (R C : Fin 2 → Fin 2 → ℝ) (p q : ℝ) (b : Fin 2) :
    U (game2x2 R C) (profile2x2 R C p q) 1 b = p * C 0 b + (1 - p) * C 1 b := by
  unfold U profileProb
  rw [sum_fin2_arrow]
  fin_cases b <;> simp [Fin.prod_univ_two, profile2x2, pointMass, Function.update]

/-- Two-action logit is the logistic function of the payoff difference. -/
theorem exp_div_exp_add_exp (a b : ℝ) : exp a / (exp a + exp b) = logistic (a - b) := by
  unfold logistic
  rw [show -(a - b) = b - a by ring, exp_sub]
  have := exp_pos a
  have := exp_pos b
  field_simp

theorem exp_div_exp_add_exp' (a b : ℝ) : exp b / (exp a + exp b) = 1 - logistic (a - b) := by
  rw [← exp_div_exp_add_exp]
  have := exp_pos a
  have := exp_pos b
  field_simp
  ring

/-- **The 2×2 QRE is a logit QRE of the 2×2 game.** -/
theorem isLogitQRE_of_qre2x2 {lam : ℝ} {R C : Fin 2 → Fin 2 → ℝ} {p q : ℝ}
    (h : IsQRE2x2 lam R C p q) : IsLogitQRE (game2x2 R C) lam (profile2x2 R C p q) := by
  unfold IsLogitQRE logitResponse
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩ <;>
    rw [Fin.sum_univ_two]
  · rw [exp_div_exp_add_exp, U_row, U_row]
    simp only [profile2x2, ite_true]
    rw [h.1, rowAdv]; congr 1; ring
  · rw [exp_div_exp_add_exp', U_row, U_row]
    simp only [profile2x2, ite_true]
    rw [h.1, rowAdv]; norm_num; congr 2; ring
  · rw [exp_div_exp_add_exp, U_col, U_col]
    simp only [profile2x2]
    rw [h.2, colAdv]; norm_num; congr 1; ring
  · rw [exp_div_exp_add_exp', U_col, U_col]
    simp only [profile2x2]
    rw [h.2, colAdv]; norm_num; congr 2; ring

/-- **Existence of logit QRE in every 2×2 game**, for the general concept. -/
theorem exists_isLogitQRE_2x2 (lam : ℝ) (R C : Fin 2 → Fin 2 → ℝ) :
    ∃ σ, IsLogitQRE (game2x2 R C) lam σ := by
  obtain ⟨p, q, -, -, h⟩ := qre2x2_exists lam R C
  exact ⟨_, isLogitQRE_of_qre2x2 h⟩

omit [∀ i, Nonempty (G.A i)] in
/-- Conversely, uniform play is a logit QRE at `λ = 0`. -/
theorem uniform_isLogitQRE_zero :
    IsLogitQRE G 0 (fun i _ => 1 / Fintype.card (G.A i)) := by
  intro i b
  simp [logitResponse]

end BoundedRationality

end Econ
