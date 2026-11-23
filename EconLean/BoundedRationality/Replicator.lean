/-
# Replicator dynamics and evolutionary stability

References. P. Taylor and L. Jonker (1978), "Evolutionarily Stable Strategies
and Game Dynamics", *Math. Biosciences* 40; J. Hofbauer, P. Schuster and
K. Sigmund (1979), "A Note on Evolutionary Stable Strategies and Game
Dynamics", *J. Theor. Biol.* 81; J. Weibull (1995), *Evolutionary Game
Theory*, §3.5 (Proposition 3.10 and its proof).

A population state is a probability vector `x` over the `n` pure strategies
of a symmetric game with payoff matrix `A`; the fitness of strategy `i` is
`(A x)ᵢ` (`fit`) and the average fitness is `xᵀ A x = E A x x`. The
**replicator dynamics** is

    ẋᵢ = xᵢ ((A x)ᵢ − xᵀ A x).

**Results.**
* `fit_eq_of_interior_nash`: at an interior symmetric Nash equilibrium every
  pure strategy earns the same fitness.
* `interior_ess_superior`: an interior ESS `x*` is *globally* superior: it
  earns strictly more against every other population state `y` than `y` earns
  against itself, `E(y, y) < E(x*, y)`.
* `isReplicatorPath_const`: an interior Nash equilibrium is a rest point.
* `hasDerivAt_lyapunov`: along any interior solution of the replicator
  dynamics, the relative entropy `V(t) = KL(x* ‖ x(t))` has derivative
  `−(E(x*, x) − E(x, x))`.
* `lyapunov_strictAnti`: if `x*` is an interior ESS, `V` is strictly
  decreasing along every interior solution that never sits at `x*`; `V ≥ 0`
  with equality only at `x*` (`lyapunov_nonneg`, `lyapunov_eq_zero_iff`). So
  `KL(x* ‖ ·)` is a strict Lyapunov function, the key step of the
  Hofbauer–Schuster–Sigmund proof that an interior ESS attracts all interior
  trajectories. `lyapunov_antitone` drops the assumption that the path avoids
  `x*` (it is otherwise implied by uniqueness of solutions).

* `tendsto_ess` (**convergence**): every interior solution converges to an
  interior ESS, `x(t) → x*` as `t → ∞`. The sublevel set
  `{KL(x* ‖ ·) ≤ KL(x* ‖ x(0))}` stays a fixed distance from the boundary
  (`le_coord`), so it is compact; on it, away from `x*`, the decrease rate
  `E(x*, x) − E(x, x)` is bounded below, which forces `KL → 0`, and
  `KL(x* ‖ ·)` vanishes only at `x*`.

The solution is assumed to exist on all of `ℝ` and to stay in the interior of
the simplex (which the replicator dynamics preserves; existence and
invariance are not formalized).
-/
module

public import EconLean.BoundedRationality.ESS
public import EconLean.Behavioral.RationalInattention
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section

namespace Econ

namespace ESS

open Finset Real Econ.Logit Econ.RationalInattention

variable {n : ℕ}

/-- Fitness of pure strategy `i` in population `x`: `(A x)ᵢ`. -/
def fit (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ := ∑ j, A i j * x j

theorem E_eq_sum_fit (A : Fin n → Fin n → ℝ) (y x : Fin n → ℝ) :
    E A y x = ∑ i, y i * fit A x i := by
  simp only [E, fit, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- At an interior symmetric Nash equilibrium all pure strategies are equally fit. -/
theorem fit_eq_of_interior_nash {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (h : IsNash A x)
    (hpos : ∀ i, 0 < x i) (i : Fin n) : fit A x i = E A x x := by
  have hle : ∀ k, fit A x k ≤ E A x x := fun k => by
    have := h.2 (degenerate k) (degenerate_mem k)
    simpa [E_eq_sum_fit, degenerate, ite_mul] using this
  have hsum : ∑ k, x k * (E A x x - fit A x k) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, h.1.2, one_mul, ← E_eq_sum_fit, sub_self]
  have := (sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg (hpos k).le (sub_nonneg.2 (hle k))).1 hsum i (mem_univ i)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (hpos i).ne'
  · linarith

/-- **An interior ESS is globally superior** (Hofbauer–Schuster–Sigmund). -/
theorem interior_ess_superior {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} (h : IsESS A x)
    (hpos : ∀ i, 0 < x i) {y : Fin n → ℝ} (hy : y ∈ lotteries (Fin n)) (hyx : y ≠ x) :
    E A y y < E A x y := by
  have heq : E A y x = E A x x := by
    rw [E_eq_sum_fit, sum_congr rfl fun i _ => by
      rw [fit_eq_of_interior_nash (isNash_of_isESS h) hpos i], ← sum_mul, hy.2, one_mul]
  rcases h.2 y hy hyx with h1 | ⟨-, h2⟩
  · exact absurd heq h1.ne
  · exact h2

/-- An interior solution of the replicator dynamics. -/
def IsReplicatorPath (A : Fin n → Fin n → ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  ∀ t, (∀ i, 0 < x t i) ∧ ∑ i, x t i = 1 ∧
    ∀ i, HasDerivAt (fun t => x t i) (x t i * (fit A (x t) i - E A (x t) (x t))) t

/-- Non-vacuity: the constant path at an interior symmetric Nash equilibrium
is a replicator path (a rest point). -/
theorem isReplicatorPath_const {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsNash A xs)
    (hpos : ∀ i, 0 < xs i) : IsReplicatorPath A fun _ => xs := fun t =>
  ⟨hpos, h.1.2, fun i => by
    rw [fit_eq_of_interior_nash h hpos i, sub_self, mul_zero]
    exact hasDerivAt_const t (xs i)⟩

/-- **The relative-entropy Lyapunov function.** Along the replicator
dynamics, `d/dt KL(x* ‖ x(t)) = −(E(x*, x) − E(x, x))`. -/
theorem hasDerivAt_lyapunov {A : Fin n → Fin n → ℝ} {x : ℝ → Fin n → ℝ}
    (hx : IsReplicatorPath A x) {xs : Fin n → ℝ} (hxs : ∑ i, xs i = 1) (t : ℝ) :
    HasDerivAt (fun t => kl xs (x t)) (-(E A xs (x t) - E A (x t) (x t))) t := by
  obtain ⟨hpos, -, hd⟩ := hx t
  have hi : ∀ i, HasDerivAt (fun t => xs i * log (xs i) - xs i * log (x t i))
      (-(xs i * (fit A (x t) i - E A (x t) (x t)))) t := fun i => by
    have h1 := ((hd i).log (hpos i).ne').const_mul (xs i)
    have h2 := h1.const_sub (xs i * log (xs i))
    convert h2 using 1
    field_simp [(hpos i).ne']
  have hs := HasDerivAt.fun_sum (u := univ) fun i _ => hi i
  unfold kl
  convert hs using 1
  rw [sum_neg_distrib, E_eq_sum_fit]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hxs, one_mul]

theorem lyapunov_nonneg {xs y : Fin n → ℝ} [NeZero n] (hxs : xs ∈ lotteries (Fin n))
    (hy : y ∈ lotteries (Fin n)) (hpos : ∀ i, 0 < y i) : 0 ≤ kl xs y :=
  kl_nonneg ⟨hxs.1, hxs.2⟩ ⟨hy.1, hy.2⟩ hpos

theorem lyapunov_eq_zero_iff {xs y : Fin n → ℝ} [NeZero n] (hxs : xs ∈ lotteries (Fin n))
    (hy : y ∈ lotteries (Fin n)) (hpos : ∀ i, 0 < y i) : kl xs y = 0 ↔ xs = y :=
  kl_eq_zero_iff ⟨hxs.1, hxs.2⟩ ⟨hy.1, hy.2⟩ hpos

/-- Without excluding the rest point: `KL(x* ‖ x(t))` is nonincreasing along
every interior solution when `x*` is an interior ESS. -/
theorem lyapunov_antitone {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsESS A xs)
    (hpos : ∀ i, 0 < xs i) {x : ℝ → Fin n → ℝ} (hx : IsReplicatorPath A x) :
    Antitone fun t => kl xs (x t) := by
  apply antitone_of_deriv_nonpos fun t => (hasDerivAt_lyapunov hx h.1.2 t).differentiableAt
  intro t
  rw [(hasDerivAt_lyapunov hx h.1.2 t).deriv]
  by_cases he : x t = xs
  · rw [he]; simp
  · have := interior_ess_superior h hpos ⟨fun i => ((hx t).1 i).le, (hx t).2.1⟩ he
    linarith

/-- **An interior ESS is a strict Lyapunov point of the replicator
dynamics**: `KL(x* ‖ x(t))` strictly decreases along every interior solution
that never sits at `x*`. -/
theorem lyapunov_strictAnti {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsESS A xs)
    (hpos : ∀ i, 0 < xs i) {x : ℝ → Fin n → ℝ} (hx : IsReplicatorPath A x)
    (hne : ∀ t, x t ≠ xs) : StrictAnti fun t => kl xs (x t) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hasDerivAt_lyapunov hx h.1.2 t).deriv]
  have := interior_ess_superior h hpos ⟨fun i => ((hx t).1 i).le, (hx t).2.1⟩ (hne t)
  linarith

/-! ### Convergence to an interior ESS -/

section Convergence

/-- The entropy `H(x*) = −Σ x*ᵢ log x*ᵢ`. -/
def ent (xs : Fin n → ℝ) : ℝ := ∑ i, -(xs i * log (xs i))

theorem ent_nonneg {xs : Fin n → ℝ} (h : xs ∈ lotteries (Fin n)) : 0 ≤ ent xs := by
  refine sum_nonneg fun i _ => neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (h.1 i)
    (log_nonpos (h.1 i) ?_))
  have := single_le_sum (f := xs) (fun j _ => h.1 j) (mem_univ i)
  rwa [h.2] at this

theorem neg_mul_log_le_kl {xs y : Fin n → ℝ} (hxs : ∀ i, 0 ≤ xs i) (hy : ∀ i, 0 < y i)
    (hy1 : ∀ i, y i ≤ 1) (k : Fin n) : -(xs k * log (y k)) ≤ kl xs y + ent xs := by
  have e : kl xs y + ent xs = ∑ i, -(xs i * log (y i)) := by
    simp only [kl, ent, ← sum_add_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [e]
  exact single_le_sum (f := fun i => -(xs i * log (y i)))
    (fun i _ => neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (hxs i)
      (log_nonpos (hy i).le (hy1 i)))) (mem_univ k)

/-- A bound on `KL(x* ‖ y)` keeps `y` away from the boundary. -/
theorem le_coord {xs y : Fin n → ℝ} (hxs : ∀ i, 0 ≤ xs i) (hy : ∀ i, 0 < y i)
    (hy1 : ∀ i, y i ≤ 1) {k : Fin n} (hk : 0 < xs k) {V0 : ℝ} (hV : kl xs y ≤ V0) :
    exp (-(V0 + ent xs) / xs k) ≤ y k := by
  have h := neg_mul_log_le_kl hxs hy hy1 k
  have : -(V0 + ent xs) / xs k ≤ log (y k) := by
    rw [div_le_iff₀ hk]; linarith [mul_comm (xs k) (log (y k))]
  calc exp _ ≤ exp (log (y k)) := exp_le_exp.2 this
    _ = y k := exp_log (hy k)

/-- **An interior ESS attracts every interior solution of the replicator
dynamics** (Taylor–Jonker; Hofbauer–Schuster–Sigmund; Weibull Theorem 3.5 for
the interior case). -/
theorem tendsto_ess [NeZero n] {A : Fin n → Fin n → ℝ} {xs : Fin n → ℝ} (h : IsESS A xs)
    (hpos : ∀ i, 0 < xs i) {x : ℝ → Fin n → ℝ} (hx : IsReplicatorPath A x) :
    Filter.Tendsto x Filter.atTop (nhds xs) := by
  set V : ℝ → ℝ := fun t => kl xs (x t) with hVdef
  have hanti : Antitone V := lyapunov_antitone h hpos hx
  have hlot : ∀ t, x t ∈ lotteries (Fin n) := fun t => ⟨fun i => ((hx t).1 i).le, (hx t).2.1⟩
  have hV0 : ∀ t, 0 ≤ V t := fun t => lyapunov_nonneg h.1 (hlot t) (hx t).1
  have hle1 : ∀ t i, x t i ≤ 1 := fun t i => by
    have := single_le_sum (f := x t) (fun j _ => ((hx t).1 j).le) (mem_univ i)
    rwa [(hx t).2.1] at this
  -- a uniform distance from the boundary for `t ≥ 0`
  obtain ⟨k0, -, hk0⟩ := exists_min_image univ xs univ_nonempty
  set a := V 0 + ent xs
  have ha : 0 ≤ a := add_nonneg (hV0 0) (ent_nonneg h.1)
  set c := exp (-a / xs k0)
  have hc : 0 < c := exp_pos _
  have hlow : ∀ t, 0 ≤ t → ∀ i, c ≤ x t i := fun t ht i => by
    refine le_trans (exp_le_exp.2 ?_) (le_coord (fun j => (hpos j).le) (hx t).1 (hle1 t)
      (hpos i) (hanti ht))
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left ha (hpos k0) (hk0 i (mem_univ i))
  set K : Set (Fin n → ℝ) := {y | (∀ i, c ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i = 1}
  have hK : IsCompact K := by
    have h1 : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.Icc c 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have h2 : IsClosed {y : Fin n → ℝ | ∑ i, y i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    convert h1.inter_right h2 using 1
    ext y
    simp only [K, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc,
      Set.mem_ofPred_eq]
  have hxK : ∀ t, 0 ≤ t → x t ∈ K := fun t ht =>
    ⟨fun i => ⟨hlow t ht i, hle1 t i⟩, (hx t).2.1⟩
  have hKlot : ∀ y ∈ K, y ∈ lotteries (Fin n) := fun y hy =>
    ⟨fun i => hc.le.trans (hy.1 i).1, hy.2⟩
  have hKpos : ∀ y ∈ K, ∀ i, 0 < y i := fun y hy i => lt_of_lt_of_le hc (hy.1 i).1
  have hklc : ContinuousOn (kl xs) K := by
    unfold kl
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact continuousOn_const.sub (continuousOn_const.mul
      ((continuous_apply i).continuousOn.log fun y hy => (hKpos y hy i).ne'))
  have hf : Continuous fun y : Fin n → ℝ => E A xs y - E A y y := by
    unfold E; fun_prop
  -- Step 1: `V(t) → 0`
  have hbdd : BddBelow (Set.range V) := ⟨0, by rintro _ ⟨t, rfl⟩; exact hV0 t⟩
  have hL := tendsto_atTop_ciInf hanti hbdd
  have hL0 : ⨅ t, V t = 0 := by
    set L := ⨅ t, V t
    have hLge : 0 ≤ L := le_ciInf hV0
    have hLle : ∀ t, L ≤ V t := fun t => ciInf_le hbdd t
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hLge (Ne.symm hne)
    set KL := K ∩ kl xs ⁻¹' Set.Ici L
    have hKLc : IsCompact KL :=
      hK.of_isClosed_subset (hklc.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
        Set.inter_subset_left
    obtain ⟨y0, hy0, hmin⟩ := hKLc.exists_isMinOn ⟨x 0, hxK 0 le_rfl, hLle 0⟩ hf.continuousOn
    have hy0ne : y0 ≠ xs := fun he => by
      have : L ≤ kl xs y0 := hy0.2
      rw [he, (lyapunov_eq_zero_iff h.1 h.1 hpos).2 rfl] at this; linarith
    set δ := E A xs y0 - E A y0 y0
    have hδ : 0 < δ := sub_pos.2 (interior_ess_superior h hpos (hKlot y0 hy0.1) hy0ne)
    have hdiff : ∀ t, HasDerivAt (fun t => V t + δ * t)
        (-(E A xs (x t) - E A (x t) (x t)) + δ * 1) t := fun t =>
      (hasDerivAt_lyapunov hx h.1.2 t).add ((hasDerivAt_id' t).const_mul δ)
    have hd : ∀ t, 0 ≤ t → deriv (fun t => V t + δ * t) t ≤ 0 := fun t ht => by
      rw [(hdiff t).deriv]
      have := hmin (show x t ∈ KL from ⟨hxK t ht, hLle t⟩)
      simp only [Set.mem_ofPred_eq] at this
      simp only [mul_one]
      linarith
    have hmono : AntitoneOn (fun t => V t + δ * t) (Set.Ici 0) :=
      antitoneOn_of_deriv_nonpos (convex_Ici 0)
        (fun t _ => (hdiff t).continuousAt.continuousWithinAt)
        (fun t _ => (hdiff t).differentiableAt.differentiableWithinAt)
        (fun t ht => hd t (interior_subset ht))
    set T := (V 0 + 1) / δ
    have hT : 0 ≤ T := div_nonneg (by linarith [hV0 0]) hδ.le
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT) hT
    simp only [mul_zero, add_zero] at this
    have e : δ * T = V 0 + 1 := by simp only [T]; field_simp
    linarith [hV0 T]
  rw [hL0] at hL
  -- Step 2: `x(t) → x*`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set Kε := K ∩ {y | ε ≤ dist y xs}
  have hKεc : IsCompact Kε := hK.of_isClosed_subset
    (hK.isClosed.inter (isClosed_le continuous_const (continuous_id.dist continuous_const)))
    Set.inter_subset_left
  by_cases hKE : Kε.Nonempty
  · obtain ⟨y1, hy1, hmin1⟩ := hKεc.exists_isMinOn hKE (hklc.mono Set.inter_subset_left)
    have hm : 0 < kl xs y1 := by
      refine lt_of_le_of_ne (lyapunov_nonneg h.1 (hKlot y1 hy1.1) (hKpos y1 hy1.1))
        fun h0 => ?_
      have := (lyapunov_eq_zero_iff h.1 (hKlot y1 hy1.1) (hKpos y1 hy1.1)).1 h0.symm
      have h2 : ε ≤ dist y1 xs := hy1.2
      rw [this, dist_self] at h2; linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hL.eventually (gt_mem_nhds hm)).and
      (Filter.eventually_ge_atTop 0))
    refine ⟨N, fun t ht => ?_⟩
    by_contra hdist
    rw [not_lt] at hdist
    have := hmin1 (show x t ∈ Kε from ⟨hxK t (hN t ht).2, hdist⟩)
    simp only [Set.mem_ofPred_eq] at this
    linarith [(hN t ht).1]
  · refine ⟨0, fun t ht => ?_⟩
    by_contra hdist
    rw [not_lt] at hdist
    exact hKE ⟨x t, hxK t ht, hdist⟩

end Convergence

end ESS

end Econ
