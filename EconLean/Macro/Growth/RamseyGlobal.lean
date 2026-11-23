/-
# Ramsey–Cass–Koopmans: global convergence to the modified golden rule

Stokey–Lucas (SL) Thm 6.1–6.2 / Exercise 6.1; Acemoglu Prop. 6.3 / Thm 6.6 (discrete time).

`Ramsey.lean` shows that every optimal capital path converges to *some* fixed
point of the policy `g`. With **Inada conditions** we pin the limit down: from
any `k₀ > 0`, the optimal path converges to the unique `k*` solving the
modified golden rule `β f'(k*) = 1`. That excludes the trivial steady state `0`.

**Inada conditions** (`RCKModel.Inada`): `u` and `f` are differentiable on
`(0, ∞)`, and `u'(c) → ∞` as `c → 0⁺`, `f'(k) → ∞` as `k → 0⁺`.

**Proof outline.**
1. `u'(0⁺) = ∞` ⇒ consumption is positive at every `k > 0`: `g(k) < f(k)`.
   Moving `ε` from savings to consumption gains `≈ u'(ε) ε`. It loses at most
   `β L ε`, where `L` is a secant slope of the concave value function.
2. `f'(0⁺) = ∞` ⇒ saving is positive at every `k > 0`: `g(k) > 0`. Saving `ε`
   gains at least `β s f(ε) ≥ β s f'(ε) ε` and loses at most `L_u ε`.
3. Interior choices therefore satisfy the Euler equation
   `u'(c) = β V'(g(k))` (first-order condition) and the envelope condition
   `V'(k) = u'(c) f'(k)` (Benveniste–Scheinkman). If `0 < k < k*` and
   `g(k) ≤ k`, concavity of `V` gives `V'(g k) ≥ V'(k)`, so `β f'(k) ≤ 1`.
   But `β f'(k) > β f'(k*) = 1`, a contradiction. Hence `g(k) > k` below `k*`.
4. So the path stays above `min(k₀, k*) > 0`, its limit is a positive fixed
   point with positive consumption, the modified golden rule holds there, and
   uniqueness gives the limit `k*`.
5. Existence of `k*`: `f'(0⁺) = ∞ > 1/β` and `f'(k̄) < f(k̄)/k̄ ≤ 1 < 1/β`, so
   Darboux's theorem gives `f'(k*) = 1/β`.

**Deviation.** As in `Ramsey.lean`, `u` must be finite and continuous at `0`
(bounded DP). So `u'(0⁺) = ∞` is compatible (e.g. `√c`), but log or CRRA
`σ ≥ 1` utility is not.
-/
module

public import EconLean.Macro.Growth.Ramsey
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Darboux

@[expose] public section

namespace Econ

open Filter Topology Set

/-- **Secant bound for concave functions**: for `0 < ε < y/2`, the drop
`f(y) - f(y - ε)` is at most `ε` times the secant slope on `[0, y/2]`. -/
theorem ConcaveOn.sub_le_mul_slope {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {y ε : ℝ} (h0 : (0 : ℝ) ∈ s) (hy : y ∈ s) (hε0 : 0 < ε) (hε : ε < y / 2) :
    f y - f (y - ε) ≤ ε * ((f (y / 2) - f 0) / (y / 2)) := by
  have hoc := hf.1.ordConnected
  have hy0 : 0 < y := by linarith
  have hm : y - ε ∈ s := hoc.out h0 hy ⟨by linarith, by linarith⟩
  have a1 := hf.slope_anti_adjacent (x := y / 2) (y := y - ε) (z := y)
    (hoc.out h0 hy ⟨by linarith, by linarith⟩) hy (by linarith) (by linarith)
  have a2 := hf.slope_anti_adjacent (x := 0) (y := y / 2) (z := y - ε) h0 hm
    (by linarith) (by linarith)
  have e : y - (y - ε) = ε := by ring
  rw [e] at a1
  have := a1.trans (by simpa using a2)
  rw [div_le_iff₀ hε0] at this
  linarith

/-- **Tangent below secant from the left end**: for concave `f` differentiable
at `ε > 0`, `ε f'(ε) ≤ f(ε) - f(0)`. -/
theorem ConcaveOn.mul_deriv_le {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {ε d : ℝ} (h0 : (0 : ℝ) ∈ s) (hε : ε ∈ s) (hε0 : 0 < ε) (hd : HasDerivAt f d ε) :
    ε * d ≤ f ε - f 0 := by
  have := hf.le_slope_of_hasDerivAt h0 hε hε0 hd
  rw [slope_def_field, sub_zero, le_div_iff₀ hε0] at this
  linarith

namespace RCKModel

variable (M : RCKModel)

/-- **Inada conditions** for the RCK model: `u`, `f` differentiable on
`(0, ∞)` with `u'(0⁺) = f'(0⁺) = ∞`. The usual `f'(∞) < 1/β` condition is not
needed: the maximal sustainable stock `f(k̄) ≤ k̄` already gives
`f'(k̄) < f(k̄)/k̄ ≤ 1 < 1/β`. -/
structure Inada : Prop where
  u_diff : ∀ c : ℝ, 0 < c → DifferentiableAt ℝ M.u c
  f_diff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ M.f k
  u_inada : Tendsto (deriv M.u) (𝓝[>] 0) atTop
  f_inada : Tendsto (deriv M.f) (𝓝[>] 0) atTop

/-- The value function extended to `ℝ` is concave on `[0, k̄]`. -/
theorem value_concaveOn : ConcaveOn ℝ M.S (extendS (M.toDynProg.value : M.S → ℝ)) :=
  ConcaveFn.concaveOn (convex_Icc 0 M.kbar) fun x x' z a b ha hb hab hz =>
    (M.toDynProg.value_strictlyConcave (convex_Icc 0 M.kbar) M.convexGraph
      M.strictlyConcaveReturn x x' z a b ha hb hab hz).1

theorem extendS_val (v : M.S → ℝ) (k : M.S) : extendS v (k : ℝ) = v k := by
  simp [extendS, k.2]

/-- `u'(c) > 0` at `c > 0` (strictly increasing and concave). -/
theorem deriv_u_pos {c u' : ℝ} (hc : 0 < c) (hu : HasDerivAt M.u u' c) : 0 < u' := by
  have h := StrictConcaveOn.slope_lt_of_hasDerivAt_left M.u_strictConcave
    (show c ∈ Ici (0 : ℝ) from hc.le) (show c + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
    (by linarith) hu
  have h2 := M.u_strictMono (show c ∈ Ici (0 : ℝ) from hc.le)
    (show c + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith) (by linarith)
  rw [show c + 1 - c = 1 by ring, div_one] at h
  linarith

variable {M}

/-- An event that holds eventually as `x → 0⁺` holds at some `x ∈ (0, b)`. -/
theorem exists_small {p : ℝ → Prop} (h : ∀ᶠ x in 𝓝[>] (0 : ℝ), p x) {b : ℝ} (hb : 0 < b) :
    ∃ x, 0 < x ∧ x < b ∧ p x := by
  obtain ⟨x, hx, hpx⟩ := (h.and (Ioo_mem_nhdsGT hb)).exists
  exact ⟨x, hpx.1, hpx.2, hx⟩

/-- **Positive consumption** (from `u'(0⁺) = ∞`): at every `k > 0`, `g(k) < f(k)`. -/
theorem policy_lt_f (hI : M.Inada) {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k})
    {k : M.S} (hk : 0 < (k : ℝ)) : ((g k : M.S) : ℝ) < M.f k := by
  set P := M.toDynProg
  set V := extendS (P.value : M.S → ℝ)
  have hpol : g k ∈ P.policy k := by rw [hg]; rfl
  obtain ⟨hfeas, hval⟩ := P.mem_policy_iff.1 hpol
  have hfeas' : ((g k : M.S) : ℝ) ≤ M.f k := hfeas
  by_contra hlt
  have hy : ((g k : M.S) : ℝ) = M.f k := le_antisymm hfeas' (not_lt.1 hlt)
  set y : ℝ := ((g k : M.S) : ℝ) with hydef
  have hy0 : 0 < y := by
    rw [hy, ← M.f_zero]; exact M.f_strictMono le_rfl k.2.1 hk
  set L := (V (y / 2) - V 0) / (y / 2)
  obtain ⟨ε, hε0, hεy, hεd⟩ :=
    exists_small ((hI.u_inada.eventually (eventually_gt_atTop (M.β * L))).and
      (eventually_mem_nhdsWithin.mono fun x hx => hI.u_diff x hx)) (b := y / 2) (by linarith)
  -- deviate: save `y - ε` instead of `y`
  have hmem : y - ε ∈ M.S := ⟨by linarith, by linarith [(g k).2.2]⟩
  have hdev := P.bellman_le (x := k) (y := ⟨y - ε, hmem⟩) (show y - ε ≤ M.f k by linarith)
  have hF1 : P.F k ⟨y - ε, hmem⟩ = M.u ε := by
    show M.u (M.f k - (y - ε)) = M.u ε; rw [← hy]; ring_nf
  have hF2 : P.F k (g k) = M.u 0 := by
    show M.u (M.f k - y) = M.u 0; rw [hy, sub_self]
  rw [hF1] at hdev; rw [hF2] at hval
  have hVy : V y = P.value (g k) := M.extendS_val _ (g k)
  have hVd : V (y - ε) = P.value ⟨y - ε, hmem⟩ := M.extendS_val _ ⟨y - ε, hmem⟩
  -- `u(ε) - u(0) ≤ β (V(y) - V(y - ε)) ≤ β L ε`
  have h1 : M.u ε - M.u 0 ≤ M.β * (V y - V (y - ε)) := by
    have hβ : P.β = M.β := rfl
    rw [hVy, hVd, ← hβ]; linarith
  have h2 := ConcaveOn.sub_le_mul_slope M.value_concaveOn (show (0 : ℝ) ∈ M.S from ⟨le_rfl, M.kbar_pos.le⟩)
    (g k).2 hε0 hεy
  have h3 := ConcaveOn.mul_deriv_le M.u_strictConcave.concaveOn (show (0 : ℝ) ∈ Ici 0 from le_rfl)
    (show ε ∈ Ici (0 : ℝ) from hε0.le) hε0 hεd.2.hasDerivAt
  have h2' : V y - V (y - ε) ≤ ε * L := h2
  have h4 : ε * deriv M.u ε ≤ ε * (M.β * L) := by
    have := mul_le_mul_of_nonneg_left h2' M.β_pos.le
    calc ε * deriv M.u ε ≤ M.u ε - M.u 0 := h3
      _ ≤ M.β * (V y - V (y - ε)) := h1
      _ ≤ M.β * (ε * L) := this
      _ = ε * (M.β * L) := by ring
  have := le_of_mul_le_mul_left h4 hε0
  linarith [hεd.1]

/-- **Positive saving** (from `f'(0⁺) = ∞`): at every `k > 0`, `g(k) > 0`. -/
theorem policy_pos (hI : M.Inada) {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k})
    {k : M.S} (hk : 0 < (k : ℝ)) : 0 < ((g k : M.S) : ℝ) := by
  set P := M.toDynProg
  have hβ := M.β_pos
  by_contra hle
  have hy : ((g k : M.S) : ℝ) = 0 := le_antisymm (not_lt.1 hle) (g k).2.1
  set a := M.f k with hadef
  have ha : 0 < a := by rw [hadef, ← M.f_zero]; exact M.f_strictMono le_rfl k.2.1 hk
  -- the state `0` is absorbing: `V(0) = u(0) + β V(0)`
  set z0 : M.S := ⟨0, le_rfl, M.kbar_pos.le⟩
  have hg0 : g z0 = z0 := by
    have h := P.policy_subset z0 (show g z0 ∈ P.policy z0 by rw [hg]; rfl)
    have h' : ((g z0 : M.S) : ℝ) ≤ M.f 0 := h
    rw [M.f_zero] at h'
    exact Subtype.ext (le_antisymm h' (g z0).2.1)
  have hval0 : M.u 0 + M.β * P.value z0 = P.value z0 := by
    have h := (P.mem_policy_iff.1 (show g z0 ∈ P.policy z0 by rw [hg]; rfl)).2
    rw [hg0] at h
    have hF : P.F z0 z0 = M.u 0 := by
      show M.u (M.f 0 - 0) = M.u 0; rw [M.f_zero, sub_zero]
    rw [hF] at h; exact h
  have hgk : g k = z0 := Subtype.ext hy
  have hvalk : M.u a + M.β * P.value z0 = P.value k := by
    have h := (P.mem_policy_iff.1 (show g k ∈ P.policy k by rw [hg]; rfl)).2
    rw [hgk] at h
    have hF : P.F k z0 = M.u a := by show M.u (M.f k - 0) = M.u a; rw [sub_zero]
    rw [hF] at h; exact h
  set Lu := (M.u (a / 2) - M.u 0) / (a / 2)
  set s := (M.u a - M.u 0) / a
  have hs : 0 < s := div_pos (sub_pos.2 (M.u_strictMono (le_refl (0 : ℝ))
    (show a ∈ Ici (0 : ℝ) from ha.le) ha)) ha
  obtain ⟨ε, hε0, hεb, hεd⟩ :=
    exists_small ((hI.f_inada.eventually (eventually_gt_atTop (Lu / (M.β * s)))).and
      (eventually_mem_nhdsWithin.mono fun x hx => hI.f_diff x hx))
      (b := min (k : ℝ) (a / 2)) (lt_min hk (by linarith))
  have hεk : ε < k := lt_of_lt_of_le hεb (min_le_left _ _)
  have hεa : ε < a / 2 := lt_of_lt_of_le hεb (min_le_right _ _)
  set zε : M.S := ⟨ε, hε0.le, by linarith [k.2.2]⟩
  -- deviation: save `ε` instead of `0`
  have hdev := P.bellman_le (x := k) (y := zε) (show ε ≤ M.f k by linarith)
  have hF : P.F k zε = M.u (a - ε) := rfl
  rw [hF] at hdev
  -- from `ε`, saving `0` is feasible: `V(ε) ≥ u(f ε) + β V(0)`
  have hε' := P.bellman_le (x := zε) (y := z0) (show (0 : ℝ) ≤ M.f ε from M.f_nonneg hε0.le)
  have hF' : P.F zε z0 = M.u (M.f ε) := by show M.u (M.f ε - 0) = _; rw [sub_zero]
  rw [hF'] at hε'
  have hβ' : P.β = M.β := rfl
  rw [hβ'] at hdev hε'
  -- `β (u(f ε) - u(0)) ≤ u(a) - u(a - ε)`
  have key : M.β * (M.u (M.f ε) - M.u 0) ≤ M.u a - M.u (a - ε) := by
    have h1 := mul_le_mul_of_nonneg_left hε' hβ.le
    have h2 : M.β * (M.u 0 + M.β * P.value z0) = M.β * P.value z0 := by rw [hval0]
    nlinarith
  have hsec := ConcaveOn.sub_le_mul_slope M.u_strictConcave.concaveOn
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show a ∈ Ici (0 : ℝ) from ha.le) hε0 hεa
  have hfε : 0 < M.f ε := by rw [← M.f_zero]; exact M.f_strictMono le_rfl hε0.le hε0
  have hfεa : M.f ε < a := M.f_strictMono hε0.le k.2.1 hεk
  -- secant slope of `u` from `0`: `u(f ε) - u(0) > s · f(ε)`
  have hslope := M.u_strictConcave.secant_strict_mono (a := 0) (x := M.f ε) (y := a)
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show M.f ε ∈ Ici (0 : ℝ) from hfε.le)
    (show a ∈ Ici (0 : ℝ) from ha.le) hfε.ne' ha.ne' hfεa
  simp only [sub_zero] at hslope
  rw [lt_div_iff₀ hfε] at hslope
  have hfd := ConcaveOn.mul_deriv_le M.f_strictConcave.concaveOn
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show ε ∈ Ici (0 : ℝ) from hε0.le) hε0 hεd.2.hasDerivAt
  rw [M.f_zero, sub_zero] at hfd
  -- `β s ε f'(ε) ≤ ε Lu`
  have hchain : ε * (M.β * s * deriv M.f ε) ≤ ε * Lu := by
    have e1 : M.β * s * (ε * deriv M.f ε) ≤ M.β * s * M.f ε :=
      mul_le_mul_of_nonneg_left hfd (by positivity)
    have e2 : M.β * (s * M.f ε) ≤ M.β * (M.u (M.f ε) - M.u 0) :=
      mul_le_mul_of_nonneg_left hslope.le hβ.le
    have e3 : M.u a - M.u (a - ε) ≤ ε * Lu := hsec
    nlinarith
  have h := le_of_mul_le_mul_left hchain hε0
  have h' := hεd.1
  rw [div_lt_iff₀ (by positivity)] at h'
  linarith

/-- **Envelope condition** (Benveniste–Scheinkman) at an interior `k` with
positive consumption: `V'(k) = u'(c) f'(k)` with `c = f(k) - g(k)`. -/
theorem hasDerivAt_value {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k})
    {k : M.S} (hk0 : 0 < (k : ℝ)) (hkb : (k : ℝ) < M.kbar)
    (hc : ((g k : M.S) : ℝ) < M.f k) {u' f' : ℝ}
    (hu : HasDerivAt M.u u' (M.f k - (g k : M.S))) (hf : HasDerivAt M.f f' k) :
    HasDerivAt (extendS (M.toDynProg.value : M.S → ℝ)) (u' * f') k := by
  set P := M.toDynProg
  have hkint : (k : ℝ) ∈ interior M.S := by rw [interior_Icc]; exact ⟨hk0, hkb⟩
  have hSn : M.S ∈ 𝓝 (k : ℝ) := mem_interior_iff_mem_nhds.1 hkint
  have hy₀ : g k ∈ P.policy k := by rw [hg]; rfl
  have hnear : ∀ᶠ r in 𝓝 (k : ℝ), ((g k : M.S) : ℝ) < M.f r :=
    (M.f_continuous.tendsto _).eventually (lt_mem_nhds hc)
  have hloc : ∀ᶠ r in 𝓝 (k : ℝ), ∀ h : r ∈ M.S, g k ∈ P.Γ ⟨r, h⟩ := by
    filter_upwards [hnear] with r hr h using hr.le
  have hFx : HasDerivAt (extendS fun x => P.F x (g k)) (u' * f') k := by
    have hd : HasDerivAt (M.u ∘ fun r => M.f r - ((g k : M.S) : ℝ)) (u' * f') k :=
      HasDerivAt.comp (h := fun r => M.f r - ((g k : M.S) : ℝ)) (k : ℝ) hu
        (hf.sub_const ((g k : M.S) : ℝ))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hSn] with r hr
    simp only [extendS, hr, dite_true]
    rfl
  exact P.hasDerivAt_value (convex_Icc 0 M.kbar) M.convexGraph M.strictlyConcaveReturn
    hkint hy₀ hloc hFx

/-- **Euler equation** (first-order condition) at an interior choice:
`u'(c) = β V'(g(k))`. -/
theorem euler {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k}) {k : M.S}
    (hy0 : 0 < ((g k : M.S) : ℝ)) (hc : ((g k : M.S) : ℝ) < M.f k) {u' v : ℝ}
    (hu : HasDerivAt M.u u' (M.f k - (g k : M.S)))
    (hV : HasDerivAt (extendS (M.toDynProg.value : M.S → ℝ)) v (g k : M.S)) :
    u' = M.β * v := by
  set P := M.toDynProg
  set y : ℝ := ((g k : M.S) : ℝ) with hydef
  have hyb : y < M.kbar := lt_of_lt_of_le hc (M.f_le k k.2)
  have hyint : y ∈ interior M.S := by rw [interior_Icc]; exact ⟨hy0, hyb⟩
  have hSn : M.S ∈ 𝓝 y := mem_interior_iff_mem_nhds.1 hyint
  have hy₀ : g k ∈ P.policy k := by rw [hg]; rfl
  set φ : ℝ → ℝ := fun r => M.u (M.f k - r) + P.β * extendS (P.value : M.S → ℝ) r
  have hmax : IsLocalMax φ y := by
    have hle : ∀ᶠ r in 𝓝 y, r ≤ M.f k := eventually_le_nhds hc
    filter_upwards [hSn, hle] with r hrS hrf
    have h1 := P.bellman_le (x := k) (y := ⟨r, hrS⟩) hrf
    have h2 := (P.mem_policy_iff.1 hy₀).2
    have hyS : y ∈ M.S := (g k).2
    simp only [φ, extendS, hrS, hyS, dite_true]
    exact h1.trans h2.ge
  have hφ : HasDerivAt φ (u' * (-1) + P.β * v) y := by
    have h1 : HasDerivAt (M.u ∘ fun r => M.f k - r) (u' * (-1)) y :=
      hu.comp y ((hasDerivAt_id' y).const_sub (M.f k))
    exact h1.add (hV.const_mul P.β)
  have h0 := hmax.hasDerivAt_eq_zero hφ
  have hβ : P.β = M.β := rfl
  rw [hβ] at h0; linarith

/-- The modified-golden-rule capital stock has positive consumption:
`β f'(k*) = 1` with `k* > 0` gives `f(k*) > k*/β > k*`. -/
theorem lt_f_of_mgr {kstar fstar : ℝ} (hks : 0 < kstar) (hfs : HasDerivAt M.f fstar kstar)
    (hmgr : M.β * fstar = 1) : kstar < M.f kstar := by
  have h := StrictConcaveOn.hasDerivAt_lt_slope_right M.f_strictConcave
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show kstar ∈ Ici (0 : ℝ) from hks.le) hks hfs
  rw [M.f_zero, sub_zero, sub_zero, lt_div_iff₀ hks] at h
  have hβ1 := M.β_lt_one
  have hβ0 := M.β_pos
  have hf1 : 1 < fstar := by nlinarith
  nlinarith

/-- **Capital rises below `k*`**: if `0 < k < k*`, then `g(k) > k`. -/
theorem lt_policy (hI : M.Inada) {g : M.S → M.S} (hg : ∀ k, M.toDynProg.policy k = {g k})
    {k kstar : M.S} (hk0 : 0 < (k : ℝ)) (hlt : (k : ℝ) < kstar) {fstar : ℝ}
    (hfs : HasDerivAt M.f fstar kstar) (hmgr : M.β * fstar = 1) :
    (k : ℝ) < ((g k : M.S) : ℝ) := by
  by_contra hle
  rw [not_lt] at hle
  have hkb : (k : ℝ) < M.kbar := lt_of_lt_of_le hlt kstar.2.2
  have hy0 := policy_pos hI hg hk0
  have hc := policy_lt_f hI hg hk0
  have hyb : ((g k : M.S) : ℝ) < M.kbar := lt_of_le_of_lt hle hkb
  have hcy := policy_lt_f hI hg (k := g k) hy0
  have hc0 : 0 < M.f k - (g k : M.S) := by linarith
  have hu := (hI.u_diff _ hc0).hasDerivAt
  have hfk := (hI.f_diff _ hk0).hasDerivAt
  have hVk := hasDerivAt_value hg hk0 hkb hc hu hfk
  have hVy := hasDerivAt_value hg (k := g k) hy0 hyb hcy
    (hI.u_diff _ (by linarith)).hasDerivAt (hI.f_diff _ hy0).hasDerivAt
  set vy := deriv M.u (M.f (g k : M.S) - (g (g k) : M.S)) * deriv M.f (g k : M.S)
  have heul := euler hg hy0 hc hu hVy
  set vk := deriv M.u (M.f k - (g k : M.S)) * deriv M.f k
  -- concavity of `V`: `V'(k) ≤ V'(g k)` since `g k ≤ k`
  have hmono : vk ≤ vy := by
    rcases hle.lt_or_eq with h | h
    · have a1 := ConcaveOn.le_slope_of_hasDerivAt M.value_concaveOn (g k).2 k.2 h hVk
      have a2 := ConcaveOn.slope_le_of_hasDerivAt M.value_concaveOn (g k).2 k.2 h hVy
      exact a1.trans a2
    · rw [h] at hVy
      exact (hVk.unique hVy).le
  -- `f'(k) > f'(k*)`
  have hf' : fstar < deriv M.f k := by
    have a := StrictConcaveOn.slope_lt_of_hasDerivAt_left M.f_strictConcave
      (show (k : ℝ) ∈ Ici 0 from k.2.1) (show (kstar : ℝ) ∈ Ici 0 from kstar.2.1) hlt hfk
    have b := StrictConcaveOn.hasDerivAt_lt_slope_right M.f_strictConcave
      (show (k : ℝ) ∈ Ici 0 from k.2.1) (show (kstar : ℝ) ∈ Ici 0 from kstar.2.1) hlt hfs
    linarith
  have hu'pos := M.deriv_u_pos hc0 hu
  set uc := deriv M.u (M.f k - (g k : M.S))
  have h1 : M.β * vk ≤ M.β * vy := mul_le_mul_of_nonneg_left hmono M.β_pos.le
  have h2 : M.β * uc * fstar < M.β * uc * deriv M.f k :=
    mul_lt_mul_of_pos_left hf' (mul_pos M.β_pos hu'pos)
  have h3 : M.β * uc * fstar = uc := by linear_combination uc * hmgr
  have h4 : vk = uc * deriv M.f k := rfl
  rw [h4] at h1
  linarith

/-- **Existence of the modified-golden-rule capital stock** (Darboux):
`f'(0⁺) = ∞ > 1/β > 1 ≥ f(k̄)/k̄ > f'(k̄)`. -/
theorem exists_mgr (hI : M.Inada) :
    ∃ kstar : M.S, 0 < (kstar : ℝ) ∧ (kstar : ℝ) < M.kbar ∧ M.β * deriv M.f kstar = 1 := by
  have hkb := M.kbar_pos
  have hβ0 := M.β_pos
  have hβ1 : 1 < 1 / M.β := one_lt_one_div hβ0 M.β_lt_one
  have hmb : deriv M.f M.kbar < 1 / M.β := by
    have h := StrictConcaveOn.hasDerivAt_lt_slope_right M.f_strictConcave
      (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show M.kbar ∈ Ici (0 : ℝ) from hkb.le) hkb
      (hI.f_diff _ hkb).hasDerivAt
    rw [M.f_zero, sub_zero, sub_zero] at h
    have : M.f M.kbar / M.kbar ≤ 1 :=
      (div_le_one hkb).2 (M.f_le M.kbar ⟨hkb.le, le_rfl⟩)
    linarith
  obtain ⟨a, ha0, hab, hma⟩ :=
    exists_small (hI.f_inada.eventually (eventually_gt_atTop (1 / M.β))) hkb
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt (f := M.f) (f' := deriv M.f)
    hab.le (fun x hx => (hI.f_diff x (by linarith [hx.1])).hasDerivAt.hasDerivWithinAt) hma hmb
  refine ⟨⟨c, by linarith [hc.1], hc.2.le⟩, by simp only; linarith [hc.1], hc.2, ?_⟩
  simp only [hcd]
  field_simp

/-- **Global convergence to the modified golden rule** (SL Thm 6.2 with Inada
conditions; Acemoglu Prop. 6.3). Under the Inada conditions there is a
capital stock `k* ∈ (0, k̄)` with `β f'(k*) = 1` and positive consumption, it
is the only `k ≥ 0` solving the modified golden rule, it is a steady state of
the optimal policy `g`, and from **every** `k₀ > 0` the optimal capital path
`k_{t+1} = g(k_t)` converges **monotonically** to `k*`. -/
theorem global_convergence (hI : M.Inada) :
    ∃ g : M.S → M.S, (∀ k, M.toDynProg.policy k = {g k}) ∧
      ∃ kstar : M.S, 0 < (kstar : ℝ) ∧ (kstar : ℝ) < M.f kstar ∧
        M.β * deriv M.f kstar = 1 ∧
        (∀ k f' : ℝ, 0 ≤ k → HasDerivAt M.f f' k → M.β * f' = 1 → k = kstar) ∧
        g kstar = kstar ∧
        ∀ k₀ : M.S, 0 < (k₀ : ℝ) → (Monotone (planOf g k₀) ∨ Antitone (planOf g k₀)) ∧
          Tendsto (planOf g k₀) atTop (𝓝 kstar) := by
  obtain ⟨g, hg, hgc, hgm⟩ := M.exists_monotone_policy
  obtain ⟨kstar, hks, -, hmgr⟩ := exists_mgr hI
  have hfs := (hI.f_diff _ hks).hasDerivAt
  have hcs := lt_f_of_mgr hks hfs hmgr
  have hfix : g kstar = kstar :=
    M.steady_state_of_modified_golden_rule hg hcs
      (hI.u_diff _ (by linarith)).hasDerivAt hfs hmgr
  refine ⟨g, hg, kstar, hks, hcs, hmgr,
    fun k f' hk hf' he => M.modified_golden_rule_unique hk kstar.2.1 hf' hfs he hmgr, hfix,
    fun k₀ hk₀ => ⟨orbit_monotone_or_antitone hgm k₀, ?_⟩⟩
  set m := min (k₀ : ℝ) kstar
  have hm : 0 < m := lt_min hk₀ hks
  -- the path never falls below `m`
  have hinv : ∀ n, m ≤ ((planOf g k₀ n : M.S) : ℝ) := by
    intro n
    induction n with
    | zero => exact min_le_left _ _
    | succ n ih =>
      rw [planOf_succ]
      set x := planOf g k₀ n
      by_cases hx : (kstar : ℝ) ≤ x
      · have := hgm (show kstar ≤ x from hx)
        rw [hfix] at this
        exact (min_le_right _ _).trans this
      · rw [not_le] at hx
        exact ih.trans (lt_policy hI hg (lt_of_lt_of_le hm ih) hx hfs hmgr).le
  obtain ⟨kinf, hkfix, hlim⟩ := orbit_tendsto_fixedPoint hgm hgc k₀
  have hlimR : Tendsto (fun n => ((planOf g k₀ n : M.S) : ℝ)) atTop (𝓝 (kinf : ℝ)) :=
    (continuous_subtype_val.tendsto _).comp hlim
  have hkinf : m ≤ kinf := ge_of_tendsto hlimR (Eventually.of_forall hinv)
  have hkinf0 : 0 < (kinf : ℝ) := lt_of_lt_of_le hm hkinf
  have hc := policy_lt_f hI hg hkinf0
  rw [hkfix] at hc
  have hmgr' := M.modified_golden_rule hg hkfix hkinf0 hc
    (hI.u_diff _ (by linarith)).hasDerivAt (hI.f_diff _ hkinf0).hasDerivAt
  have heq : (kinf : ℝ) = kstar :=
    M.modified_golden_rule_unique kinf.2.1 kstar.2.1 (hI.f_diff _ hkinf0).hasDerivAt hfs
      hmgr' hmgr
  rwa [Subtype.ext heq] at hlim

end RCKModel

/-! ### Non-vacuity: the `√` economy satisfies the Inada conditions -/

theorem tendsto_deriv_sqrt : Tendsto (deriv Real.sqrt) (𝓝[>] 0) atTop := by
  have heq : (fun x => (2 * Real.sqrt x)⁻¹) =ᶠ[𝓝[>] 0] deriv Real.sqrt := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [(Real.hasDerivAt_sqrt (ne_of_gt hx)).deriv, one_div]
  have h2 : Tendsto (fun x => 2 * Real.sqrt x) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_const.mul Real.continuous_sqrt).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos two_pos (Real.sqrt_pos.2 hx)
  exact (tendsto_inv_nhdsGT_zero.comp h2).congr' heq

theorem RCKModel.sqrtExample_inada : RCKModel.sqrtExample.Inada where
  u_diff := fun _ hc => (Real.hasDerivAt_sqrt hc.ne').differentiableAt
  f_diff := fun _ hk => (Real.hasDerivAt_sqrt hk.ne').differentiableAt
  u_inada := tendsto_deriv_sqrt
  f_inada := tendsto_deriv_sqrt

/-- In the `√` economy (`β = 1/2`), every optimal capital path from `k₀ > 0`
converges to `k* = 1/16`. -/
example : ∃ g : RCKModel.sqrtExample.S → RCKModel.sqrtExample.S,
    (∀ k, RCKModel.sqrtExample.toDynProg.policy k = {g k}) ∧
    ∀ k₀ : RCKModel.sqrtExample.S, 0 < (k₀ : ℝ) →
      Tendsto (fun t => ((planOf g k₀ t : RCKModel.sqrtExample.S) : ℝ)) atTop (𝓝 (1 / 16)) := by
  set M := RCKModel.sqrtExample
  obtain ⟨g, hg, kstar, hks, -, hmgr, -, -, hconv⟩ := M.global_convergence RCKModel.sqrtExample_inada
  have hs : Real.sqrt (1 / 16) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hfd : HasDerivAt M.f (1 / (2 * Real.sqrt (1 / 16))) (1 / 16) :=
    Real.hasDerivAt_sqrt (by norm_num)
  have hmgr2 : M.β * (1 / (2 * Real.sqrt (1 / 16))) = 1 := by
    rw [hs]; norm_num [M, RCKModel.sqrtExample]
  have heq : (kstar : ℝ) = 1 / 16 :=
    M.modified_golden_rule_unique kstar.2.1 (by norm_num)
      (RCKModel.sqrtExample_inada.f_diff _ hks).hasDerivAt hfd hmgr hmgr2
  refine ⟨g, hg, fun k₀ hk₀ => ?_⟩
  rw [← heq]
  exact (continuous_subtype_val.tendsto _).comp (hconv k₀ hk₀).2

end Econ
