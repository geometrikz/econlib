/-
# The Solow model with labour-augmenting technical progress

Acemoglu §2.7 (Prop. 2.11, balanced growth with Harrod-neutral progress);
Romer §1.2; Barro and Sala-i-Martin §1.3.

**The economics.** Aggregate output is `Y = F(K, A L)`, constant returns to
scale, with labour-augmenting ("Harrod-neutral") technology `A`. Labour grows
at rate `n` and technology at rate `g`:

    L_{t+1} = (1 + n) L_t,   A_{t+1} = (1 + g) A_t,
    K_{t+1} = s Y_t + (1 − δ) K_t.

Writing `F(K, AL) = A L f(K / (A L))` (intensive form, `f(k) = F(k, 1)`), the
capital stock per *effective* worker `k = K / (A L)` obeys

    (1 + n)(1 + g) k_{t+1} = s f(k_t) + (1 − δ) k_t,

which is the basic Solow model with population growth replaced by the
effective growth rate `n_eff = (1 + n)(1 + g) − 1 = n + g + n g`. So `k`
converges to a unique `k*`, and along the way:

* `TechEconomy.effective_eq_path`: `K_t / (A_t L_t)` follows the Solow law of
  motion with `n_eff`.
* `TechEconomy.tendsto_effective`: it converges to `k*` (global stability).
* `TechEconomy.tendsto_detrended_output`: output per worker divided by
  technology, `(Y_t / L_t) / A_t`, converges to `f(k*)`.
* `TechEconomy.balanced_growth`: in steady state, output per worker and
  capital per worker grow at exactly rate `g` (Acemoglu Prop. 2.11).

**Deviation from the textbook.** We take the intensive form `f` as primitive
(as in `Solow.lean`) and define `Y_t = A_t L_t f(K_t / (A_t L_t))` directly.
-/
module

public import EconLean.Macro.Growth.Solow

@[expose] public section

noncomputable section

namespace Econ
namespace Solow

open Set Filter Topology

/-- A Solow economy with population growth `n` and technology growth `g`.
Ranges: `n, g > −1` (so `L` and `A` stay positive), `δ ∈ [0, 1]`, and
`n_eff + δ > 0` where `n_eff = (1 + n)(1 + g) − 1`. -/
structure TechEconomy where
  f : ℝ → ℝ
  s : ℝ
  δ : ℝ
  n : ℝ
  g : ℝ
  hf : NeoclassicalProduction f
  hs_pos : 0 < s
  hs_le_one : s ≤ 1
  hδ_nonneg : 0 ≤ δ
  hδ_le_one : δ ≤ 1
  hn : -1 < n
  hg : -1 < g
  hnδ : 0 < (1 + n) * (1 + g) - 1 + δ

namespace TechEconomy

variable (T : TechEconomy)

/-- The effective population growth rate `n_eff = (1 + n)(1 + g) − 1`. -/
def nEff : ℝ := (1 + T.n) * (1 + T.g) - 1

/-- The associated basic Solow economy for capital per effective worker. -/
def toEconomy : Economy where
  f := T.f
  s := T.s
  δ := T.δ
  n := T.nEff
  hf := T.hf
  hs_pos := T.hs_pos
  hs_le_one := T.hs_le_one
  hδ_nonneg := T.hδ_nonneg
  hδ_le_one := T.hδ_le_one
  hn := by
    unfold nEff
    have h1 : 0 < 1 + T.n := by linarith [T.hn]
    have h2 : 0 < 1 + T.g := by linarith [T.hg]
    nlinarith [mul_pos h1 h2]
  hnδ := T.hnδ

/-- Labour force `L_t = L₀ (1 + n)^t`. -/
def labor (L₀ : ℝ) (t : ℕ) : ℝ := L₀ * (1 + T.n) ^ t

/-- Technology `A_t = A₀ (1 + g)^t`. -/
def tech (A₀ : ℝ) (t : ℕ) : ℝ := A₀ * (1 + T.g) ^ t

/-- Aggregate capital: `K_{t+1} = s Y_t + (1 − δ) K_t` with
`Y_t = A_t L_t f(K_t / (A_t L_t))`. -/
def capital (K₀ A₀ L₀ : ℝ) : ℕ → ℝ
  | 0 => K₀
  | t + 1 =>
    let K := capital K₀ A₀ L₀ t
    let AL := T.tech A₀ t * T.labor L₀ t
    T.s * (AL * T.f (K / AL)) + (1 - T.δ) * K

/-- Aggregate output `Y_t = A_t L_t f(K_t / (A_t L_t))`. -/
def output (K₀ A₀ L₀ : ℝ) (t : ℕ) : ℝ :=
  T.tech A₀ t * T.labor L₀ t *
    T.f (T.capital K₀ A₀ L₀ t / (T.tech A₀ t * T.labor L₀ t))

/-- Capital per effective worker `k_t = K_t / (A_t L_t)`. -/
def effective (K₀ A₀ L₀ : ℝ) (t : ℕ) : ℝ :=
  T.capital K₀ A₀ L₀ t / (T.tech A₀ t * T.labor L₀ t)

theorem tech_pos {A₀ : ℝ} (hA : 0 < A₀) (t : ℕ) : 0 < T.tech A₀ t :=
  mul_pos hA (pow_pos (by linarith [T.hg]) t)

theorem labor_pos {L₀ : ℝ} (hL : 0 < L₀) (t : ℕ) : 0 < T.labor L₀ t :=
  mul_pos hL (pow_pos (by linarith [T.hn]) t)

/-- **Reduction to the basic model.** Capital per effective worker follows
the Solow law of motion with effective population growth `n_eff`. -/
theorem effective_eq_path {K₀ A₀ L₀ : ℝ} (hA : 0 < A₀) (hL : 0 < L₀) (t : ℕ) :
    T.effective K₀ A₀ L₀ t = T.toEconomy.path (K₀ / (A₀ * L₀)) t := by
  induction t with
  | zero => simp [effective, capital, tech, labor]
  | succ t ih =>
    rw [Economy.path_succ, ← ih]
    have hAt := T.tech_pos hA t
    have hLt := T.labor_pos hL t
    have h1 : 0 < 1 + T.n := by linarith [T.hn]
    have h2 : 0 < 1 + T.g := by linarith [T.hg]
    simp only [effective, capital, Economy.next, toEconomy, nEff]
    have htech : T.tech A₀ (t + 1) = T.tech A₀ t * (1 + T.g) := by
      simp [tech, pow_succ, mul_assoc]
    have hlab : T.labor L₀ (t + 1) = T.labor L₀ t * (1 + T.n) := by
      simp [labor, pow_succ, mul_assoc]
    rw [htech, hlab]
    field_simp
    ring

/-- **Global stability with technical progress.** From any `K₀, A₀, L₀ > 0`,
capital per effective worker converges to the steady state `k*` of the
effective-growth Solow model. -/
theorem tendsto_effective {kstar K₀ A₀ L₀ : ℝ} (hs : T.toEconomy.IsSteadyState kstar)
    (hK : 0 < K₀) (hA : 0 < A₀) (hL : 0 < L₀) :
    Tendsto (T.effective K₀ A₀ L₀) atTop (𝓝 kstar) := by
  have := T.toEconomy.tendsto_path hs (k₀ := K₀ / (A₀ * L₀)) (by positivity)
  exact this.congr fun t => (T.effective_eq_path hA hL t).symm

/-- **Detrended output per worker converges:** `(Y_t / L_t) / A_t → f(k*)`.
So output per worker grows asymptotically at the rate of technical progress. -/
theorem tendsto_detrended_output {kstar K₀ A₀ L₀ : ℝ} (hs : T.toEconomy.IsSteadyState kstar)
    (hK : 0 < K₀) (hA : 0 < A₀) (hL : 0 < L₀) :
    Tendsto (fun t => T.output K₀ A₀ L₀ t / T.labor L₀ t / T.tech A₀ t) atTop
      (𝓝 (T.f kstar)) := by
  have hcont : ContinuousAt T.f kstar :=
    (T.hf.continuousOn kstar hs.1).continuousAt (Ioi_mem_nhds hs.1)
  refine (hcont.tendsto.comp (T.tendsto_effective hs hK hA hL)).congr fun t => ?_
  have hAt := T.tech_pos hA t
  have hLt := T.labor_pos hL t
  simp only [Function.comp, output, effective]
  field_simp

/-- **Balanced growth (Acemoglu Prop. 2.11).** If the economy starts at the
steady state (`K₀ / (A₀ L₀) = k*`), it stays there, and output per worker
and capital per worker both grow at exactly rate `g` every period. -/
theorem balanced_growth {kstar K₀ A₀ L₀ : ℝ} (hs : T.toEconomy.IsSteadyState kstar)
    (hA : 0 < A₀) (hL : 0 < L₀) (h0 : K₀ / (A₀ * L₀) = kstar) (t : ℕ) :
    T.effective K₀ A₀ L₀ t = kstar ∧
    T.output K₀ A₀ L₀ (t + 1) / T.labor L₀ (t + 1) =
      (1 + T.g) * (T.output K₀ A₀ L₀ t / T.labor L₀ t) ∧
    T.capital K₀ A₀ L₀ (t + 1) / T.labor L₀ (t + 1) =
      (1 + T.g) * (T.capital K₀ A₀ L₀ t / T.labor L₀ t) := by
  have heff : ∀ t, T.effective K₀ A₀ L₀ t = kstar := by
    intro t
    rw [T.effective_eq_path hA hL, h0]
    induction t with
    | zero => rfl
    | succ t ih => rw [Economy.path_succ, ih, hs.2]
  have hcap : ∀ t, T.capital K₀ A₀ L₀ t = kstar * (T.tech A₀ t * T.labor L₀ t) := by
    intro t
    have := heff t
    unfold effective at this
    have hAt := T.tech_pos hA t
    have hLt := T.labor_pos hL t
    rw [← this]
    field_simp
  have htech : T.tech A₀ (t + 1) = T.tech A₀ t * (1 + T.g) := by
    simp [tech, pow_succ, mul_assoc]
  have hlab : T.labor L₀ (t + 1) = T.labor L₀ t * (1 + T.n) := by
    simp [labor, pow_succ, mul_assoc]
  have hAt := T.tech_pos hA t
  have hLt := T.labor_pos hL t
  have h1 : 0 < 1 + T.n := by linarith [T.hn]
  refine ⟨heff t, ?_, ?_⟩
  · have e1 := heff t
    have e2 := heff (t + 1)
    simp only [effective] at e1 e2
    simp only [output]
    rw [e1, e2, htech, hlab]
    field_simp
  · rw [hcap, hcap, htech, hlab]
    field_simp

end TechEconomy

end Solow
end Econ

end
