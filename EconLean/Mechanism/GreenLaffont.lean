/-
# Green–Laffont: every efficient strategy-proof mechanism is a Groves mechanism

Green and Laffont (1977), "Characterization of satisfactory mechanisms for the revelation of
preferences for public goods", Econometrica; Holmström (1979); MWG Prop. 23.C.5. The setting
is that of `Mechanism/VCG`: agent `i` of type `θᵢ` values outcome `x` at `v i x θᵢ`, utilities
are quasilinear, and `k` is an efficient decision rule.

* `green_laffont`: if every valuation function `X → ℝ` is the valuation of some type of agent
  `i` (an **unrestricted domain**, for every agent), and the mechanism `(k, t)` with efficient
  `k` is strategy-proof, then each transfer has the Groves form
  `tᵢ(θ) = ∑_{j ≠ i} vⱼ(k θ, θⱼ) + hᵢ(θ₋ᵢ)`.
* `green_laffont_groves`: equivalently `t = grovesTransfer v k h` for some `h` ignoring own
  reports; together with `groves_truthful`, the efficient strategy-proof mechanisms on an
  unrestricted domain are exactly the Groves mechanisms.

The statement does not require `X` to be finite, but it only has content when an efficient
rule exists on the whole unrestricted domain, which essentially forces `X` to be finite (with
`X = ℕ` the valuation `n ↦ n` has no maximizer); MWG's setting is a finite `X`. The witness
below has two outcomes. Holmström (1979) extends the result to smoothly
connected domains; only the unrestricted domain is formalized here.
-/
module

public import EconLean.Mechanism.VCG

@[expose] public section

namespace Econ

open Finset Function

variable {I : Type*} [Fintype I] [DecidableEq I] {Θ : I → Type*} {X : Type*}

/-- The mechanism `(k, t)` is **strategy-proof**: truth-telling is a dominant strategy. -/
def IsStrategyProof (v : ∀ i, X → Θ i → ℝ) (k : (∀ i, Θ i) → X) (t : I → (∀ i, Θ i) → ℝ) :
    Prop :=
  ∀ i (θ : ∀ j, Θ j) (θi' : Θ i),
    v i (k (update θ i θi')) (θ i) + t i (update θ i θi') ≤ v i (k θ) (θ i) + t i θ

/-- Every valuation function is the valuation of some type of each agent. -/
def IsUnrestrictedDomain (v : ∀ i, X → Θ i → ℝ) : Prop :=
  ∀ i (f : X → ℝ), ∃ θi : Θ i, ∀ x, v i x θi = f x

/-- The others' total value of `x` at profile `θ`. -/
def othersValue (v : ∀ i, X → Θ i → ℝ) (i : I) (θ : ∀ j, Θ j) (x : X) : ℝ :=
  ∑ j ∈ univ.erase i, v j x (θ j)

lemma othersValue_update (v : ∀ i, X → Θ i → ℝ) (i : I) (θ : ∀ j, Θ j) (θi : Θ i) (x : X) :
    othersValue v i (update θ i θi) x = othersValue v i θ x :=
  sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

lemma total_split (v : ∀ i, X → Θ i → ℝ) (i : I) (θ : ∀ j, Θ j) (x : X) :
    ∑ j, v j x (θ j) = v i x (θ i) + othersValue v i θ x :=
  (add_sum_erase _ (fun j => v j x (θ j)) (mem_univ i)).symm

/-- **Green–Laffont theorem** (unrestricted domain): with an efficient decision rule, a
strategy-proof mechanism's transfer to `i`, minus the others' value of the chosen outcome,
does not depend on `i`'s own report. -/
theorem green_laffont {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X} {t : I → (∀ i, Θ i) → ℝ}
    (hk : IsEfficientRule v k) (hdom : IsUnrestrictedDomain v) (hsp : IsStrategyProof v k t)
    (i : I) : IgnoresOwn i (fun θ => t i θ - othersValue v i θ (k θ)) := by
  classical
  intro θ θi'
  -- `g a` is the transfer net of the others' value when `i` reports `a`
  set W := othersValue v i θ
  set g : Θ i → ℝ := fun a => t i (update θ i a) - W (k (update θ i a))
  have hW : ∀ a x, othersValue v i (update θ i a) x = W x := fun a x => othersValue_update ..
  -- strategy-proofness between two reports `a` (true) and `b`
  have sp : ∀ a b : Θ i, g b - g a ≤ (v i (k (update θ i a)) a + W (k (update θ i a))) -
      (v i (k (update θ i b)) a + W (k (update θ i b))) := by
    intro a b
    have := hsp i (update θ i a) b
    simp only [update_idem, update_self] at this
    simp only [g]
    linarith
  -- efficiency in total-value form
  have eff : ∀ a x, v i x a + W x ≤ v i (k (update θ i a)) a + W (k (update θ i a)) := by
    intro a x
    have := hk (update θ i a) x
    rw [total_split v i, total_split v i, update_self, hW, hW] at this
    exact this
  -- if `a` and `b` lead to the same outcome, `g a = g b`
  have same : ∀ a b, k (update θ i a) = k (update θ i b) → g a = g b := by
    intro a b hab
    have h1 := sp a b
    have h2 := sp b a
    rw [hab] at h1 h2
    linarith
  -- a type of `i` making `x` the unique efficient outcome, `y` a near-tie
  have probe : ∀ (x y : X) (ε : ℝ), 0 < ε → ∃ a : Θ i, k (update θ i a) = x ∧
      v i x a + W x = ε ∧ v i y a + W y = (if y = x then ε else 0) := by
    intro x y ε hε
    obtain ⟨a, ha⟩ := hdom i (fun z => -W z + (if z = x then ε else if z = y then 0 else -1))
    refine ⟨a, ?_, by rw [ha]; simp, by rw [ha]; split_ifs <;> simp_all⟩
    by_contra hne
    have := eff a x
    rw [ha, ha] at this
    simp only [ite_true, neg_add_cancel_comm] at this
    have hval : ∀ z, -W z + (if z = x then ε else if z = y then 0 else -1) + W z ≤ ε := by
      intro z; split_ifs <;> linarith
    split_ifs at this <;> simp_all <;> linarith
  -- main argument: compare `θ i` and `θi'` through probes, up to any `ε > 0`
  have key : ∀ ε, 0 < ε → |g (θ i) - g θi'| ≤ ε := by
    intro ε hε
    set x := k (update θ i (θ i))
    set y := k (update θ i θi')
    obtain ⟨a, hax, hav, hay⟩ := probe x y ε hε
    obtain ⟨b, hby, hbv, hbx⟩ := probe y x ε hε
    have ga := same a (θ i) hax
    have gb := same b θi' hby
    have s1 := sp a b
    have s2 := sp b a
    rw [hax, hby, hav, hay] at s1
    rw [hax, hby, hbv, hbx] at s2
    rw [abs_le]
    constructor <;> split_ifs at s1 s2 <;> linarith
  have : g (θ i) = g θi' := by
    by_contra hne
    have hpos : 0 < |g (θ i) - g θi'| / 2 := by
      have := abs_pos.2 (sub_ne_zero.2 hne); linarith
    have := key _ hpos
    linarith
  simp only [g, update_eq_self] at this
  simp only
  rw [othersValue_update]
  linarith

/-- **Green–Laffont, Groves form**: an efficient strategy-proof mechanism on an unrestricted
domain uses Groves transfers. -/
theorem green_laffont_groves {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X}
    {t : I → (∀ i, Θ i) → ℝ} (hk : IsEfficientRule v k) (hdom : IsUnrestrictedDomain v)
    (hsp : IsStrategyProof v k t) :
    ∃ h : I → (∀ j, Θ j) → ℝ, (∀ i, IgnoresOwn i (h i)) ∧ t = grovesTransfer v k h := by
  refine ⟨fun i θ => t i θ - othersValue v i θ (k θ), fun i => green_laffont hk hdom hsp i, ?_⟩
  funext i θ
  simp only [grovesTransfer, othersValue]
  exact (add_sub_cancel _ _).symm

/-- Conversely, Groves mechanisms are strategy-proof (`groves_truthful`). -/
theorem groves_isStrategyProof {v : ∀ i, X → Θ i → ℝ} {k : (∀ i, Θ i) → X}
    (hk : IsEfficientRule v k) {h : I → (∀ j, Θ j) → ℝ} (hh : ∀ i, IgnoresOwn i (h i)) :
    IsStrategyProof v k (grovesTransfer v k h) :=
  fun i θ θi' => groves_truthful hk hh i θ θi'

/-- Witness: two agents, two outcomes, valuation functions as types (`Θ i = Bool → ℝ`). The
domain is unrestricted, "pick the outcome with the larger total" is efficient, and Groves
transfers with `h = 0` are strategy-proof, so all hypotheses hold together. -/
example : ∃ (k : (Fin 2 → Bool → ℝ) → Bool) (t : Fin 2 → (Fin 2 → Bool → ℝ) → ℝ),
    IsEfficientRule (Θ := fun _ => Bool → ℝ) (fun _ x θi => θi x) k ∧
    IsUnrestrictedDomain (Θ := fun (_ : Fin 2) => Bool → ℝ) (fun _ x θi => θi x) ∧
    IsStrategyProof (Θ := fun _ => Bool → ℝ) (fun _ x θi => θi x) k t := by
  classical
  set k : (Fin 2 → Bool → ℝ) → Bool := fun θ => decide (∑ i, θ i false ≤ ∑ i, θ i true)
  have hk : IsEfficientRule (Θ := fun _ => Bool → ℝ) (fun _ x θi => θi x) k := by
    intro θ x
    simp only [k]
    by_cases h : ∑ i, θ i false ≤ ∑ i, θ i true
    · simp only [h, decide_true]; cases x <;> simp [h]
    · simp only [h, decide_false]; push Not at h; cases x <;> simp [h.le]
  exact ⟨k, grovesTransfer (Θ := fun _ => Bool → ℝ) (fun _ x θi => θi x) k (fun _ _ => 0), hk,
    fun _ f => ⟨f, fun _ => rfl⟩, groves_isStrategyProof hk fun _ _ _ => rfl⟩

end Econ
