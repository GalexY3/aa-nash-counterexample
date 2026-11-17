/-
C05 — Formal verification of the Advantage Alignment / Nash counterexample (V205)
and of a covariance characterization of the joint-advantage shaping term.

Source of the operator: Duque et al., "Advantage Alignment Algorithms", ICLR 2025, Eq. 8
(joint-action advantages, detached; ordinary policy gradient included).
Preregistration: formal/PREREG_C05_FORMALIZACION_AA_NASH.md (commit 97ea340).
-/
import Mathlib

open Finset

namespace AaNash

/-! ## Part I. General finite-action lemmas (T1, T2, T3, T5) -/

section General

variable {α β : Type*} [Fintype α] [Fintype β]

/-- T2 (first form). With independent policies `p` (own) and `q` (opponent), a pre-action
weight `W`, an opponent advantage `A` on joint actions and an own score `S`, the shaping
term only depends on the opponent advantage averaged over the opponent's action,
`μ a = ∑ b, q b * A a b`. -/
theorem shaping_eq_weighted_mu (p : α → ℝ) (q : β → ℝ) (W : ℝ) (A : α → β → ℝ) (S : α → ℝ) :
    ∑ a, ∑ b, p a * q b * W * A a b * S a = W * ∑ a, p a * S a * (∑ b, q b * A a b) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- T2 (covariance form). If the own score has zero mean under `p` (score identity, T1), the
shaping term equals `W` times the covariance, under `p`, between the own score and the
opponent's conditional expected advantage `μ`. Any centring constant `k` (e.g. the mean of
`μ`) can be subtracted. -/
theorem shaping_eq_cov (p : α → ℝ) (q : β → ℝ) (W : ℝ) (A : α → β → ℝ) (S : α → ℝ)
    (hS : ∑ a, p a * S a = 0) (k : ℝ) :
    ∑ a, ∑ b, p a * q b * W * A a b * S a
      = W * ∑ a, p a * S a * ((∑ b, q b * A a b) - k) := by
  rw [shaping_eq_weighted_mu]
  congr 1
  have : ∑ a, p a * S a * ((∑ b, q b * A a b) - k)
      = ∑ a, p a * S a * (∑ b, q b * A a b) - k * ∑ a, p a * S a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [this, hS]
  ring

/-- T3 (marginal correction). Replacing the opponent's joint advantage by its marginal over
the own action, `Abar b = ∑ a', p a' * A a' b`, removes the shaping term for every policy,
provided the own score has zero mean. -/
theorem marginal_shaping_vanishes (p : α → ℝ) (q : β → ℝ) (W : ℝ) (A : α → β → ℝ)
    (S : α → ℝ) (hS : ∑ a, p a * S a = 0) :
    ∑ a, ∑ b, p a * q b * W * (∑ a', p a' * A a' b) * S a = 0 := by
  rw [shaping_eq_weighted_mu]
  have : ∑ a, p a * S a * ∑ b, q b * ∑ a', p a' * A a' b
      = (∑ a, p a * S a) * ∑ b, q b * ∑ a', p a' * A a' b := by
    rw [Finset.sum_mul]
  rw [this, hS]
  ring

/-- T5. With a nonzero pre-action weight the shaping term vanishes if and only if the own
score is uncorrelated with the opponent's conditional expected advantage. Nash conditions
constrain own-action marginal advantages, not this covariance. -/
theorem shaping_zero_iff_cov_zero (p : α → ℝ) (q : β → ℝ) (W : ℝ) (hW : W ≠ 0)
    (A : α → β → ℝ) (S : α → ℝ) (hS : ∑ a, p a * S a = 0) (k : ℝ) :
    ∑ a, ∑ b, p a * q b * W * A a b * S a = 0
      ↔ ∑ a, p a * S a * ((∑ b, q b * A a b) - k) = 0 := by
  rw [shaping_eq_cov p q W A S hS k]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hW
    · exact h
  · intro h
    rw [h, mul_zero]

/-- T6 (pure profiles). If the own policy is a point mass on `a0`, the shaping term vanishes
whatever the opponent's advantages: a degenerate policy has zero covariance. This is why the
published argument covers pure-strategy equilibria. -/
theorem shaping_zero_of_point_mass [DecidableEq α] (a0 : α) (q : β → ℝ) (W : ℝ)
    (A : α → β → ℝ) (S : α → ℝ)
    (hS : ∑ a, (if a = a0 then (1:ℝ) else 0) * S a = 0) :
    ∑ a, ∑ b, (if a = a0 then (1:ℝ) else 0) * q b * W * A a b * S a = 0 := by
  rw [shaping_eq_weighted_mu]
  have h0 : S a0 = 0 := by simpa using hS
  simp [h0]

/-- T7 (repair suggested by the authors in issue #12: average the past self-advantage over the
opponent's action). The averaged past weight `∑_{b'} q' b' * A₁past a' b'` vanishes whenever
the agent is indifferent at that past state (own marginal advantage zero for its past action),
which holds at every state of a completely mixed Markov-perfect equilibrium. The shaping term
then vanishes for every opponent advantage and score. -/
theorem repaired_shaping_vanishes_of_indifference {γ' : Type*} {δ : Type*} [Fintype γ'] [Fintype δ]
    (q' : δ → ℝ) (A₁past : γ' → δ → ℝ) (a' : γ')
    (hind : ∑ b', q' b' * A₁past a' b' = 0) (p : α → ℝ) (q : β → ℝ) (A : α → β → ℝ)
    (S : α → ℝ) :
    ∑ a, ∑ b, p a * q b * (∑ b', q' b' * A₁past a' b') * A a b * S a = 0 := by
  rw [hind]; simp

/-- Softmax policy over a finite action type. -/
noncomputable def softmax (θ : α → ℝ) (a : α) : ℝ :=
  Real.exp (θ a) / ∑ a', Real.exp (θ a')

theorem softmax_sum (θ : α → ℝ) [Nonempty α] : ∑ a, softmax θ a = 1 := by
  unfold softmax
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty))

/-- T1 (general, algebraic part). The softmax score of action `a` with respect to logit `c`
is `[a = c] - π c`; its mean under `π` is zero for every coordinate `c`. -/
theorem softmax_score_mean_zero [DecidableEq α] [Nonempty α] (θ : α → ℝ) (c : α) :
    ∑ a, softmax θ a * ((if a = c then 1 else 0) - softmax θ c) = 0 := by
  have h1 : ∑ a, softmax θ a * ((if a = c then 1 else 0) - softmax θ c)
      = ∑ a, (if a = c then softmax θ a else 0) - (∑ a, softmax θ a) * softmax θ c := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [h1, Finset.sum_ite_eq' Finset.univ c, softmax_sum]
  simp

end General

/-! ## Part II. Bernoulli-logit policies (T1, analytic part) -/

/-- Logistic function. -/
noncomputable def sig (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

theorem sig_zero : sig 0 = 1 / 2 := by
  unfold sig; rw [neg_zero, Real.exp_zero]; norm_num

theorem one_add_exp_neg_pos (x : ℝ) : 0 < 1 + Real.exp (-x) := by
  have := Real.exp_pos (-x); linarith

theorem sig_pos (x : ℝ) : 0 < sig x := by
  unfold sig; exact div_pos one_pos (one_add_exp_neg_pos x)

theorem one_sub_sig (x : ℝ) : 1 - sig x = Real.exp (-x) / (1 + Real.exp (-x)) := by
  unfold sig
  have h := one_add_exp_neg_pos x
  field_simp
  ring

/-- For a positive logit the probability of the `true` action exceeds one half. -/
theorem sig_gt_half {x : ℝ} (hx : 0 < x) : 1 / 2 < sig x := by
  unfold sig
  have he : Real.exp (-x) < 1 := by
    have h0 : Real.exp (-x) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h0
  have h := one_add_exp_neg_pos x
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) h]
  linarith

/-- T1 (analytic). The score of the `true` action, `d/dθ log σ(θ)`, equals `1 - σ(θ)`. -/
theorem hasDerivAt_log_sig (x : ℝ) : HasDerivAt (fun t => Real.log (sig t)) (1 - sig x) x := by
  have hpos : ∀ t, 0 < 1 + Real.exp (-t) := one_add_exp_neg_pos
  have hfun : (fun t => Real.log (sig t)) = fun t => - Real.log (1 + Real.exp (-t)) := by
    funext t
    unfold sig
    rw [one_div, Real.log_inv]
  rw [hfun]
  have hexp : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
    have := (hasDerivAt_neg x).exp
    convert this using 1
    ring
  have hin : HasDerivAt (fun t => 1 + Real.exp (-t)) (-Real.exp (-x)) x := by
    simpa using hexp.const_add 1
  have hlog := (hin.log (ne_of_gt (hpos x))).neg
  rw [one_sub_sig]
  convert hlog using 1
  ring

/-- T1 (analytic). The score of the `false` action, `d/dθ log (1 - σ(θ))`, equals `-σ(θ)`. -/
theorem hasDerivAt_log_one_sub_sig (x : ℝ) :
    HasDerivAt (fun t => Real.log (1 - sig t)) (-sig x) x := by
  have hfun : (fun t => Real.log (1 - sig t)) = fun t => Real.log (sig t) - t := by
    funext t
    rw [one_sub_sig]
    have h := one_add_exp_neg_pos t
    unfold sig
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt h), Real.log_exp, one_div, Real.log_inv]
    ring
  rw [hfun]
  have h := (hasDerivAt_log_sig x).sub (hasDerivAt_id' x)
  convert h using 1
  ring

/-- Probability of a Bernoulli action under logit `θ`. -/
noncomputable def prob (θ : ℝ) (b : Bool) : ℝ := if b then sig θ else 1 - sig θ

/-- Score `d/dθ log prob θ b` (justified by `hasDerivAt_log_sig` and
`hasDerivAt_log_one_sub_sig`). -/
noncomputable def score (θ : ℝ) (b : Bool) : ℝ := if b then 1 - sig θ else - sig θ

/-- T1 (Bernoulli). The score has zero mean. -/
theorem score_mean_zero (θ : ℝ) : ∑ b, prob θ b * score θ b = 0 := by
  simp [Fintype.sum_bool, prob, score]
  ring

theorem prob_sum (θ : ℝ) : ∑ b, prob θ b = 1 := by
  simp [Fintype.sum_bool, prob]

/-! ## Part III. The two-stage counterexample game (T4) -/

/-- Signed action. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Logit indices: 0 = start, 1 = terminal state reached by z = +1, 2 = by z = -1. -/
def st (z : Bool) : Fin 3 := if z then 1 else 2

variable (γ c β α : ℝ)

/-- Stage rewards. Stage 0: player 1 gets z(1+cx), player 2 gets -cxz.
Stage 1 at public state z: player 1 gets cfg, player 2 gets f(z-cg). -/
def r1₀ (x z : Bool) : ℝ := sgn z * (1 + c * sgn x)
def r2₀ (x z : Bool) : ℝ := -c * sgn x * sgn z
def r1₁ (f g : Bool) : ℝ := c * sgn f * sgn g
def r2₁ (z f g : Bool) : ℝ := sgn f * (sgn z - c * sgn g)

variable (θ₁ θ₂ : Fin 3 → ℝ)

/-- Terminal state values. -/
noncomputable def V1₁ (z : Bool) : ℝ :=
  ∑ f, ∑ g, prob (θ₁ (st z)) f * prob (θ₂ (st z)) g * r1₁ c f g
noncomputable def V2₁ (z : Bool) : ℝ :=
  ∑ f, ∑ g, prob (θ₁ (st z)) f * prob (θ₂ (st z)) g * r2₁ c z f g

/-- Start values. -/
noncomputable def V1₀ : ℝ :=
  ∑ x, ∑ z, prob (θ₁ 0) x * prob (θ₂ 0) z * (r1₀ c x z + γ * V1₁ c θ₁ θ₂ z)
noncomputable def V2₀ : ℝ :=
  ∑ x, ∑ z, prob (θ₁ 0) x * prob (θ₂ 0) z * (r2₀ c x z + γ * V2₁ c θ₁ θ₂ z)

/-- Exact joint-action advantages Q - V. -/
noncomputable def A1₀ (x z : Bool) : ℝ := r1₀ c x z + γ * V1₁ c θ₁ θ₂ z - V1₀ γ c θ₁ θ₂
noncomputable def A2₀ (x z : Bool) : ℝ := r2₀ c x z + γ * V2₁ c θ₁ θ₂ z - V2₀ γ c θ₁ θ₂
noncomputable def A1₁ (z f g : Bool) : ℝ := r1₁ c f g - V1₁ c θ₁ θ₂ z
noncomputable def A2₁ (z f g : Bool) : ℝ := r2₁ c z f g - V2₁ c θ₁ θ₂ z

/-- Score vector component `k` of a player whose logit vector is `θ`, acting `b` at the
state with index `s`. -/
noncomputable def sc (θ : Fin 3 → ℝ) (s k : Fin 3) (b : Bool) : ℝ :=
  if s = k then score (θ s) b else 0

/-- Trajectory probability. -/
noncomputable def P (x z f g : Bool) : ℝ :=
  prob (θ₁ 0) x * prob (θ₂ 0) z * prob (θ₁ (st z)) f * prob (θ₂ (st z)) g

/-- Eq. 8 update direction for player 1, component `k`: ordinary policy gradient
`∑_t γ^t A¹_t S¹_t` plus `β ∑_t γ^{t+1} (∑_{k<t} γ^{t-k} A¹_k) A²_t S¹_t`
(the t = 0 shaping term has an empty past). -/
noncomputable def F1 (k : Fin 3) : ℝ :=
  ∑ x, ∑ z, ∑ f, ∑ g, P θ₁ θ₂ x z f g *
    (A1₀ γ c θ₁ θ₂ x z * sc θ₁ 0 k x
      + γ * A1₁ c θ₁ θ₂ z f g * sc θ₁ (st z) k f
      + β * γ ^ 2 * (γ * A1₀ γ c θ₁ θ₂ x z) * A2₁ c θ₁ θ₂ z f g * sc θ₁ (st z) k f)

/-- Same for player 2 (roles of advantages swapped). -/
noncomputable def F2 (k : Fin 3) : ℝ :=
  ∑ x, ∑ z, ∑ f, ∑ g, P θ₁ θ₂ x z f g *
    (A2₀ γ c θ₁ θ₂ x z * sc θ₂ 0 k z
      + γ * A2₁ c θ₁ θ₂ z f g * sc θ₂ (st z) k g
      + β * γ ^ 2 * (γ * A2₀ γ c θ₁ θ₂ x z) * A1₁ c θ₁ θ₂ z f g * sc θ₂ (st z) k g)

/-- Uniform profile π*: all logits zero. -/
def zero3 : Fin 3 → ℝ := fun _ => 0

/-! ### T4a: values vanish at π* -/

theorem V1₁_zero (z : Bool) : V1₁ c zero3 zero3 z = 0 := by
  simp [V1₁, zero3, prob, sig_zero, r1₁, sgn]; ring

theorem V2₁_zero (z : Bool) : V2₁ c zero3 zero3 z = 0 := by
  cases z <;> simp [V2₁, zero3, prob, sig_zero, r2₁, sgn] <;> ring

theorem V1₀_zero : V1₀ γ c zero3 zero3 = 0 := by
  simp [V1₀, V1₁_zero, zero3, prob, sig_zero, r1₀, sgn]; ring

theorem V2₀_zero : V2₀ γ c zero3 zero3 = 0 := by
  simp [V2₀, V2₁_zero, zero3, prob, sig_zero, r2₀, sgn]; ring

/-! ### T4b: π* is a Nash equilibrium (no profitable deterministic history-dependent deviation) -/

/-- Return of player 2 using first action `z0` and terminal action `g x z` (it observes the
whole public history (x, z)), against player 1's policy `θ₁`. -/
noncomputable def R2dev (z0 : Bool) (g : Bool → Bool → Bool) : ℝ :=
  ∑ x, ∑ f, prob (θ₁ 0) x * prob (θ₁ (st z0)) f * (r2₀ c x z0 + γ * r2₁ c z0 f (g x z0))

/-- Return of player 1 using `x0` and terminal action `f x z`, against player 2's `θ₂`. -/
noncomputable def R1dev (x0 : Bool) (f : Bool → Bool → Bool) : ℝ :=
  ∑ z, ∑ g, prob (θ₂ 0) z * prob (θ₂ (st z)) g * (r1₀ c x0 z + γ * r1₁ c (f x0 z) g)

theorem nash_player2 (z0 : Bool) (g : Bool → Bool → Bool) :
    R2dev γ c zero3 z0 g = 0 := by
  cases z0 <;> cases h1 : g true false <;> cases h2 : g false false <;>
    cases h3 : g true true <;> cases h4 : g false true <;>
    simp [R2dev, zero3, prob, sig_zero, r2₀, r2₁, sgn, h1, h2, h3, h4] <;> ring

theorem nash_player1 (x0 : Bool) (f : Bool → Bool → Bool) :
    R1dev γ c zero3 x0 f = 0 := by
  cases x0 <;> cases h1 : f true false <;> cases h2 : f false false <;>
    cases h3 : f true true <;> cases h4 : f false true <;>
    simp [R1dev, zero3, prob, sig_zero, r1₀, r1₁, sgn, h1, h2, h3, h4] <;> ring

/-- The on-policy values at π* are zero (T4a), so no deterministic deviation improves on them. -/
theorem uniform_is_nash :
    (∀ z0 g, R2dev γ c zero3 z0 g ≤ V2₀ γ c zero3 zero3) ∧
    (∀ x0 f, R1dev γ c zero3 x0 f ≤ V1₀ γ c zero3 zero3) := by
  refine ⟨fun z0 g => ?_, fun x0 f => ?_⟩
  · rw [nash_player2, V2₀_zero]
  · rw [nash_player1, V1₀_zero]

/-! ### T4c: the Eq. 8 field at π* -/

theorem F1_at_uniform :
    F1 γ c β zero3 zero3 0 = 0 ∧
    F1 γ c β zero3 zero3 1 = β * γ ^ 3 / 4 ∧
    F1 γ c β zero3 zero3 2 = β * γ ^ 3 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [F1, P, A1₀, A1₁, A2₁, V1₀_zero, V1₁_zero, V2₁_zero, sc, st, zero3, prob, score,
      sig_zero, r1₀, r1₁, r2₁, sgn] <;> ring

theorem F2_at_uniform (k : Fin 3) : F2 γ c β zero3 zero3 k = 0 := by
  fin_cases k <;>
    simp [F2, P, A2₀, A2₁, A1₁, V2₀_zero, V2₁_zero, V1₁_zero, sc, st, zero3, prob, score,
      sig_zero, r2₀, r2₁, r1₁, sgn] <;> ring

/-! ### T4d: after one simultaneous ascent step the profile is not Nash -/

/-- Player 1's logits after the step θ' = 0 + α F1 (player 2 does not move since F2 = 0). -/
noncomputable def θ1step : Fin 3 → ℝ := fun k => if k = 0 then 0 else α * (β * γ ^ 3 / 4)

/-- Player 2's on-policy return after the step (player 2 still uniform). -/
noncomputable def R2onpolicy : ℝ :=
  ∑ x, ∑ z, ∑ f, ∑ g, P (θ1step γ β α) zero3 x z f g * (r2₀ c x z + γ * r2₁ c z f g)

theorem R2onpolicy_zero : R2onpolicy γ c β α = 0 := by
  simp [R2onpolicy, P, θ1step, st, zero3, prob, sig_zero, r2₀, r2₁, sgn]
  ring

/-- The deviation z = +1, then g = -1 at the reached terminal state, earns γ(1+c)m with
m = 2σ(αβγ³/4) - 1. -/
theorem R2dev_after_step :
    R2dev γ c (θ1step γ β α) true (fun _ _ => false)
      = γ * (1 + c) * (2 * sig (α * (β * γ ^ 3 / 4)) - 1) := by
  simp [R2dev, θ1step, st, prob, sig_zero, r2₀, r2₁, sgn]
  ring

/-- **Counterexample (T4d).** For 0 < γ, 0 < c, 0 < α, 0 < β, the uniform Nash profile is
moved by the Advantage Alignment field to a profile where player 2 has a strictly profitable
unilateral deviation: the profile after one step is not a Nash equilibrium. -/
theorem not_nash_after_step (hγ : 0 < γ) (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β) :
    R2onpolicy γ c β α < R2dev γ c (θ1step γ β α) true (fun _ _ => false) := by
  rw [R2onpolicy_zero, R2dev_after_step]
  have hθ : 0 < α * (β * γ ^ 3 / 4) := by positivity
  have hm : 0 < 2 * sig (α * (β * γ ^ 3 / 4)) - 1 := by
    have := sig_gt_half hθ; linarith
  have : 0 < γ * (1 + c) := by positivity
  positivity

/-- The step really is the Eq. 8 ascent from π*: player 1's new logits are α F1 and
player 2's are α F2 = 0. -/
theorem step_is_eq8_ascent (k : Fin 3) :
    θ1step γ β α k = zero3 k + α * F1 γ c β zero3 zero3 k ∧
    zero3 k = zero3 k + α * F2 γ c β zero3 zero3 k := by
  obtain ⟨h0, h1, h2⟩ := F1_at_uniform γ c β
  refine ⟨?_, ?_⟩
  · fin_cases k <;> simp [θ1step, zero3, h0, h1, h2]
  · simp [F2_at_uniform]

end AaNash
