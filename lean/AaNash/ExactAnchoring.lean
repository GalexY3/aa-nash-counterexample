/-
C21b — Exact anchoring (formal/INFORME_C21B_DESPLAZAMIENTO_DEL_RIVAL.md).

Stage game, finite actions, softmax policies. Player 1 runs any shaped update
`F₁ = J_p (u₁ q) + β T(p, q)`; player 2 is naive: `F₂ = J_q (u₂ᵀ p)`.
With `q` interior, player 2's fixed-point condition `F₂ = 0` says only that `u₂ᵀ p` is
constant over player 2's actions. It does not involve `q`, `β` or `T`.
Hence, whenever that indifference condition pins down `p` uniquely on the simplex,
every fixed point of the shaped dynamics, for every `β` and every shaping term, has the
same `p`: the shaper cannot move its own equilibrium strategy; only the rival's can move.
-/
import Mathlib
import AaNash.WelfareIncentive

open Finset

namespace AaNash.EA

open AaNash.WI

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- Player 2's expected payoff for each of its actions, against player 1's policy `p`. -/
def v₂ (u₂ : α → β → ℝ) (p : α → ℝ) (b : β) : ℝ := ∑ a, p a * u₂ a b

/-- `p` makes player 2 indifferent among all its actions. -/
def Indifferent (u₂ : α → β → ℝ) (p : α → ℝ) : Prop := ∃ k : ℝ, ∀ b, v₂ u₂ p b = k

/-- With an interior `q`, the softmax Jacobian kills `v` iff `v` is constant. -/
theorem jac_eq_zero_iff_const (q : β → ℝ) (hq : ∑ b, q b = 1) (hpos : ∀ b, 0 < q b)
    (v : β → ℝ) : (∀ c, Jac q v c = 0) ↔ ∃ k : ℝ, ∀ b, v b = k := by
  constructor
  · intro h
    refine ⟨∑ b, q b * v b, fun c => ?_⟩
    have hc := h c
    unfold Jac at hc
    have hne : q c ≠ 0 := (hpos c).ne'
    have : q c * (v c - ∑ b, q b * v b) = 0 := by rw [mul_sub]; exact hc
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hne
    · linarith
  · rintro ⟨k, hk⟩ c
    have hv : v = fun _ => k := funext hk
    rw [hv]
    exact Jac_const q hq k c

/-- Player 2's naive fixed-point condition at an interior `q` is exactly indifference,
whatever `q` is. -/
theorem rival_fixed_iff_indifferent (u₂ : α → β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hq : ∑ b, q b = 1) (hpos : ∀ b, 0 < q b) :
    (∀ c, Jac q (v₂ u₂ p) c = 0) ↔ Indifferent u₂ p :=
  jac_eq_zero_iff_const q hq hpos (v₂ u₂ p)

/-- **Exact anchoring.** Suppose indifference of player 2 determines `p` uniquely on the
simplex. Take any two fixed points `(p, q)` and `(p', q')` of shaped dynamics, with any
shaping strengths and any shaping terms for player 1 (only player 2's naive condition and
interiority are used). Then `p = p'`. -/
theorem shaper_strategy_anchored (u₂ : α → β → ℝ)
    (huniq : ∀ p p' : α → ℝ, (∀ a, 0 ≤ p a) → ∑ a, p a = 1 → (∀ a, 0 ≤ p' a) →
      ∑ a, p' a = 1 → Indifferent u₂ p → Indifferent u₂ p' → p = p')
    (p p' : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hp0' : ∀ a, 0 ≤ p' a) (hp1' : ∑ a, p' a = 1)
    (q q' : β → ℝ) (hq : ∑ b, q b = 1) (hqpos : ∀ b, 0 < q b)
    (hq' : ∑ b, q' b = 1) (hqpos' : ∀ b, 0 < q' b)
    (hfix : ∀ c, Jac q (v₂ u₂ p) c = 0) (hfix' : ∀ c, Jac q' (v₂ u₂ p') c = 0) :
    p = p' :=
  huniq p p' hp0 hp1 hp0' hp1'
    ((rival_fixed_iff_indifferent u₂ p q hq hqpos).1 hfix)
    ((rival_fixed_iff_indifferent u₂ p' q' hq' hqpos').1 hfix')

/-- **Corollary (shaping moves only the rival).** Let `F₁ β p q` be player 1's shaped field,
for an arbitrary family indexed by the shaping strength `β`. Under the uniqueness hypothesis,
the player-1 component of every interior fixed point is the same for every `β`. -/
theorem shaping_cannot_move_shaper (u₂ : α → β → ℝ)
    (huniq : ∀ p p' : α → ℝ, (∀ a, 0 ≤ p a) → ∑ a, p a = 1 → (∀ a, 0 ≤ p' a) →
      ∑ a, p' a = 1 → Indifferent u₂ p → Indifferent u₂ p' → p = p')
    (F₁ : ℝ → (α → ℝ) → (β → ℝ) → α → ℝ)
    (β₀ β₁ : ℝ) (p₀ p₁ : α → ℝ) (q₀ q₁ : β → ℝ)
    (hp₀ : (∀ a, 0 ≤ p₀ a) ∧ ∑ a, p₀ a = 1) (hp₁ : (∀ a, 0 ≤ p₁ a) ∧ ∑ a, p₁ a = 1)
    (hq₀ : ∑ b, q₀ b = 1 ∧ ∀ b, 0 < q₀ b) (hq₁ : ∑ b, q₁ b = 1 ∧ ∀ b, 0 < q₁ b)
    (_hF₀ : ∀ c, F₁ β₀ p₀ q₀ c = 0) (_hF₁ : ∀ c, F₁ β₁ p₁ q₁ c = 0)
    (h₂₀ : ∀ c, Jac q₀ (v₂ u₂ p₀) c = 0) (h₂₁ : ∀ c, Jac q₁ (v₂ u₂ p₁) c = 0) :
    p₀ = p₁ :=
  shaper_strategy_anchored u₂ huniq p₀ p₁ hp₀.1 hp₀.2 hp₁.1 hp₁.2 q₀ q₁ hq₀.1 hq₀.2
    hq₁.1 hq₁.2 h₂₀ h₂₁

end AaNash.EA
