/-
C05c — Advantage Alignment is not invariant to strategic equivalence (machine-checked).

Family of games indexed by `lam`: player 1's first-stage reward is `c·x·z + lam·z`; everything
else as in `AaNash.Basic` (the original game is `lam = 1`). Adding `lam·z`, a term that depends
only on the opponent's action, shifts player 1's return by the same amount for every own policy,
so unilateral deviation gains and equilibrium sets coincide across the family. Yet the Eq. 8 field
at the uniform equilibrium is `(0, βγ³·lam/4, βγ³·lam/4)`.
-/
import AaNash.Basic

open Finset

namespace AaNash

variable (γ c β lam : ℝ) (θ₁ θ₂ : Fin 3 → ℝ)

def r1₀L (x z : Bool) : ℝ := c * sgn x * sgn z + lam * sgn z

theorem r1₀L_one (x z : Bool) : r1₀L c 1 x z = r1₀ c x z := by
  simp [r1₀L, r1₀]; ring

noncomputable def V1₀L : ℝ :=
  ∑ x, ∑ z, prob (θ₁ 0) x * prob (θ₂ 0) z * (r1₀L c lam x z + γ * V1₁ c θ₁ θ₂ z)

noncomputable def A1₀L (x z : Bool) : ℝ :=
  r1₀L c lam x z + γ * V1₁ c θ₁ θ₂ z - V1₀L γ c lam θ₁ θ₂

/-- Eq. 8 direction of player 1 in the `lam` game (same form as `F1`). -/
noncomputable def F1L (k : Fin 3) : ℝ :=
  ∑ x, ∑ z, ∑ f, ∑ g, P θ₁ θ₂ x z f g *
    (A1₀L γ c lam θ₁ θ₂ x z * sc θ₁ 0 k x
      + γ * A1₁ c θ₁ θ₂ z f g * sc θ₁ (st z) k f
      + β * γ ^ 2 * (γ * A1₀L γ c lam θ₁ θ₂ x z) * A2₁ c θ₁ θ₂ z f g * sc θ₁ (st z) k f)

/-- `lam = 1` is exactly the original operator of `AaNash.Basic`. -/
theorem F1L_one (k : Fin 3) : F1L γ c β 1 θ₁ θ₂ k = F1 γ c β θ₁ θ₂ k := by
  have hV : V1₀L γ c 1 θ₁ θ₂ = V1₀ γ c θ₁ θ₂ := by simp [V1₀L, V1₀, r1₀L_one]
  have hA : ∀ x z, A1₀L γ c 1 θ₁ θ₂ x z = A1₀ γ c θ₁ θ₂ x z := by
    intro x z; simp [A1₀L, A1₀, hV, r1₀L_one]
  simp [F1L, F1, hA]

theorem V1₀L_zero : V1₀L γ c lam zero3 zero3 = 0 := by
  simp [V1₀L, V1₁_zero, zero3, prob, sig_zero, r1₀L, sgn]; ring

/-- The field at the uniform equilibrium scales with the nonstrategic component `lam`. -/
theorem F1L_at_uniform :
    F1L γ c β lam zero3 zero3 0 = 0 ∧
    F1L γ c β lam zero3 zero3 1 = β * γ ^ 3 * lam / 4 ∧
    F1L γ c β lam zero3 zero3 2 = β * γ ^ 3 * lam / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [F1L, P, A1₀L, A1₁, A2₁, V1₀L_zero, V1₁_zero, V2₁_zero, sc, st, zero3, prob, score,
      sig_zero, r1₀L, r1₁, r2₁, sgn] <;> ring

/-- Player 1's return from any deterministic history-dependent policy (`x0`, terminal action
`f x z`) against any opponent profile `θ₂` in the `lam` game. -/
noncomputable def R1devL (x0 : Bool) (f : Bool → Bool → Bool) : ℝ :=
  ∑ z, ∑ g, prob (θ₂ 0) z * prob (θ₂ (st z)) g * (r1₀L c lam x0 z + γ * r1₁ c (f x0 z) g)

/-- **Strategic equivalence.** Against any opponent profile, the `lam` term adds the same constant
`lam · E[z]` to every own deterministic policy, so all unilateral deviation gains are independent
of `lam`. (Player 2's rewards do not involve `lam`.) -/
theorem R1devL_shift (x0 : Bool) (f : Bool → Bool → Bool) :
    R1devL γ c lam θ₂ x0 f
      = R1devL γ c 0 θ₂ x0 f + lam * ∑ z, prob (θ₂ 0) z * sgn z := by
  simp [R1devL, r1₀L, prob, sgn]
  ring

theorem deviation_gain_independent_of_lam (x0 x0' : Bool) (f f' : Bool → Bool → Bool) :
    R1devL γ c lam θ₂ x0 f - R1devL γ c lam θ₂ x0' f'
      = R1devL γ c 0 θ₂ x0 f - R1devL γ c 0 θ₂ x0' f' := by
  rw [R1devL_shift, R1devL_shift γ c lam θ₂ x0' f']; ring

/-- **Headline.** For `β, γ > 0`, two strategically equivalent games (`lam = 0` and any
`lam ≠ 0`) with the same deviation gains and the same uniform equilibrium receive different
Advantage Alignment updates at that equilibrium: zero in one, nonzero in the other. -/
theorem aa_not_invariant_to_strategic_equivalence (hβ : 0 < β) (hγ : 0 < γ) (hlam : lam ≠ 0) :
    F1L γ c β 0 zero3 zero3 1 = 0 ∧ F1L γ c β lam zero3 zero3 1 ≠ 0 := by
  obtain ⟨_, h1, _⟩ := F1L_at_uniform γ c β lam
  obtain ⟨_, h1', _⟩ := F1L_at_uniform γ c β 0
  refine ⟨by rw [h1']; ring, ?_⟩
  rw [h1]
  have : 0 < β * γ ^ 3 / 4 := by positivity
  intro h
  have : β * γ ^ 3 * lam / 4 = (β * γ ^ 3 / 4) * lam := by ring
  rw [this] at h
  rcases mul_eq_zero.mp h with h | h <;> [linarith; exact hlam h]

end AaNash
