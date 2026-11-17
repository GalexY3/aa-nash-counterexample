/-
C06 — Welfare shaping vs incentive shaping (preregistered in formal/PREREG_C06_BIENESTAR_VS_INCENTIVOS.md).

At a single state with finite action sets, own policy `p` and opponent policy `q`:
* the Advantage Alignment term reads only the main effect of MY action on the opponent's payoff
  (`n₂`, the opponent's welfare externality);
* the first-order LOLA shaping term reads only the interaction (`i₂`, how my action changes the
  opponent's incentives).
`J p v = diag(p) v - p (pᵀ v)` is the softmax Jacobian applied to `v` (standard identity; the
derivative itself is not re-derived here).
-/
import Mathlib

open Finset

namespace AaNash.WI

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- Softmax Jacobian applied to a vector: `(diag p - p pᵀ) v`. -/
def Jac (p : α → ℝ) (v : α → ℝ) (c : α) : ℝ := p c * v c - p c * ∑ a, p a * v a

/-- The softmax Jacobian kills constant vectors when `p` sums to one. -/
theorem Jac_const (p : α → ℝ) (hp : ∑ a, p a = 1) (k : ℝ) (c : α) :
    Jac p (fun _ => k) c = 0 := by
  unfold Jac
  rw [show ∑ a, p a * k = (∑ a, p a) * k by rw [Finset.sum_mul], hp]
  ring

theorem Jac_add (p v w : α → ℝ) (c : α) : Jac p (fun a => v a + w a) c = Jac p v c + Jac p w c := by
  unfold Jac
  rw [show ∑ a, p a * (v a + w a) = ∑ a, p a * v a + ∑ a, p a * w a by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun a _ => by ring]
  ring

/-- Components of a Jacobian-image sum to zero. -/
theorem Jac_sum (p : α → ℝ) (hp : ∑ a, p a = 1) (v : α → ℝ) : ∑ c, Jac p v c = 0 := by
  unfold Jac
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp]
  ring

/-- Score of action `a` w.r.t. logit `c` for a softmax policy: `[a = c] - p c`. -/
def sc (p : α → ℝ) (a c : α) : ℝ := (if a = c then 1 else 0) - p c

/-- Advantage Alignment term at one state (component `c`), in expectation form:
`W · E_{a∼p, b∼q}[(u₂(a,b) - V₂) · score(a)]`. -/
def aaTerm (p : α → ℝ) (q : β → ℝ) (W : ℝ) (u₂ : α → β → ℝ) (c : α) : ℝ :=
  W * ∑ a, ∑ b, p a * q b * ((u₂ a b - ∑ a', ∑ b', p a' * q b' * u₂ a' b') * sc p a c)

theorem sum_p_sc (p : α → ℝ) (hp : ∑ a, p a = 1) (c : α) : ∑ a, p a * sc p a c = 0 := by
  unfold sc
  rw [show ∑ a, p a * ((if a = c then (1:ℝ) else 0) - p c)
      = (∑ a, if a = c then p a else 0) - (∑ a, p a) * p c by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring]
  rw [Finset.sum_ite_eq' Finset.univ c, hp]; simp

theorem sum_p_sc_mul (p : α → ℝ) (f : α → ℝ) (c : α) : ∑ a, p a * sc p a c * f a = Jac p f c := by
  unfold sc Jac
  rw [show ∑ a, p a * ((if a = c then (1:ℝ) else 0) - p c) * f a
      = (∑ a, if a = c then p a * f a else 0) - (∑ a, p a * f a) * p c by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring]
  rw [Finset.sum_ite_eq' Finset.univ c]; simp; ring

/-- The AA term equals `W · J_p μ`, with `μ a = E_{b∼q} u₂(a,b)`. -/
theorem aaTerm_eq (p : α → ℝ) (q : β → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (W : ℝ) (u₂ : α → β → ℝ) (c : α) :
    aaTerm p q W u₂ c = W * Jac p (fun a => ∑ b, q b * u₂ a b) c := by
  unfold aaTerm
  congr 1
  generalize hV : (∑ a', ∑ b', p a' * q b' * u₂ a' b') = V
  have h : ∀ a, ∑ b, p a * q b * ((u₂ a b - V) * sc p a c)
      = p a * sc p a c * (∑ b, q b * u₂ a b) - V * (p a * sc p a c) := by
    intro a
    have e1 : ∑ b, p a * q b * ((u₂ a b - V) * sc p a c)
        = p a * sc p a c * (∑ b, q b * u₂ a b) - p a * sc p a c * V * (∑ b, q b) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e1, hq]; ring
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_p_sc p hp c,
    ← sum_p_sc_mul p (fun a => ∑ b, q b * u₂ a b) c]
  ring

/-- **T8 (AA reads only my action's welfare effect on the opponent).** -/
theorem aa_invariant_own_effect (p : α → ℝ) (q : β → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (W : ℝ) (u₂ : α → β → ℝ) (s : β → ℝ) (c : α) :
    aaTerm p q W (fun a b => u₂ a b + s b) c = aaTerm p q W u₂ c := by
  rw [aaTerm_eq p q hp hq, aaTerm_eq p q hp hq]
  have : (fun a => ∑ b, q b * (u₂ a b + s b)) = fun a => (∑ b, q b * u₂ a b) + ∑ b, q b * s b := by
    funext a; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, Jac_add, Jac_const p hp]; ring

theorem aa_invariant_interaction (p : α → ℝ) (q : β → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (W : ℝ) (u₂ i : α → β → ℝ) (hi : ∀ a, ∑ b, q b * i a b = 0) (c : α) :
    aaTerm p q W (fun a b => u₂ a b + i a b) c = aaTerm p q W u₂ c := by
  rw [aaTerm_eq p q hp hq, aaTerm_eq p q hp hq]
  have : (fun a => ∑ b, q b * (u₂ a b + i a b)) = fun a => (∑ b, q b * u₂ a b) + 0 := by
    funext a; rw [← hi a, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [this]; simp

theorem aa_reads_welfare (p : α → ℝ) (q : β → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (W : ℝ) (u₂ : α → β → ℝ) (n : α → ℝ) (c : α) :
    aaTerm p q W (fun a b => u₂ a b + n a) c = aaTerm p q W u₂ c + W * Jac p n c := by
  rw [aaTerm_eq p q hp hq, aaTerm_eq p q hp hq]
  have : (fun a => ∑ b, q b * (u₂ a b + n a)) = fun a => (∑ b, q b * u₂ a b) + n a := by
    funext a
    rw [show ∑ b, q b * (u₂ a b + n a) = ∑ b, q b * u₂ a b + (∑ b, q b) * n a by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring, hq]
    ring
  rw [this, Jac_add]; ring

/-- First-order LOLA shaping term for player 1 (component `c`): `J_p (u₂ (J_q g))`, where `g` is the
gradient of my value w.r.t. the opponent's logits. -/
def lolaTerm [DecidableEq β] (p : α → ℝ) (q : β → ℝ) (u₂ : α → β → ℝ) (g : β → ℝ) (c : α) : ℝ :=
  Jac p (fun a => ∑ b, u₂ a b * Jac q g b) c

/-- **T9 (LOLA reads only the interaction).** -/
theorem lola_invariant_welfare [DecidableEq β] (p : α → ℝ) (q : β → ℝ) (hq : ∑ b, q b = 1)
    (u₂ : α → β → ℝ) (n : α → ℝ) (g : β → ℝ) (c : α) :
    lolaTerm p q (fun a b => u₂ a b + n a) g c = lolaTerm p q u₂ g c := by
  unfold lolaTerm
  congr 1; funext a
  rw [show ∑ b, (u₂ a b + n a) * Jac q g b = ∑ b, u₂ a b * Jac q g b + n a * ∑ b, Jac q g b by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring,
    Jac_sum q hq]
  ring

theorem lola_invariant_own_effect [DecidableEq β] (p : α → ℝ) (q : β → ℝ) (hp : ∑ a, p a = 1)
    (u₂ : α → β → ℝ) (s : β → ℝ) (g : β → ℝ) (c : α) :
    lolaTerm p q (fun a b => u₂ a b + s b) g c = lolaTerm p q u₂ g c := by
  unfold lolaTerm
  have : (fun a => ∑ b, (u₂ a b + s b) * Jac q g b)
      = fun a => (∑ b, u₂ a b * Jac q g b) + ∑ b, s b * Jac q g b := by
    funext a; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, Jac_add, Jac_const p hp]; ring

theorem lola_reads_interaction [DecidableEq β] (p : α → ℝ) (q : β → ℝ) (u₂ i : α → β → ℝ)
    (g : β → ℝ) (c : α) :
    lolaTerm p q (fun a b => u₂ a b + i a b) g c = lolaTerm p q u₂ g c + lolaTerm p q i g c := by
  unfold lolaTerm
  have : (fun a => ∑ b, (u₂ a b + i a b) * Jac q g b)
      = fun a => (∑ b, u₂ a b * Jac q g b) + ∑ b, i a b * Jac q g b := by
    funext a; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, Jac_add]

/-! ### T10: separation in 2×2 games at the uniform profile -/

noncomputable def half : Bool → ℝ := fun _ => 1 / 2
def sgnB (b : Bool) : ℝ := if b then 1 else -1

/-- Gift game: my action `true` gives the opponent 1 (pure welfare externality, no interaction). -/
def gift : Bool → Bool → ℝ := fun a _ => if a then 1 else 0
/-- Incentive game: pure, doubly centered interaction. -/
def incentive : Bool → Bool → ℝ := fun a b => sgnB a * sgnB b
def gTrue : Bool → ℝ := fun b => if b then 1 else 0

theorem separation :
    aaTerm half half 1 gift true = 1 / 4 ∧ (∀ g, lolaTerm half half gift g true = 0) ∧
    aaTerm half half 1 incentive true = 0 ∧ lolaTerm half half incentive gTrue true = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [aaTerm, half, gift, sc] <;> norm_num
  · intro g; simp [lolaTerm, Jac, half, gift] <;> ring
  · simp [aaTerm, half, incentive, sgnB, sc] <;> norm_num
  · simp [lolaTerm, Jac, half, incentive, sgnB, gTrue] <;> norm_num

end AaNash.WI
