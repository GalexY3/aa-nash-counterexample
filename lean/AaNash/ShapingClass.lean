/-
C21 — Which opponent-shaping terms preserve Nash equilibria (preregistered in
formal/PREREG_C21_CLASE_SHAPING_NASH.md, commit cdf4949).

Abstract setting. `V₁`, `V₂` are the spaces of payoff functions of player 1 and player 2 at
fixed interior policies `(p, q)`. `r : V₁ →ₗ R₁` is player 1's incentive (main effect of own
action against `q`), `s : V₂ →ₗ R₂` player 2's incentive (main effect of its action against
`p`). `(p, q)` is an interior Nash equilibrium of the game `(u₁, u₂)` iff `r u₁ = 0` and
`s u₂ = 0`. A local shaping term is a bilinear map `T : V₁ →ₗ V₂ →ₗ W`.

T11: `T` vanishes on every game with an interior Nash at `(p, q)` iff it is incentive-gated:
`T u₁ u₂ = B₁ (r u₁) u₂ + B₂ u₁ (s u₂)` for some bilinear `B₁`, `B₂`.
T13 (contrapositive form): a term that is not incentive-gated is non-zero at some Nash game,
so the shaped update displaces that equilibrium for every `β ≠ 0`.
-/
import Mathlib

namespace AaNash.SC

variable {K : Type*} [Field K]
variable {V₁ V₂ R₁ R₂ W : Type*}
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup R₁] [Module K R₁] [AddCommGroup R₂] [Module K R₂]
  [AddCommGroup W] [Module K W]

/-- Incentive-gated bilinear terms: they read player 1's payoff only through `r` or
player 2's payoff only through `s`. -/
def Gated (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂) (T : V₁ →ₗ[K] V₂ →ₗ[K] W) : Prop :=
  ∃ (B₁ : R₁ →ₗ[K] V₂ →ₗ[K] W) (B₂ : V₁ →ₗ[K] R₂ →ₗ[K] W),
    ∀ u₁ u₂, T u₁ u₂ = B₁ (r u₁) u₂ + B₂ u₁ (s u₂)

/-- `T` vanishes on every game with an interior Nash equilibrium at the fixed profile. -/
def PreservesNash (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂) (T : V₁ →ₗ[K] V₂ →ₗ[K] W) : Prop :=
  ∀ u₁ u₂, r u₁ = 0 → s u₂ = 0 → T u₁ u₂ = 0

/-- Gated terms preserve Nash (T11, ⇐). -/
theorem preservesNash_of_gated (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂)
    (T : V₁ →ₗ[K] V₂ →ₗ[K] W) (h : Gated r s T) : PreservesNash r s T := by
  obtain ⟨B₁, B₂, hT⟩ := h
  intro u₁ u₂ h₁ h₂
  rw [hT, h₁, h₂, map_zero, map_zero, LinearMap.zero_apply, add_zero]

/-- T11, ⇒, given generalized inverses `L₁`, `L₂` (`r ∘ L₁ ∘ r = r`, `s ∘ L₂ ∘ s = s`). -/
theorem gated_of_preservesNash_of_ginv (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂)
    (L₁ : R₁ →ₗ[K] V₁) (L₂ : R₂ →ₗ[K] V₂)
    (hL₁ : ∀ u, r (L₁ (r u)) = r u) (hL₂ : ∀ u, s (L₂ (s u)) = s u)
    (T : V₁ →ₗ[K] V₂ →ₗ[K] W) (h : PreservesNash r s T) : Gated r s T := by
  -- projection of player 1's payoff onto the Nash subspace
  let P₁ : V₁ →ₗ[K] V₁ := LinearMap.id - L₁ ∘ₗ r
  refine ⟨T ∘ₗ L₁, (T ∘ₗ P₁).compl₂ L₂, ?_⟩
  intro u₁ u₂
  have hP₁ : r (P₁ u₁) = 0 := by
    simp [P₁, hL₁]
  have hG₂ : s (u₂ - L₂ (s u₂)) = 0 := by
    rw [map_sub, hL₂, sub_self]
  have hzero : T (P₁ u₁) (u₂ - L₂ (s u₂)) = 0 := h _ _ hP₁ hG₂
  have hsplit₁ : u₁ = P₁ u₁ + L₁ (r u₁) := by
    simp [P₁]
  have hsplit₂ : u₂ = (u₂ - L₂ (s u₂)) + L₂ (s u₂) := by
    abel
  calc T u₁ u₂ = T (P₁ u₁ + L₁ (r u₁)) u₂ := by rw [← hsplit₁]
    _ = T (P₁ u₁) u₂ + T (L₁ (r u₁)) u₂ := by rw [map_add, LinearMap.add_apply]
    _ = T (P₁ u₁) ((u₂ - L₂ (s u₂)) + L₂ (s u₂)) + T (L₁ (r u₁)) u₂ := by
        rw [← hsplit₂]
    _ = T (L₁ (r u₁)) u₂ + T (P₁ u₁) (L₂ (s u₂)) := by
        rw [map_add, hzero, zero_add, add_comm]
    _ = (T ∘ₗ L₁) (r u₁) u₂ + ((T ∘ₗ P₁).compl₂ L₂) u₁ (s u₂) := by
        rfl

/-- Over a field every linear map has a generalized inverse. -/
theorem exists_ginv {V R : Type*} [AddCommGroup V] [Module K V] [AddCommGroup R] [Module K R]
    (f : V →ₗ[K] R) : ∃ g : R →ₗ[K] V, ∀ v, f (g (f v)) = f v := by
  obtain ⟨h, hh⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  refine ⟨h ∘ₗ π, fun v => ?_⟩
  have h1 : π (f v) = f.rangeRestrict v := by
    have := congrArg (fun φ => φ (f.rangeRestrict v)) hπ
    simpa using this
  have h2 : f.rangeRestrict (h (f.rangeRestrict v)) = f.rangeRestrict v := by
    have := DFunLike.congr_fun hh (f.rangeRestrict v)
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at this
  have h3 : ∀ x, f x = (f.rangeRestrict x : R) := fun x => rfl
  rw [LinearMap.comp_apply, h1, h3 (h _), h2, h3 v]

/-- **T11.** A bilinear shaping term preserves every interior Nash equilibrium at the fixed
profile iff it is incentive-gated. -/
theorem preservesNash_iff_gated (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂)
    (T : V₁ →ₗ[K] V₂ →ₗ[K] W) : PreservesNash r s T ↔ Gated r s T := by
  constructor
  · intro h
    obtain ⟨L₁, hL₁⟩ := exists_ginv r
    obtain ⟨L₂, hL₂⟩ := exists_ginv s
    exact gated_of_preservesNash_of_ginv r s L₁ L₂ hL₁ hL₂ T h
  · exact preservesNash_of_gated r s T

/-- **T13 (no free shaping), contrapositive form.** A term that is not incentive-gated is
non-zero at some game with an interior Nash equilibrium at the fixed profile. -/
theorem not_gated_displaces (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂)
    (T : V₁ →ₗ[K] V₂ →ₗ[K] W) (h : ¬ Gated r s T) :
    ∃ u₁ u₂, r u₁ = 0 ∧ s u₂ = 0 ∧ T u₁ u₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h ((preservesNash_iff_gated r s T).1 hcon)

/-- **T13, fixed-point form.** Let `ξ₁` be player 1's naive gradient, which vanishes at an
interior Nash (`r u₁ = 0`). The shaped field `ξ₁ + β T` vanishes at every interior Nash for a
given `β ≠ 0` iff `T` is incentive-gated. -/
theorem shaped_fixed_point_iff_gated (r : V₁ →ₗ[K] R₁) (s : V₂ →ₗ[K] R₂)
    (T : V₁ →ₗ[K] V₂ →ₗ[K] W) (ξ₁ : V₁ → V₂ → W)
    (hξ : ∀ u₁ u₂, r u₁ = 0 → s u₂ = 0 → ξ₁ u₁ u₂ = 0) (β : K) (hβ : β ≠ 0) :
    (∀ u₁ u₂, r u₁ = 0 → s u₂ = 0 → ξ₁ u₁ u₂ + β • T u₁ u₂ = 0) ↔ Gated r s T := by
  rw [← preservesNash_iff_gated]
  constructor
  · intro h u₁ u₂ h₁ h₂
    have := h u₁ u₂ h₁ h₂
    rw [hξ u₁ u₂ h₁ h₂, zero_add] at this
    exact (smul_eq_zero.mp this).resolve_left hβ
  · intro h u₁ u₂ h₁ h₂
    rw [hξ u₁ u₂ h₁ h₂, h u₁ u₂ h₁ h₂, smul_zero, add_zero]

end AaNash.SC
