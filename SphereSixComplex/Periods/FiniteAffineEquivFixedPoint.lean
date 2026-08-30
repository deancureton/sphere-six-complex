module

public import SphereSixComplex.Periods.FiniteGroupCocycleAveraging
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Fixed points of finite affine actions

This file converts a finite group action by affine equivalences into the translation cocycle of
its linear part.  The general averaging theorem then gives a common fixed point.
-/

noncomputable section

namespace groupCohomology

variable {K G E : Type*} [DivisionRing K] [CharZero K] [Group G] [Fintype G]
  [AddCommGroup E] [Module K E]

include K

/-- Every affine action of a finite group on a vector space in characteristic zero has a fixed
point. -/
public theorem finite_affineEquivAction_has_fixedPoint
    (A : G →* (E ≃ᵃ[K] E)) :
    ∃ v : E, ∀ g, A g v = v := by
  let _ : SMul G E := ⟨fun g v ↦ (A g).linear v⟩
  let _ : DistribMulAction G E := {
    one_smul := fun v ↦ by
      change (A 1).linear v = v
      rw [map_one]
      rfl
    mul_smul := fun g h v ↦ by
      change (A (g * h)).linear v = (A g).linear ((A h).linear v)
      rw [map_mul]
      rfl
    smul_zero := fun g ↦ (A g).linear.map_zero
    smul_add := fun g u v ↦ (A g).linear.map_add u v }
  let _ : SMulCommClass G K E := {
    smul_comm := fun g k v ↦ (A g).linear.map_smul k v }
  let c : G → E := fun g ↦ A g 0
  have hc : IsCocycle₁ c := by
    intro g h
    dsimp [c]
    change A (g * h) 0 = (A g).linear (A h 0) + A g 0
    rw [map_mul]
    change A g (A h 0) = _
    have hv := (A g).map_vadd 0 (A h 0)
    simpa using hv
  obtain ⟨v, hv⟩ := finite_affineAction_has_fixedPoint (K := K) c hc
  refine ⟨v, fun g ↦ ?_⟩
  have hmap := (A g).map_vadd 0 v
  change A g v = v
  rw [show A g v = (A g).linear v + A g 0 by simpa using hmap]
  exact hv g

end groupCohomology
