module
public import SphereSixComplex.Paper.Topology.CuspThirdCircle

@[expose] public section
namespace SphereSixComplex.TriangleGroup
open Geometry.CuspRadialClutchingConstruction

public theorem rhoLambda_thirdBasis_gZero_zpow (k : ℤ) :
    rhoLambda (g₀ ^ k) (Pi.single (2 : Fin 4) 1) = Pi.single 2 1 := by
  have hinv : rhoLambda g₀⁻¹ (Pi.single (2 : Fin 4) 1) = Pi.single 2 1 := by
    apply (rhoLambda g₀).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact cuspThirdCoordinate_fixed.symm
  apply zpow_induction_left (P := fun g ↦ rhoLambda g (Pi.single (2 : Fin 4) 1) = Pi.single 2 1)
  · simp
  · intro a ha
    rw [map_mul, LinearEquiv.mul_apply, ha, cuspThirdCoordinate_fixed]
  · intro a ha
    rw [map_mul, LinearEquiv.mul_apply, ha, hinv]

public theorem rhoLambda_thirdBasis_peripheral_zpow (k : ℤ) :
    rhoLambda ((g₁ * g₂) ^ k) (Pi.single (2 : Fin 4) 1) = Pi.single 2 1 := by
  have h : g₁ * g₂ = g₀⁻¹ := eq_inv_of_mul_eq_one_left g₁_mul_g₂_mul_g₀
  rw [h, inv_zpow, ← zpow_neg]
  exact rhoLambda_thirdBasis_gZero_zpow (-k)

end SphereSixComplex.TriangleGroup
