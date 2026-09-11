module

public import SphereSixComplex.Paper.Topology.EllipticThreeTorusClutchingDegreeTwo

/-!
# Integral Wang lattices of the elliptic three-torus clutchings
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology.EllipticThreeTorusWangLattice

open EllipticThreeTorusClutchingDegreeTwo

public abbrev ThreeLattice := Fin 3 → ℤ

public def orderThreeDegreeTwoDifference : ThreeLattice →ₗ[ℤ] ThreeLattice :=
  orderThreeClutchingDegreeTwoMatrix.mulVecLin - LinearMap.id

public def orderFourDegreeTwoDifference : ThreeLattice →ₗ[ℤ] ThreeLattice :=
  orderFourClutchingDegreeTwoMatrix.mulVecLin - LinearMap.id

public theorem orderThreeDegreeTwoDifference_apply (x : ThreeLattice) :
    orderThreeDegreeTwoDifference x =
      ![0, -x 0 - x 1 + x 2, x 0 - x 1 - 2 * x 2] := by
  funext i
  fin_cases i <;>
    simp [orderThreeDegreeTwoDifference, orderThreeClutchingDegreeTwoMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

public theorem orderFourDegreeTwoDifference_apply (x : ThreeLattice) :
    orderFourDegreeTwoDifference x = ![0, -x 1 - x 2, x 0 + x 1 - x 2] := by
  funext i
  fin_cases i <;>
    simp [orderFourDegreeTwoDifference, orderFourClutchingDegreeTwoMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

public def degreeTwoCoinvariantCoordinate : ThreeLattice →ₗ[ℤ] ℤ :=
  LinearMap.proj 0

public theorem orderThreeDegreeTwoDifference_range_eq_ker :
    LinearMap.range orderThreeDegreeTwoDifference =
      LinearMap.ker degreeTwoCoinvariantCoordinate := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [orderThreeDegreeTwoDifference_apply, degreeTwoCoinvariantCoordinate]
  · intro hx
    have hx0 : x 0 = 0 := LinearMap.mem_ker.mp hx
    refine ⟨![-x 2 - 2 * x 1, 0, -x 2 - x 1], ?_⟩
    rw [orderThreeDegreeTwoDifference_apply]
    funext i
    fin_cases i <;> simp [hx0] <;> ring

public theorem orderFourDegreeTwoDifference_range_eq_ker :
    LinearMap.range orderFourDegreeTwoDifference =
      LinearMap.ker degreeTwoCoinvariantCoordinate := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [orderFourDegreeTwoDifference_apply, degreeTwoCoinvariantCoordinate]
  · intro hx
    have hx0 : x 0 = 0 := LinearMap.mem_ker.mp hx
    refine ⟨![x 2 + x 1, -x 1, 0], ?_⟩
    rw [orderFourDegreeTwoDifference_apply]
    funext i
    fin_cases i <;> simp [hx0]








end SphereSixComplex.Topology.EllipticThreeTorusWangLattice

end

end
