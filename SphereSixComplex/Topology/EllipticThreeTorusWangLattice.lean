module

public import SphereSixComplex.Topology.EllipticThreeTorusClutchingDegreeTwo

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

public def orderThreeDegreeOneNorm : ThreeLattice →ₗ[ℤ] ThreeLattice :=
  LinearMap.id + orderThreeClutchingDegreeOneMatrix.mulVecLin +
    orderThreeClutchingDegreeOneMatrix.mulVecLin.comp
      orderThreeClutchingDegreeOneMatrix.mulVecLin

public def orderFourDegreeOneNorm : ThreeLattice →ₗ[ℤ] ThreeLattice :=
  LinearMap.id + orderFourClutchingDegreeOneMatrix.mulVecLin +
    orderFourClutchingDegreeOneMatrix.mulVecLin.comp
      orderFourClutchingDegreeOneMatrix.mulVecLin +
    orderFourClutchingDegreeOneMatrix.mulVecLin.comp
      (orderFourClutchingDegreeOneMatrix.mulVecLin.comp
        orderFourClutchingDegreeOneMatrix.mulVecLin)

public theorem orderThreeDegreeOneNorm_apply (x : ThreeLattice) :
    orderThreeDegreeOneNorm x = ![0, 0, 2 * x 0 + x 1 + 3 * x 2] := by
  funext i
  fin_cases i <;>
    simp [orderThreeDegreeOneNorm, orderThreeClutchingDegreeOneMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

public theorem orderFourDegreeOneNorm_apply (x : ThreeLattice) :
    orderFourDegreeOneNorm x = ![0, 0, 2 * x 0 + 2 * x 1 + 4 * x 2] := by
  funext i
  fin_cases i <;>
    simp [orderFourDegreeOneNorm, orderFourClutchingDegreeOneMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

public theorem orderThreeDegreeOneNorm_surjects_invariantGenerator :
    orderThreeDegreeOneNorm ![0, 1, 0] = ![0, 0, 1] := by decide

public theorem orderFourDegreeOneNorm_image_even (x : ThreeLattice) :
    ∃ n : ℤ, orderFourDegreeOneNorm x = ![0, 0, 2 * n] := by
  refine ⟨x 0 + x 1 + 2 * x 2, ?_⟩
  rw [orderFourDegreeOneNorm_apply]
  funext i
  fin_cases i <;> simp <;> ring

public theorem orderFourDegreeOneNorm_hits_doubleInvariantGenerator :
    orderFourDegreeOneNorm ![1, 0, 0] = ![0, 0, 2] := by decide

end SphereSixComplex.Topology.EllipticThreeTorusWangLattice

end

end
