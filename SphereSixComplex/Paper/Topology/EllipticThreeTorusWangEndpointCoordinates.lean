module

public import SphereSixComplex.Paper.Topology.EllipticThreeTorusWangLattice
public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicThreeTorusWangNaturality

/-!
# Endpoint coordinates for the elliptic three-torus Wang sequences
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology.EllipticThreeTorusWangEndpointCoordinates

open EllipticThreeTorusClutchingDegreeTwo
open EllipticThreeTorusWangLattice

public def orderThreeDegreeOneDifference : ThreeLattice →ₗ[ℤ] ThreeLattice :=
  orderThreeClutchingDegreeOneMatrix.mulVecLin - LinearMap.id

public def orderFourDegreeOneDifference : ThreeLattice →ₗ[ℤ] ThreeLattice :=
  orderFourClutchingDegreeOneMatrix.mulVecLin - LinearMap.id

public theorem orderThreeDegreeOneDifference_apply (x : ThreeLattice) :
    orderThreeDegreeOneDifference x = ![-x 0 + x 1, -x 0 - 2 * x 1, x 0] := by
  funext i
  fin_cases i <;>
    simp [orderThreeDegreeOneDifference, orderThreeClutchingDegreeOneMatrix,
      dotProduct, Fin.sum_univ_succ] <;> ring

public theorem orderFourDegreeOneDifference_apply (x : ThreeLattice) :
    orderFourDegreeOneDifference x = ![-x 0 - x 1, x 0 - x 1, x 1] := by
  funext i
  fin_cases i <;>
    simp [orderFourDegreeOneDifference, orderFourClutchingDegreeOneMatrix,
      dotProduct, Fin.sum_univ_succ]
  all_goals ring

public def orderThreeInvariantEquivInt :
    LinearMap.ker orderThreeDegreeOneDifference ≃ₗ[ℤ] ℤ where
  toFun x := x.1 2
  invFun z := ⟨![0, 0, z], by
    apply LinearMap.mem_ker.mpr
    rw [orderThreeDegreeOneDifference_apply]
    funext i
    fin_cases i <;> simp⟩
  left_inv x := by
    apply Subtype.ext
    have hx := LinearMap.mem_ker.mp x.2
    rw [orderThreeDegreeOneDifference_apply] at hx
    have h0 := congrFun hx 2
    have h1 := congrFun hx 0
    funext i
    fin_cases i <;> simp at h0 h1 ⊢ <;> omega
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public def orderFourInvariantEquivInt :
    LinearMap.ker orderFourDegreeOneDifference ≃ₗ[ℤ] ℤ where
  toFun x := x.1 2
  invFun z := ⟨![0, 0, z], by
    apply LinearMap.mem_ker.mpr
    rw [orderFourDegreeOneDifference_apply]
    funext i
    fin_cases i <;> simp⟩
  left_inv x := by
    apply Subtype.ext
    have hx := LinearMap.mem_ker.mp x.2
    rw [orderFourDegreeOneDifference_apply] at hx
    have h1 := congrFun hx 2
    have h0 := congrFun hx 0
    funext i
    fin_cases i <;> simp at h0 h1 ⊢ <;> omega
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

public theorem degreeTwoCoinvariantCoordinate_surjective :
    Function.Surjective degreeTwoCoinvariantCoordinate := by
  intro z
  refine ⟨![z, 0, 0], ?_⟩
  rfl

public noncomputable def orderThreeDegreeTwoCoinvariantsEquivInt :
    (ThreeLattice ⧸ LinearMap.range orderThreeDegreeTwoDifference) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ orderThreeDegreeTwoDifference_range_eq_ker).trans
    (degreeTwoCoinvariantCoordinate.quotKerEquivOfSurjective
      degreeTwoCoinvariantCoordinate_surjective)

public noncomputable def orderFourDegreeTwoCoinvariantsEquivInt :
    (ThreeLattice ⧸ LinearMap.range orderFourDegreeTwoDifference) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ orderFourDegreeTwoDifference_range_eq_ker).trans
    (degreeTwoCoinvariantCoordinate.quotKerEquivOfSurjective
      degreeTwoCoinvariantCoordinate_surjective)

@[simp]
public theorem orderThreeDegreeTwoCoinvariantsEquivInt_mk (x : ThreeLattice) :
    orderThreeDegreeTwoCoinvariantsEquivInt (Submodule.Quotient.mk x) = x 0 :=
  rfl

@[simp]
public theorem orderFourDegreeTwoCoinvariantsEquivInt_mk (x : ThreeLattice) :
    orderFourDegreeTwoCoinvariantsEquivInt (Submodule.Quotient.mk x) = x 0 :=
  rfl








end SphereSixComplex.Topology.EllipticThreeTorusWangEndpointCoordinates

end

end
