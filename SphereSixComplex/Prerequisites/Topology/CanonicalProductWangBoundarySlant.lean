module

public import SphereSixComplex.Prerequisites.Topology.NormalizedCoverCrossLowOverlapCalculationProof
public import SphereSixComplex.Prerequisites.Topology.StandardThreeTorusProductWangBoundary

/-!
# The circle-slant formula for the product Wang boundary

The explicit fixed-loop cover calculation identifies the canonical product Wang boundary on
positive circle cross-products.  The explicit torus coordinates then determine the boundary on
all of `H₂(S¹ × T³)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.CanonicalProductWangBoundarySlant

open CircleProductIdentityMappingTorus
open FiniteCyclicMappingTorusWangNaturality
open FiniteCyclicThreeTorusWangNaturality
open CyclicMappingTorus
open PositiveCircleCross
open StandardThreeTorusProductWangBoundary
open StandardTorusHomology
open CyclicAngularFundamentalDomain












private theorem gammaSplit_cross_coordinateCircle (i : Fin 3) :
    ((StandardTorusHomology.fourTorusSplit.symm :
        C(UnitAddCircle × StdTorus 3, StdTorus 4)).comp
      (circleProductMap (standardThreeTorusCoordinateCircle i))).comp
        (circleProdStandardCircleHomeomorph.symm :
          C(StdTorus 2, UnitAddCircle × StdTorus 1)) =
      standardFourTorusCoordinateTwoTorus ⟨i.val, by omega⟩ := by
  ext z j
  fin_cases i <;> fin_cases j <;> rfl

@[simp]
public theorem productHomologyTwo_positiveCircleCross_coordinateCircle (i : Fin 3) :
    productHomologyTwo (positiveCircleCross (standardThreeTorusCoordinateCircle i)) =
      Pi.single ⟨i.val, by omega⟩ 1 := by
  change naturalStdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 StandardTorusHomology.fourTorusSplit.symm
        (integralSingularHomologyMap 2
          (circleProductMap (standardThreeTorusCoordinateCircle i))
          (integralSingularHomologyMap 2 circleProdStandardCircleHomeomorph.symm
            standardTwoTorusHomologyGenerator))) = _
  rw [integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang,
    gammaSplit_cross_coordinateCircle]
  change standardFourTorusCanonicalHomologyTwo
      (standardFourTorusCoordinateTwoTorusHomologyClass ⟨i.val, by omega⟩) = _
  exact standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass _








end SphereSixComplex.Topology.CanonicalProductWangBoundarySlant

end

end
