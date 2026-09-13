module

public import SphereSixComplex.Paper.Topology.EllipticCentralCoverSourceGammaCoordinates
public import SphereSixComplex.Paper.Topology.EllipticCentralProjectionMappingTorusSquare
public import SphereSixComplex.Paper.Topology.EllipticSpecializedNormalizedCoverSweep
public import SphereSixComplex.Paper.Topology.FiniteCoverPerfectPairing

/-!
# Elliptic degree-two generators from orbit sweeps

The fixed-loop sweep and transverse fibre class give integral Wang coordinates on each reduced
mapping torus. Selected covering projections identify these classes with explicit combinations
of source tori, supplying the local generation argument in `EllipticHomologyGenerators`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.EllipticDegreeTwoBasisFromOrbitSweep

open CanonicalProductWangBoundarySlant
open EllipticCentralCoverSourceGammaCoordinates
open EllipticCentralProjectionMappingTorusSquare
open EllipticGammaShearDegreeTwoCoordinates
open EllipticSpecializedNormalizedCoverSweep
open EllipticThreeTorusAdditiveOrbitSweep
open EllipticThreeTorusClutchingDegreeTwo
open EllipticThreeTorusExplicitOrbitSweepHomology
open EllipticThreeTorusRankOneMappingTorusCoordinates
open EllipticThreeTorusWangEndpointCoordinates
open EllipticThreeTorusWangLattice
open FiniteCoverPerfectPairing
open FiniteCyclicMappingTorusWangNaturality
open FiniteCyclicThreeTorusWangNaturality
open FixedLoopSweepWangBoundary
open Geometry Geometry.EllipticFamilySpecialization
open NormalizedAffineMappingTorusCover
open NormalizedFiniteOrderAdditiveCircleSweep
open CyclicMappingTorus.CircleSweep
open EllipticReducedFiberMappingTorus
open EllipticFilling
open PositiveCircleCross
open StandardThreeTorusProductWangBoundary
open StandardTorusHomology
open SphereSixComplex.CircleMappingTorusHomologyBases

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

private abbrev DegreeTwoLattice := Fin 6 → ℤ

private def orderThreeBasisCombination : DegreeTwoLattice :=
  Pi.single 1 1 + 2 • Pi.single 3 1

private def orderFourBasisCombination : DegreeTwoLattice :=
  Pi.single 0 1 + 3 • Pi.single 3 1

private theorem homologyMap_square {X Y Z W : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (f : C(X, Y)) (g : C(Y, W)) (e : C(X, Z)) (h : C(Z, W))
    (hsquare : g.comp f = h.comp e) (z : IntegralSingularHomology 2 X) :
    integralSingularHomologyMap 2 g (integralSingularHomologyMap 2 f z) =
      integralSingularHomologyMap 2 h (integralSingularHomologyMap 2 e z) := by
  calc
    _ = integralSingularHomologyMap 2 (g.comp f) z :=
      integralSingularHomologyMap_comp_wang 2 f g z
    _ = integralSingularHomologyMap 2 (h.comp e) z := congrArg (fun k =>
      integralSingularHomologyMap 2 k z) hsquare
    _ = _ := (integralSingularHomologyMap_comp_wang 2 e h z).symm

private theorem orderThreeGamma_basisCombination :
    integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          orderThreeBasisCombination) =
      -positiveCircleCross (standardThreeTorusCoordinateCircle 1) := by
  apply productHomologyTwo.injective
  change gammaProductHomologyTwo
      (integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          orderThreeBasisCombination)) = _
  rw [orderThreeSourceToGammaProduct_homologyTwo,
    map_neg, productHomologyTwo_positiveCircleCross_coordinateCircle]
  funext i
  fin_cases i <;> simp [orderThreeBasisCombination]

private theorem orderFourGamma_basisCombination :
    integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          orderFourBasisCombination) =
      positiveCircleCross (standardThreeTorusCoordinateCircle 0) := by
  apply productHomologyTwo.injective
  change gammaProductHomologyTwo
      (integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          orderFourBasisCombination)) = _
  rw [orderFourSourceToGammaProduct_homologyTwo,
    productHomologyTwo_positiveCircleCross_coordinateCircle]
  funext i
  fin_cases i <;> simp [orderFourBasisCombination]

private theorem orderThreeGamma_coordinateThree :
    integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          (Pi.single 3 1)) =
      integralSingularHomologyMap 2
        (circleProductFiberInclusion (X := StdTorus 3))
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) := by
  apply productHomologyTwo.injective
  change gammaProductHomologyTwo
      (integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
        ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          (Pi.single 3 1))) = _
  rw [orderThreeSourceToGammaProduct_homologyTwo,
    productHomologyTwo_fiberInclusion,
    standardThreeTorusHomologyTwo.apply_symm_apply]
  funext i
  fin_cases i <;> simp [joinCoordinates]

private theorem orderFourGamma_coordinateThree :
    integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          (Pi.single 3 1)) =
      integralSingularHomologyMap 2
        (circleProductFiberInclusion (X := StdTorus 3))
        (standardThreeTorusHomologyTwo.symm (Pi.single 0 1)) := by
  apply productHomologyTwo.injective
  change gammaProductHomologyTwo
      (integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
        ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          (Pi.single 3 1))) = _
  rw [orderFourSourceToGammaProduct_homologyTwo,
    productHomologyTwo_fiberInclusion,
    standardThreeTorusHomologyTwo.apply_symm_apply]
  funext i
  fin_cases i <;> simp [joinCoordinates]

private theorem orderThree_projection_in_mappingTorus (x : DegreeTwoLattice) :
    integralSingularHomologyMap 2
        (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _))
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderThreeRadialActionData F))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
          orderThreeThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) := by
  apply homologyMap_square
  ext y
  exact congrArg (fun k => k y) (orderThree_coverProjection_square F)

private theorem orderFour_projection_in_mappingTorus (x : DegreeTwoLattice) :
    integralSingularHomologyMap 2
        (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _))
        (integralSingularHomologyMap 2
          (RadialEllipticActionData.centralFiberCoverProjection
            (orderFourRadialActionData F))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) =
      integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
          orderFourThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm x)) := by
  apply homologyMap_square
  ext y
  exact congrArg (fun k => k y) (orderFour_coverProjection_square F)

private def orderThreeSweepGenerator : IntegralSingularHomology 2
    (CircleMappingTorus orderThreeThreeTorusClutching) :=
  -orderThreeFixedLoopSweep

private def orderFourSweepGenerator : IntegralSingularHomology 2
    (CircleMappingTorus orderFourThreeTorusClutching) :=
  orderFourFixedLoopSweep

private def orderThreeFiberGenerator : IntegralSingularHomology 2
    (CircleMappingTorus orderThreeThreeTorusClutching) :=
  (circleMappingTorusWangPresentationOfCover orderThreeThreeTorusClutching 1).inclusion
    (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))

private def orderFourFiberGenerator : IntegralSingularHomology 2
    (CircleMappingTorus orderFourThreeTorusClutching) :=
  (circleMappingTorusWangPresentationOfCover orderFourThreeTorusClutching 1).inclusion
    (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))

private theorem orderThree_cover_basisCombination :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
          orderThreeThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            orderThreeBasisCombination)) = orderThreeSweepGenerator := by
  rw [orderThreeGamma_basisCombination, map_neg]
  change -orderThreeNormalizedCross 1 = _
  rw [orderThreeNormalizedCross_one_eq_fixedLoopSweep]
  rfl

private theorem orderFour_cover_basisCombination :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
          orderFourThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            orderFourBasisCombination)) = 2 • orderFourSweepGenerator := by
  rw [orderFourGamma_basisCombination]
  change orderFourNormalizedCross 0 = _
  rw [orderFourNormalizedCross_zero_eq_two_fixedLoopSweep]
  rfl

private theorem orderThree_cover_coordinateThree :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
          orderThreeThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderThreeSourceToGammaProduct F : C(_, _))
          ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 3 1))) = orderThreeFiberGenerator := by
  rw [orderThreeGamma_coordinateThree]
  convert normalizedFiniteOrderAdditiveCircleSweep_fiberSquare
    orderThreeClutchingAddEquiv orderThreeClutchingAddEquiv_pow _ using 1 <;> rfl

private theorem orderFour_cover_coordinateThree :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
          orderFourThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 3 1))) = orderFourFiberGenerator := by
  rw [orderFourGamma_coordinateThree]
  convert normalizedFiniteOrderAdditiveCircleSweep_fiberSquare
    orderFourClutchingAddEquiv orderFourClutchingAddEquiv_pow _ using 1 <;> rfl

private theorem orderThreeFixedSweep_positiveInvariant :
    orderThreeInvariantsEquivInt
        (orderThreePresentation.totalToInvariants
          orderThreeFixedLoopSweep) = 1 := by
  change orderThreeInvariantEquivInt
    ((invariantsEquivOfConjugacy
      standardThreeTorusHomologyOne.toIntLinearEquiv
      (circleMonodromyDifference orderThreeThreeTorusClutching 1).toIntLinearMap
      orderThreeDegreeOneDifference
      (circleDifference_conjugacy orderThreeThreeTorusClutching 1
        standardThreeTorusHomologyOne.toIntLinearEquiv
        orderThreeClutchingDegreeOneMatrix.mulVecLin
        orderThreeThreeTorusClutching_homologyOne))
      (orderThreePresentation.totalToInvariants
        orderThreeFixedLoopSweep)) = 1
  change standardThreeTorusHomologyOne
    (orderThreePresentation.boundary
      orderThreeFixedLoopSweep) 2 = 1
  have hboundary : orderThreePresentation.boundary
      orderThreeFixedLoopSweep =
        standardThreeTorusCoordinateHomologyClass 2 := by
    change (circleMappingTorusWangPresentationOfCover
      orderThreeThreeTorusClutching 1).boundary
        (fixedLoopSweepClass orderThreeClutchingAddEquiv
          orderThreeFixedCoordinateTwo) = _
    convert fixedLoopSweepClass_boundary orderThreeClutchingAddEquiv
      orderThreeFixedCoordinateTwo using 1 <;> rfl
  rw [hboundary]
  change standardThreeTorusDegreeOneCoordinateHom
    (standardThreeTorusCoordinateHomologyClass 2) 2 = 1
  rw [standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  simp

private theorem orderFourFixedSweep_positiveInvariant :
    orderFourInvariantsEquivInt
        (orderFourPresentation.totalToInvariants
          orderFourFixedLoopSweep) = 1 := by
  change orderFourInvariantEquivInt
    ((invariantsEquivOfConjugacy
      standardThreeTorusHomologyOne.toIntLinearEquiv
      (circleMonodromyDifference orderFourThreeTorusClutching 1).toIntLinearMap
      orderFourDegreeOneDifference
      (circleDifference_conjugacy orderFourThreeTorusClutching 1
        standardThreeTorusHomologyOne.toIntLinearEquiv
        orderFourClutchingDegreeOneMatrix.mulVecLin
        orderFourThreeTorusClutching_homologyOne))
      (orderFourPresentation.totalToInvariants
        orderFourFixedLoopSweep)) = 1
  change standardThreeTorusHomologyOne
    (orderFourPresentation.boundary
      orderFourFixedLoopSweep) 2 = 1
  have hboundary : orderFourPresentation.boundary
      orderFourFixedLoopSweep =
        standardThreeTorusCoordinateHomologyClass 2 := by
    change (circleMappingTorusWangPresentationOfCover
      orderFourThreeTorusClutching 1).boundary
        (fixedLoopSweepClass orderFourClutchingAddEquiv
          orderFourFixedCoordinateTwo) = _
    convert fixedLoopSweepClass_boundary orderFourClutchingAddEquiv
      orderFourFixedCoordinateTwo using 1 <;> rfl
  rw [hboundary]
  change standardThreeTorusDegreeOneCoordinateHom
    (standardThreeTorusCoordinateHomologyClass 2) 2 = 1
  rw [standardThreeTorusDegreeOneCoordinateHom_coordinateClass]
  simp

private theorem orderThreeSweepGenerator_positiveInvariant :
    orderThreeNegatedInvariantsEquivInt
        (orderThreePresentation.totalToInvariants orderThreeSweepGenerator) = 1 := by
  rw [orderThreeNegatedInvariantsEquivInt_apply]
  have hneg : orderThreePresentation.totalToInvariants orderThreeSweepGenerator =
      -(orderThreePresentation.totalToInvariants
        orderThreeFixedLoopSweep) := by
    change orderThreePresentation.totalToInvariants
      (-orderThreeFixedLoopSweep) = _
    exact map_neg orderThreePresentation.totalToInvariants orderThreeFixedLoopSweep
  rw [hneg, map_neg, orderThreeFixedSweep_positiveInvariant]
  norm_num

private theorem orderFourSweepGenerator_positiveInvariant :
    orderFourInvariantsEquivInt
        (orderFourPresentation.totalToInvariants orderFourSweepGenerator) = 1 :=
  orderFourFixedSweep_positiveInvariant

private noncomputable def orderThreeMappingTorusCoordinates :
    IntegralSingularHomology 2 (CircleMappingTorus orderThreeThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  orderThreeNegatedTotalAddEquiv orderThreeSweepGenerator
    orderThreeSweepGenerator_positiveInvariant

private noncomputable def orderFourMappingTorusCoordinates :
    IntegralSingularHomology 2 (CircleMappingTorus orderFourThreeTorusClutching) ≃+
      (Fin 2 → ℤ) :=
  orderFourTotalAddEquiv orderFourSweepGenerator orderFourSweepGenerator_positiveInvariant

end SphereSixComplex.Topology.EllipticDegreeTwoBasisFromOrbitSweep

end

end
