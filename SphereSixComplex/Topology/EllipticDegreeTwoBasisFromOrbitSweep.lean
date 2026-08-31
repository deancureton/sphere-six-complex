module

public import SphereSixComplex.Topology.EllipticCentralCoverSourceGammaCoordinates
public import SphereSixComplex.Topology.EllipticCentralProjectionMappingTorusSquare
public import SphereSixComplex.Topology.EllipticSpecializedNormalizedCoverSweep
public import SphereSixComplex.Topology.EllipticThreeTorusAdditiveOrbitSweep
public import SphereSixComplex.Topology.EllipticThreeTorusRankOneMappingTorusCoordinates
public import SphereSixComplex.Topology.FiniteCoverPerfectPairing

/-!
# Elliptic degree-two bases from normalized orbit sweeps
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
open NormalizedFiniteOrderAdditiveCircleSweepProof
open PaperAffineCyclicReducedFiberMappingTorus
open PaperEllipticFillingRadialRetraction
open PaperEllipticReducedCentralFiberCoverModels
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

private def orderThreeFibreGenerator : IntegralSingularHomology 2
    (CircleMappingTorus orderThreeThreeTorusClutching) :=
  (circleMappingTorusWangPresentationOfCover orderThreeThreeTorusClutching 1).inclusion
    (standardThreeTorusHomologyTwo.symm (Pi.single 0 1))

private def orderFourFibreGenerator : IntegralSingularHomology 2
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
            (Pi.single 3 1))) = orderThreeFibreGenerator := by
  rw [orderThreeGamma_coordinateThree]
  convert normalizedFiniteOrderAdditiveCircleSweep_fibreSquare
    orderThreeClutchingAddEquiv orderThreeClutchingAddEquiv_pow _ using 1 <;> rfl

private theorem orderFour_cover_coordinateThree :
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
          orderFourThreeTorusClutching_pow)
        (integralSingularHomologyMap 2 (orderFourSourceToGammaProduct F : C(_, _))
          ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 3 1))) = orderFourFibreGenerator := by
  rw [orderFourGamma_coordinateThree]
  convert normalizedFiniteOrderAdditiveCircleSweep_fibreSquare
    orderFourClutchingAddEquiv orderFourClutchingAddEquiv_pow _ using 1 <;> rfl

private theorem orderThreeFixedSweep_positiveInvariant :
    orderThreeInvariantsEquivInt
        (OrderThreePresentation.totalToInvariants
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
      (OrderThreePresentation.totalToInvariants
        orderThreeFixedLoopSweep)) = 1
  change standardThreeTorusHomologyOne
    (OrderThreePresentation.boundary
      orderThreeFixedLoopSweep) 2 = 1
  have hboundary : OrderThreePresentation.boundary
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
        (OrderFourPresentation.totalToInvariants
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
      (OrderFourPresentation.totalToInvariants
        orderFourFixedLoopSweep)) = 1
  change standardThreeTorusHomologyOne
    (OrderFourPresentation.boundary
      orderFourFixedLoopSweep) 2 = 1
  have hboundary : OrderFourPresentation.boundary
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
        (OrderThreePresentation.totalToInvariants orderThreeSweepGenerator) = 1 := by
  rw [orderThreeNegatedInvariantsEquivInt_apply]
  have hneg : OrderThreePresentation.totalToInvariants orderThreeSweepGenerator =
      -(OrderThreePresentation.totalToInvariants
        orderThreeFixedLoopSweep) := by
    change OrderThreePresentation.totalToInvariants
      (-orderThreeFixedLoopSweep) = _
    exact map_neg OrderThreePresentation.totalToInvariants orderThreeFixedLoopSweep
  rw [hneg, map_neg, orderThreeFixedSweep_positiveInvariant]
  norm_num

private theorem orderFourSweepGenerator_positiveInvariant :
    orderFourInvariantsEquivInt
        (OrderFourPresentation.totalToInvariants orderFourSweepGenerator) = 1 :=
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

private noncomputable def orderThreeTargetCoordinates :
    IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F) ≃+ (Fin 2 → ℤ) :=
  (integralSingularHomologyEquiv 2
    (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F)).trans
      orderThreeMappingTorusCoordinates

private noncomputable def orderFourTargetCoordinates :
    IntegralSingularHomology 2 (OrderFourReducedCentralFiber F) ≃+ (Fin 2 → ℤ) :=
  (integralSingularHomologyEquiv 2
    (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F)).trans
      orderFourMappingTorusCoordinates

private theorem orderThreeTargetCoordinates_apply (x) :
    orderThreeTargetCoordinates F x = orderThreeMappingTorusCoordinates
      (integralSingularHomologyMap 2
        (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _)) x) :=
  rfl

private theorem orderFourTargetCoordinates_apply (x) :
    orderFourTargetCoordinates F x = orderFourMappingTorusCoordinates
      (integralSingularHomologyMap 2
        (orderFourReducedCentralFiberCircleMappingTorusHomeomorph F : C(_, _)) x) :=
  rfl

private theorem orderThreeTargetCoordinates_basisCombination :
    orderThreeTargetCoordinates F
        (orderThreeProjectedDegreeTwoGenerator F 1 +
          2 • orderThreeProjectedDegreeTwoGenerator F 3) = ![1, 0] := by
  have hsource :
      (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          orderThreeBasisCombination =
        (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 1 1) +
          2 • (orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 3 1) := by
    rw [orderThreeBasisCombination, map_add, map_nsmul]
  have hprojection := orderThree_projection_in_mappingTorus F orderThreeBasisCombination
  rw [orderThree_cover_basisCombination] at hprojection
  rw [hsource, map_add, map_nsmul, map_add, map_nsmul] at hprojection
  rw [orderThreeTargetCoordinates_apply, map_add, map_nsmul]
  simp only [orderThreeProjectedDegreeTwoGenerator]
  rw [hprojection]
  exact orderThreeNegatedTotalAddEquiv_section _ _

private theorem orderThreeTargetCoordinates_coordinateThree :
    orderThreeTargetCoordinates F (orderThreeProjectedDegreeTwoGenerator F 3) =
      ![0, 1] := by
  have hprojection := orderThree_projection_in_mappingTorus F (Pi.single 3 1)
  rw [orderThree_cover_coordinateThree] at hprojection
  rw [orderThreeTargetCoordinates_apply, orderThreeProjectedDegreeTwoGenerator,
    hprojection]
  exact orderThreeNegatedTotalAddEquiv_fibreCoordinateZero _ _

private theorem orderFourTargetCoordinates_basisCombination :
    orderFourTargetCoordinates F
        (orderFourProjectedDegreeTwoGenerator F 0 +
          3 • orderFourProjectedDegreeTwoGenerator F 3) = ![2, 0] := by
  have hsource :
      (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
          orderFourBasisCombination =
        (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 0 1) +
          3 • (orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm
            (Pi.single 3 1) := by
    rw [orderFourBasisCombination, map_add, map_nsmul]
  have hprojection := orderFour_projection_in_mappingTorus F orderFourBasisCombination
  rw [orderFour_cover_basisCombination] at hprojection
  rw [hsource, map_add, map_nsmul, map_add, map_nsmul] at hprojection
  rw [orderFourTargetCoordinates_apply, map_add, map_nsmul]
  simp only [orderFourProjectedDegreeTwoGenerator]
  rw [hprojection, map_nsmul]
  have hsection : orderFourMappingTorusCoordinates orderFourSweepGenerator = ![1, 0] :=
    orderFourTotalAddEquiv_section _ _
  rw [hsection]
  funext i
  fin_cases i <;> norm_num

private theorem orderFourTargetCoordinates_coordinateThree :
    orderFourTargetCoordinates F (orderFourProjectedDegreeTwoGenerator F 3) =
      ![0, 1] := by
  have hprojection := orderFour_projection_in_mappingTorus F (Pi.single 3 1)
  rw [orderFour_cover_coordinateThree] at hprojection
  rw [orderFourTargetCoordinates_apply, orderFourProjectedDegreeTwoGenerator,
    hprojection]
  exact orderFourTotalAddEquiv_fibreCoordinateZero _ _

/-- The actual elliptic degree-two basis package, derived from the single normalized orbit-sweep
theorem and the explicit three-torus clutching calculations. -/
public theorem actualEllipticDegreeTwoHomologyBasisFiniteData :
    Nonempty (EllipticDegreeTwoHomologyBasisFiniteData F) := by
  let e₃ : IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F) ≃ₗ[ℤ]
      (Fin 2 → ℤ) := (orderThreeTargetCoordinates F).toIntLinearEquiv
  let e₄ : IntegralSingularHomology 2 (OrderFourReducedCentralFiber F) ≃ₗ[ℤ]
      (Fin 2 → ℤ) := (orderFourTargetCoordinates F).toIntLinearEquiv
  have he₃ : (e₃ : _ → _) = orderThreeTargetCoordinates F := by
    funext x
    rfl
  have he₄ : (e₄ : _ → _) = orderFourTargetCoordinates F := by
    funext x
    rfl
  let b₃ : Module.Basis (Fin 2) ℤ
      (IntegralSingularHomology 2 (OrderThreeReducedCentralFiber F)) :=
    Module.Basis.ofEquivFun e₃
  let b₄ : Module.Basis (Fin 2) ℤ
      (IntegralSingularHomology 2 (OrderFourReducedCentralFiber F)) :=
    Module.Basis.ofEquivFun e₄
  refine ⟨{
    orderThreeBasis := b₃
    orderThreeBasis_zero := ?_
    orderThreeBasis_one := ?_
    orderFourBasis := b₄
    orderFourBasis_zero_double := ?_
    orderFourBasis_one := ?_
  }⟩
  · apply e₃.injective
    rw [map_add, map_nsmul, he₃]
    simp only [b₃, Module.Basis.coe_ofEquivFun]
    rw [← he₃, e₃.apply_symm_apply]
    rw [← map_nsmul, ← map_add, he₃,
      orderThreeTargetCoordinates_basisCombination]
    funext i
    fin_cases i <;> simp
  · apply e₃.injective
    rw [he₃, orderThreeTargetCoordinates_coordinateThree]
    simp only [b₃, Module.Basis.coe_ofEquivFun]
    rw [← he₃, e₃.apply_symm_apply]
    funext i
    fin_cases i <;> simp
  · apply e₄.injective
    rw [map_nsmul, map_add, map_nsmul, he₄]
    simp only [b₄, Module.Basis.coe_ofEquivFun]
    rw [← he₄, e₄.apply_symm_apply]
    rw [← map_nsmul, ← map_add, he₄,
      orderFourTargetCoordinates_basisCombination]
    funext i
    fin_cases i <;> simp
  · apply e₄.injective
    rw [he₄, orderFourTargetCoordinates_coordinateThree]
    simp only [b₄, Module.Basis.coe_ofEquivFun]
    rw [← he₄, e₄.apply_symm_apply]
    funext i
    fin_cases i <;> simp

end SphereSixComplex.Topology.EllipticDegreeTwoBasisFromOrbitSweep

end

end
