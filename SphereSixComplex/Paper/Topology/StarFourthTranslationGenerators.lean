module
public import SphereSixComplex.Paper.Topology.StarFourthTranslation
public import SphereSixComplex.Paper.Topology.EllipticHomologyGenerators
public import SphereSixComplex.Paper.Topology.EllipticHomologyGeneration
public import SphereSixComplex.Paper.Topology.EllipticHomologyGeneratorAlignment
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthSideInclusion
public import SphereSixComplex.Prerequisites.Topology.CircleActionHomology
import all SphereSixComplex.Prerequisites.Topology.NormalizedCoverCrossLowOverlapCalculationProof
/-! The fixed-loop tori in the two reduced elliptic fibers are actual fourth-translation
orbits. Their images in the star therefore vanish in second homology. -/

@[expose] public section
noncomputable section
open Set Topology AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.EllipticFilling SphereSixComplex.EllipticReducedFiberMappingTorus
open SphereSixComplex.Periods ComplexTorus AnalyticTorusFamily TorusFamily GlobalTorusFamily
open EllipticSpecializedNormalizedCoverSweep EllipticThreeTorusAdditiveOrbitSweep
open FixedLoopSweepWangBoundary EllipticCentralProjectionMappingTorusSquare
open SphereSixComplex.CyclicMappingTorus.CircleSweep
open SphereSixComplex.CyclicAngularFundamentalDomain
open EllipticFamilySpecialization
open NormalizedAffineMappingTorusCover CircleProductIdentityMappingTorus

public theorem orderThree_gamma_fourth (A : AnalyticData) (z : UnitAddCircle)
    (q : AdditiveTorus
      (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne).1) :
    orderThreeGammaNormalFormHomeomorph A.periods
      (fourthPeriodCircle
        (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne) z + q) =
    ((orderThreeGammaNormalFormHomeomorph A.periods q).1,
      Pi.single 2 z + (orderThreeGammaNormalFormHomeomorph A.periods q).2) := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  induction q using Quotient.inductionOn with
  | _ v =>
    rw [fourthPeriodCircle_real]
    let p := parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zOne
    change orderThreeStandardGammaShear
      (periodCoordMap p.1 (fullRankDomain p) (t • periodVector p.1 ![0,0,0,1] + v)) =
      ((orderThreeStandardGammaShear (periodCoordMap p.1 (fullRankDomain p) v)).1,
        Pi.single 2 (t : UnitAddCircle) +
          (orderThreeStandardGammaShear (periodCoordMap p.1 (fullRankDomain p) v)).2)
    have h := realEquiv_symm_periodVector p.1 (fullRankDomain p) ![0,0,0,1]
    ext i
    · simp [orderThreeStandardGammaShear, periodCoordMap, map_add, map_smul, h, integerToReal]
    · fin_cases i <;>
        simp [orderThreeStandardGammaShear, periodCoordMap, map_add, map_smul, h, integerToReal]
public theorem orderThree_mappingTorus_orbitProjection (A : AnalyticData)
    (q : AdditiveTorus (parameterMap A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne).1) :
    orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods
      (RadialEllipticActionData.centralFiberOrbitProjection
        (orderThreeRadialActionData A.periods) q) =
      normalizedAffineCoverToCircleMappingTorus orderThreeThreeTorusClutching
        orderThreeThreeTorusClutching_pow (orderThreeGammaNormalFormHomeomorph A.periods q) := by
  have h := congrArg (fun f ↦ f
    ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderThreeRadialActionData A.periods)).symm q)) (orderThree_coverProjection_square A.periods)
  change _ = normalizedAffineCoverToCircleMappingTorus _ _
    (orderThreeGammaNormalFormHomeomorph A.periods
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph _)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph _).symm q))) at h
  rw [Homeomorph.apply_symm_apply] at h
  exact h

public theorem orderThree_fixedLoop_inverse_real (A : AnalyticData) (t : ℝ) (s : StdTorus 1) :
    (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
      (fixedLoopMappingTorusMap orderThreeClutchingAddEquiv orderThreeFixedCoordinateTwo
        ((t : UnitAddCircle),s)) =
      RadialEllipticActionData.centralFiberOrbitProjection (orderThreeRadialActionData A.periods)
        ((orderThreeGammaNormalFormHomeomorph A.periods).symm
          (((t / 3 : ℝ) : UnitAddCircle), standardThreeTorusCoordinateCircle 2 s)) := by
  apply (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).injective
  erw [Homeomorph.apply_symm_apply, A.orderThree_mappingTorus_orbitProjection,
    Homeomorph.apply_symm_apply]
  erw [SphereSixComplex.CyclicMappingTorus.Cross.normalizedAffineCover_real
    3 orderThreeClutchingAddEquiv orderThreeThreeTorusClutching_pow]
  have ht : (3 : ℝ) * (t / 3) = t := by ring
  erw [ht]
  change (realMappingTorusHomeomorph _)
    (fixedLoopRealMappingTorusMap _ _
      (circleProductRealMappingTorusHomeomorph ((t : UnitAddCircle),s))) = _
  have h := circleProductRealMappingTorusHomeomorph_real (X := StdTorus 1) (t,s)
  change circleProductRealMappingTorusHomeomorph ((t : UnitAddCircle),s) = _ at h
  erw [h, fixedLoopRealMappingTorusMap_mk]
  rfl


public theorem orderThree_fixedLoop_fourth (A : AnalyticData)
    (t : UnitAddCircle) (s : StdTorus 1) :
    ((orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
      (fixedLoopMappingTorusMap orderThreeClutchingAddEquiv orderThreeFixedCoordinateTwo
        (t,s))).val =
    orderThreeFourthCircleTranslation A.periods
      (s 0, ((orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
        (fixedLoopMappingTorusMap orderThreeClutchingAddEquiv orderThreeFixedCoordinateTwo
          (t,0))).val) := by
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective t
  erw [A.orderThree_fixedLoop_inverse_real r s, A.orderThree_fixedLoop_inverse_real r 0]
  change Quotient.mk _ ((orderThreeRadialActionData A.periods).actionData.center,
    (orderThreeGammaNormalFormHomeomorph A.periods).symm
      (((r / 3 : ℝ) : UnitAddCircle), standardThreeTorusCoordinateCircle 2 s)) =
    Quotient.mk _ ((orderThreeRadialActionData A.periods).actionData.center,
      fourthPeriodCircle _ (s 0) + (orderThreeGammaNormalFormHomeomorph A.periods).symm
        (((r / 3 : ℝ) : UnitAddCircle), standardThreeTorusCoordinateCircle 2 0))
  apply congrArg (Quotient.mk _)
  apply congrArg (Prod.mk _)
  apply (orderThreeGammaNormalFormHomeomorph A.periods).injective
  rw [Homeomorph.apply_symm_apply, A.orderThree_gamma_fourth,
    Homeomorph.apply_symm_apply]
  congr 1
  ext i
  fin_cases i <;> simp [standardThreeTorusCoordinateCircle, standardThreeTorusTailRetractionOne,
    standardFourTorusCoordinateCircle, Fin.tail]

public theorem orderFour_gamma_fourth (A : AnalyticData) (z : UnitAddCircle)
    (q : AdditiveTorus
      (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    orderFourGammaNormalFormHomeomorph A.periods
      (fourthPeriodCircle
        (parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo) z + q) =
    ((orderFourGammaNormalFormHomeomorph A.periods q).1,
      Pi.single 2 z + (orderFourGammaNormalFormHomeomorph A.periods q).2) := by
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  induction q using Quotient.inductionOn with
  | _ v =>
    rw [fourthPeriodCircle_real]
    let p := parameterMap A.periods A.modular.modularParameter.toTriangleUniformization.zTwo
    change orderFourStandardGammaShear
      (periodCoordMap p.1 (fullRankDomain p) (t • periodVector p.1 ![0,0,0,1] + v)) =
      ((orderFourStandardGammaShear (periodCoordMap p.1 (fullRankDomain p) v)).1,
        Pi.single 2 (t : UnitAddCircle) +
          (orderFourStandardGammaShear (periodCoordMap p.1 (fullRankDomain p) v)).2)
    have h := realEquiv_symm_periodVector p.1 (fullRankDomain p) ![0,0,0,1]
    ext i
    · simp [orderFourStandardGammaShear, periodCoordMap, map_add, map_smul, h, integerToReal]
    · fin_cases i <;>
        simp [orderFourStandardGammaShear, periodCoordMap, map_add, map_smul, h, integerToReal]
public theorem orderFour_mappingTorus_orbitProjection (A : AnalyticData)
    (q : AdditiveTorus (parameterMap A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo).1) :
    orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods
      (RadialEllipticActionData.centralFiberOrbitProjection
        (orderFourRadialActionData A.periods) q) =
      normalizedAffineCoverToCircleMappingTorus orderFourThreeTorusClutching
        orderFourThreeTorusClutching_pow (orderFourGammaNormalFormHomeomorph A.periods q) := by
  have h := congrArg (fun f ↦ f
    ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
      (orderFourRadialActionData A.periods)).symm q)) (orderFour_coverProjection_square A.periods)
  change _ = normalizedAffineCoverToCircleMappingTorus _ _
    (orderFourGammaNormalFormHomeomorph A.periods
      ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph _)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph _).symm q))) at h
  rw [Homeomorph.apply_symm_apply] at h
  exact h

public theorem orderFour_fixedLoop_inverse_real (A : AnalyticData) (t : ℝ) (s : StdTorus 1) :
    (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
      (fixedLoopMappingTorusMap orderFourClutchingAddEquiv orderFourFixedCoordinateTwo
        ((t : UnitAddCircle),s)) =
      RadialEllipticActionData.centralFiberOrbitProjection (orderFourRadialActionData A.periods)
        ((orderFourGammaNormalFormHomeomorph A.periods).symm
          (((t / 4 : ℝ) : UnitAddCircle), standardThreeTorusCoordinateCircle 2 s)) := by
  apply (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).injective
  erw [Homeomorph.apply_symm_apply, A.orderFour_mappingTorus_orbitProjection,
    Homeomorph.apply_symm_apply]
  erw [SphereSixComplex.CyclicMappingTorus.Cross.normalizedAffineCover_real
    4 orderFourClutchingAddEquiv orderFourThreeTorusClutching_pow]
  have ht : (4 : ℝ) * (t / 4) = t := by ring
  erw [ht]
  change (realMappingTorusHomeomorph _)
    (fixedLoopRealMappingTorusMap _ _
      (circleProductRealMappingTorusHomeomorph ((t : UnitAddCircle),s))) = _
  have h := circleProductRealMappingTorusHomeomorph_real (X := StdTorus 1) (t,s)
  change circleProductRealMappingTorusHomeomorph ((t : UnitAddCircle),s) = _ at h
  erw [h, fixedLoopRealMappingTorusMap_mk]
  rfl


public theorem orderFour_fixedLoop_fourth (A : AnalyticData)
    (t : UnitAddCircle) (s : StdTorus 1) :
    ((orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
      (fixedLoopMappingTorusMap orderFourClutchingAddEquiv orderFourFixedCoordinateTwo
        (t,s))).val =
    orderFourFourthCircleTranslation A.periods
      (s 0, ((orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
        (fixedLoopMappingTorusMap orderFourClutchingAddEquiv orderFourFixedCoordinateTwo
          (t,0))).val) := by
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective t
  erw [A.orderFour_fixedLoop_inverse_real r s, A.orderFour_fixedLoop_inverse_real r 0]
  change Quotient.mk _ ((orderFourRadialActionData A.periods).actionData.center,
    (orderFourGammaNormalFormHomeomorph A.periods).symm
      (((r / 4 : ℝ) : UnitAddCircle), standardThreeTorusCoordinateCircle 2 s)) =
    Quotient.mk _ ((orderFourRadialActionData A.periods).actionData.center,
      fourthPeriodCircle _ (s 0) + (orderFourGammaNormalFormHomeomorph A.periods).symm
        (((r / 4 : ℝ) : UnitAddCircle), standardThreeTorusCoordinateCircle 2 0))
  apply congrArg (Quotient.mk _)
  apply congrArg (Prod.mk _)
  apply (orderFourGammaNormalFormHomeomorph A.periods).injective
  rw [Homeomorph.apply_symm_apply, A.orderFour_gamma_fourth,
    Homeomorph.apply_symm_apply]
  congr 1
  ext i
  fin_cases i <;> simp [standardThreeTorusCoordinateCircle, standardThreeTorusTailRetractionOne,
    standardFourTorusCoordinateCircle, Fin.tail]


open EllipticHomologyGeneratorAlignment

public def orderThreeCoreToStar {A : AnalyticData} (R : A.AffineRadialCompletionInput) :
    C(orderThreeReducedCentralFiber A.periods, A.VanKampenSpace) :=
  (ellipticUnionInclusion R.twoDiscCover).comp
    ((IntegralMayerVietoris.leftToUnion R.twoDiscCover.orderThreeSide
      R.twoDiscCover.orderFourSide).comp R.twoDiscCover.orderThreeSideHomotopyEquiv.invFun)

public def orderFourCoreToStar {A : AnalyticData} (R : A.AffineRadialCompletionInput) :
    C(orderFourReducedCentralFiber A.periods, A.VanKampenSpace) :=
  (ellipticUnionInclusion R.twoDiscCover).comp
    ((IntegralMayerVietoris.rightToUnion R.twoDiscCover.orderThreeSide
      R.twoDiscCover.orderFourSide).comp R.twoDiscCover.orderFourSideHomotopyEquiv.invFun)

public theorem reducedFibersToStar_left {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (orderThreeReducedCentralFiber A.periods)) :
    integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2 (x,0)) =
        integralSingularHomologyMap 2 (orderThreeCoreToStar R) x := by
  change integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
    (integralSingularHomologyMap 2
      (IntegralMayerVietoris.leftToUnion R.twoDiscCover.orderThreeSide
        R.twoDiscCover.orderFourSide)
      (integralSingularHomologyMap 2 R.twoDiscCover.orderThreeSideHomotopyEquiv.invFun x) +
    integralSingularHomologyMap 2
      (IntegralMayerVietoris.rightToUnion R.twoDiscCover.orderThreeSide
        R.twoDiscCover.orderFourSide)
      (integralSingularHomologyMap 2 R.twoDiscCover.orderFourSideHomotopyEquiv.invFun 0)) = _
  rw [map_zero, map_zero, add_zero, integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang]
  rfl

public theorem reducedFibersToStar_right {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (orderFourReducedCentralFiber A.periods)) :
    integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2 (0,x)) =
        integralSingularHomologyMap 2 (orderFourCoreToStar R) x := by
  change integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
    (integralSingularHomologyMap 2
      (IntegralMayerVietoris.leftToUnion R.twoDiscCover.orderThreeSide
        R.twoDiscCover.orderFourSide)
      (integralSingularHomologyMap 2 R.twoDiscCover.orderThreeSideHomotopyEquiv.invFun 0) +
    integralSingularHomologyMap 2
      (IntegralMayerVietoris.rightToUnion R.twoDiscCover.orderThreeSide
        R.twoDiscCover.orderFourSide)
      (integralSingularHomologyMap 2 R.twoDiscCover.orderFourSideHomotopyEquiv.invFun x)) = _
  rw [map_zero, map_zero, zero_add, integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang]
  rfl

public def orderThreeFixedTorusToStar {A : AnalyticData} (R : A.AffineRadialCompletionInput) :
    C(UnitAddCircle × StdTorus 1, A.VanKampenSpace) :=
  (orderThreeCoreToStar R).comp
    ⟨fun p ↦ (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
      (fixedLoopMappingTorusMap orderThreeClutchingAddEquiv orderThreeFixedCoordinateTwo p),
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm.continuous.comp
        (fixedLoopMappingTorusMap orderThreeClutchingAddEquiv
          orderThreeFixedCoordinateTwo).continuous⟩

public def orderFourFixedTorusToStar {A : AnalyticData} (R : A.AffineRadialCompletionInput) :
    C(UnitAddCircle × StdTorus 1, A.VanKampenSpace) :=
  (orderFourCoreToStar R).comp
    ⟨fun p ↦ (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm
      (fixedLoopMappingTorusMap orderFourClutchingAddEquiv orderFourFixedCoordinateTwo p),
      (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm.continuous.comp
        (fixedLoopMappingTorusMap orderFourClutchingAddEquiv
          orderFourFixedCoordinateTwo).continuous⟩

open PositiveCircleCross

public theorem orderThreeFixedTorusToStar_homology {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    integralSingularHomologyMap 2 (orderThreeFixedTorusToStar R)
      positiveCircleProductGenerator =
    integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2
        ((integralSingularHomologyEquiv 2
          (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
          orderThreeFixedLoopSweep,0)) := by
  rw [reducedFibersToStar_left]
  change _ = integralSingularHomologyMap 2 (orderThreeCoreToStar R)
    (integralSingularHomologyMap 2
      ⟨(orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm,
        (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm.continuous⟩
      (integralSingularHomologyMap 2
        (fixedLoopMappingTorusMap orderThreeClutchingAddEquiv orderThreeFixedCoordinateTwo)
        positiveCircleProductGenerator))
  conv_rhs =>
    erw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  rfl

public theorem orderFourFixedTorusToStar_homology {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    integralSingularHomologyMap 2 (orderFourFixedTorusToStar R)
      positiveCircleProductGenerator =
    integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2
        (0,(integralSingularHomologyEquiv 2
          (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
          orderFourFixedLoopSweep)) := by
  rw [reducedFibersToStar_right]
  change _ = integralSingularHomologyMap 2 (orderFourCoreToStar R)
    (integralSingularHomologyMap 2
      ⟨(orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm,
        (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods).symm.continuous⟩
      (integralSingularHomologyMap 2
        (fixedLoopMappingTorusMap orderFourClutchingAddEquiv orderFourFixedCoordinateTwo)
        positiveCircleProductGenerator))
  conv_rhs =>
    erw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  rfl

public theorem orderThree_fixedLoopSweep_toStar_eq_zero {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2
        ((integralSingularHomologyEquiv 2
          (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
          (-orderThreeFixedLoopSweep),0)) = 0 := by
  have hz : integralSingularHomologyMap 2 (orderThreeFixedTorusToStar R)
      positiveCircleProductGenerator = 0 := by
    let _ := A.star_homologyOne_subsingleton
    apply circleAction_torus_homologyTwo_eq_zero _ A.starFourthTranslation
    intro t s
    exact (orderThreeSide_fourthTranslation R (s 0) _ _
      (A.orderThree_fixedLoop_fourth t s)).symm
  rw [orderThreeFixedTorusToStar_homology] at hz
  have hn : ((integralSingularHomologyEquiv 2
      (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
      (-orderThreeFixedLoopSweep),
      (0 : IntegralSingularHomology 2 (orderFourReducedCentralFiber A.periods))) =
      -((integralSingularHomologyEquiv 2
        (orderThreeReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
        orderThreeFixedLoopSweep,0) := by
    rw [map_neg]
    exact Prod.ext rfl neg_zero.symm
  rw [hn, map_neg, map_neg, hz, neg_zero]

public theorem orderFour_fixedLoopSweep_toStar_eq_zero {A : AnalyticData}
    (R : A.AffineRadialCompletionInput) :
    integralSingularHomologyMap 2 (ellipticUnionInclusion R.twoDiscCover)
      (reducedFibersToUnion R.twoDiscCover 2
        (0,(integralSingularHomologyEquiv 2
          (orderFourReducedCentralFiberCircleMappingTorusHomeomorph A.periods)).symm
          orderFourFixedLoopSweep)) = 0 := by
  rw [← orderFourFixedTorusToStar_homology]
  let _ := A.star_homologyOne_subsingleton
  apply circleAction_torus_homologyTwo_eq_zero _ A.starFourthTranslation
  intro t s
  exact (orderFourSide_fourthTranslation R (s 0) _ _
    (A.orderFour_fixedLoop_fourth t s)).symm

end SphereSixComplex.Geometry.AnalyticData
