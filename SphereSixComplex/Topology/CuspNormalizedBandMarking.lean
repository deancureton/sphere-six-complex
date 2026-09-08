module
public import SphereSixComplex.Topology.CuspNormalizedCylinderBoundary
public import SphereSixComplex.Topology.IntegerPeriodCircle
public import SphereSixComplex.Topology.PaperCuspFourthPeriodInvariance

@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory TopologicalSpace
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology GlobalTorusFamily TriangleGroup
open SphereSixComplex.StandardTorusHomology SphereSixComplex.Periods
open ComplexTorus EllipticFamilySpecialization EllipticRealPeriodProductTrivialization
open SectionSevenEllipticTwoDiscHomologyCoordinates
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

public theorem regularMovingToFixed_period_smul (A : PaperAnalyticData)
    (b : RegularBase (U := A.paperTriangleUniformization)) (n : IntegerPeriods) (t : ℝ) :
    A.regularMovingToFixed b (t • periodVector (regularParameterMap A.periods b).1 n) =
      t • periodVector A.duplicatedSectionSevenBandParameter n := by
  change (fullRankDomain _).realEquiv
    ((fullRankDomain _).realEquiv.symm (t • periodVector _ n)) = _
  dsimp only [Prod.fst]
  rw [map_smul]
  change (fullRankDomain _).realEquiv
    (t • ((fullRankDomain (regularParameterMap A.periods b)).realEquiv.symm
      (periodVector (regularParameterMap A.periods b).1 n))) = _
  rw [realEquiv_symm_periodVector, map_smul, FullRank.map_integer]
  rfl

public theorem normalizedMarkedPeriodCircle_central (A : PaperAnalyticData)
    (n : IntegerPeriods) (z : StdTorus 1) :
    A.stripLiftPoint A.sectionSevenAffineNamedStripLift sectionSevenAffineStripMidpoint
      (integerPeriodCircle A.duplicatedSectionSevenBandParameter
        A.duplicatedSectionSevenBandFullRank n z) =
      regularPeriodCircleInGlobal A.periods n
        (z 0, A.sectionSevenAffineNormalizedMidpoint) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (z 0)
  have hz : z = fun _ ↦ (t : UnitAddCircle) := by
    ext i
    fin_cases i
    exact ht.symm
  rw [hz, integerPeriodCircle_real]
  rw [← A.regularMovingToFixed_period_smul
    (A.sectionSevenAffineNamedStripLift.lift sectionSevenAffineStripMidpoint)]
  erw [A.stripLiftPoint_regularMovingToFixed]
  rw [A.sectionSevenAffineNamedStripLift_apply_midpoint]
  change _ = Quotient.mk _ (regularPeriodCircle A.periods n ((t : UnitAddCircle), _))
  rw [regularPeriodCircle_real]
  rfl

public def normalizedMarkedPeriodBandCircle {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) :
    C(StdTorus 1, (Opens.toTopCat (TopCat.of A.SectionSevenEllipticInterior)).obj
      (orderThreeOpen R.twoDiscCover ⊓ orderFourOpen R.twoDiscCover)) where
  toFun z := A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.symm
    ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation).symm
        (sectionSevenAffineStripMidpoint, integerPeriodCircle A.duplicatedSectionSevenBandParameter
          A.duplicatedSectionSevenBandFullRank n z))
  continuous_toFun := A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.symm.continuous.comp
    ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation).symm.continuous.comp
        (continuous_const.prodMk (integerPeriodCircle _ _ _).continuous))

public theorem normalizedMarkedPeriodBandCircle_coordinate {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) :
    R.twoDiscCover.bandHomotopyEquiv.toFun.comp (normalizedMarkedPeriodBandCircle R n) =
      integerPeriodCircle A.duplicatedSectionSevenBandParameter
        A.duplicatedSectionSevenBandFullRank n := by
  ext1 z
  change (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
    A.sectionSevenAffineCentralSeparation
      (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph
        (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.symm
          ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
            A.sectionSevenAffineCentralSeparation).symm
            (sectionSevenAffineStripMidpoint, integerPeriodCircle _ _ n z))))).2 = _
  erw [Homeomorph.apply_symm_apply]
  rfl

public theorem normalizedMarkedPeriodBandCircle_interior {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) (z : StdTorus 1) :
    (normalizedMarkedPeriodBandCircle R n z).1 =
      A.centralToEllipticInterior
        (regularPeriodCircleInGlobal A.periods n (z 0, A.sectionSevenAffineNormalizedMidpoint)) := by
  have h := A.sectionSevenAffineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    A.sectionSevenAffineCentralSeparation
    (sectionSevenAffineStripMidpoint, integerPeriodCircle A.duplicatedSectionSevenBandParameter
      A.duplicatedSectionSevenBandFullRank n z)
  rw [A.normalizedMarkedPeriodCircle_central] at h
  have h' := congrArg A.centralToEllipticInterior h
  dsimp only [centralToEllipticInterior, sectionSevenAffineCentralBandToCentralFamily,
    ContinuousMap.coe_mk] at h'
  rw [Homeomorph.symm_apply_apply] at h'
  exact h'

public theorem normalizedMarkedPeriodBandCircle_bandOne {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (n : IntegerPeriods) :
    EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (integralSingularHomologyMap 1 (normalizedMarkedPeriodBandCircle R n)
        standardCircleHomologyGenerator) = n := by
  let e := PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData A.periods)
  change additiveTorusHomologyDegreeOne A.duplicatedSectionSevenBandParameter
    A.duplicatedSectionSevenBandFullRank
      (integralSingularHomologyMap 1 ⟨e, e.continuous⟩
        (integralSingularHomologyMap 1 ⟨e.symm, e.symm.continuous⟩
          (integralSingularHomologyMap 1 R.twoDiscCover.bandHomotopyEquiv.toFun
            (integralSingularHomologyMap 1 (normalizedMarkedPeriodBandCircle R n)
              standardCircleHomologyGenerator)))) = n
  erw [integralSingularHomologyMap_comp_wang 1 ⟨e.symm, e.symm.continuous⟩]
  have he : (⟨e, e.continuous⟩ : C(_, _)).comp ⟨e.symm, e.symm.continuous⟩ =
      ContinuousMap.id _ := by
    ext1 z
    exact e.apply_symm_apply z
  erw [he, integralSingularHomologyMap_id_wang]
  erw [integralSingularHomologyMap_comp_wang,
    normalizedMarkedPeriodBandCircle_coordinate]
  exact integerPeriodCircle_homology _ _ n

public theorem normalizedThirdOverlapCircle_eq_marked {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) (g : Delta) :
    normalizedThirdOverlapCircle R (regularSourceEquiv g A.sectionSevenAffineNormalizedMidpoint)
      ((A.regularCoordinate_sourceEquiv g _).trans A.sectionSevenAffineNormalizedMidpoint_projects) =
      normalizedMarkedPeriodBandCircle R (rhoLambda g⁻¹ (Pi.single 2 1)) := by
  ext1 z
  apply Subtype.ext
  rw [normalizedMarkedPeriodBandCircle_interior]
  change A.centralToEllipticInterior
    (regularPeriodCircleInGlobal A.periods (Pi.single 2 1)
      (z 0, regularSourceEquiv g A.sectionSevenAffineNormalizedMidpoint)) = _
  exact congrArg A.centralToEllipticInterior
    (DFunLike.congr_fun (regularPeriodCircleFamily_deck A.periods (Pi.single 2 1)
      g A.sectionSevenAffineNormalizedMidpoint) (z 0))

public theorem normalizedThirdOverlapCircle_midpoint_eq_marked {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    normalizedThirdOverlapCircle R A.sectionSevenAffineNormalizedMidpoint
      A.sectionSevenAffineNormalizedMidpoint_projects =
      normalizedMarkedPeriodBandCircle R (Pi.single 2 1) := by
  ext1 z
  apply Subtype.ext
  rw [normalizedMarkedPeriodBandCircle_interior]
  rfl

public theorem normalizedThirdOverlapCircle_difference_bandOne {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (integralSingularHomologyMap 1
        (normalizedThirdOverlapCircle R (regularSourceEquiv g₁ A.sectionSevenAffineNormalizedMidpoint)
          ((A.regularCoordinate_sourceEquiv g₁ _).trans A.sectionSevenAffineNormalizedMidpoint_projects))
        standardCircleHomologyGenerator -
      integralSingularHomologyMap 1
        (normalizedThirdOverlapCircle R A.sectionSevenAffineNormalizedMidpoint
          A.sectionSevenAffineNormalizedMidpoint_projects) standardCircleHomologyGenerator) =
      alphaOneKernelGenerator := by
  erw [normalizedThirdOverlapCircle_eq_marked, normalizedThirdOverlapCircle_midpoint_eq_marked,
    map_sub, normalizedMarkedPeriodBandCircle_bandOne, normalizedMarkedPeriodBandCircle_bandOne]
  have hn : (Pi.single 2 1 : IntegerPeriods) = ![0, 0, 1, 0] := by
    ext i
    fin_cases i <;> simp
  rw [hn]
  exact inverse_orderThree_thirdBasis_difference

open CircleProductIdentityMappingTorus CanonicalProductWangBoundarySlant PositiveCircleCross

public def normalizedCuspProductClass :
    IntegralSingularHomology 2 (CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :=
  integralSingularHomologyMap 2
    (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
      C(UnitAddCircle × StdTorus 1, CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
    positiveCircleProductGenerator

public theorem normalizedCuspProductClass_wang :
    (circleMappingTorusWangPresentationOfCover (Homeomorph.refl (StdTorus 1)) 1).boundary
      normalizedCuspProductClass = standardCircleHomologyGenerator :=
  canonicalProductWangBoundary_positiveGenerator_core

public theorem normalizedThirdCylinder_primitive_boundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (ConcreteCategory.hom ((BinaryOpenCover.openCoverHomologyComparisonOfCover
        (ellipticOpenCover R.twoDiscCover)).boundary 1)
        (integralSingularHomologyMap 2
          (identityMappingTorusMapOfLoop
            (A.normalizedThirdZeroCirclePath.trans A.normalizedThirdOneCirclePath))
          normalizedCuspProductClass)) = alphaOneKernelGenerator := by
  rw [normalizedThirdMeridianCylinder_boundary, normalizedCuspProductClass_wang]
  exact normalizedThirdOverlapCircle_difference_bandOne R

public theorem actualCuspChosenThirdSweep_interior_class (A : PaperAnalyticData) :
    integralSingularHomologyMap 2
      (A.centralToEllipticInterior.comp A.actualCuspChosenThirdSweepCentral)
      positiveCircleProductGenerator =
    integralSingularHomologyMap 2
      (identityMappingTorusMapOfLoop
        (A.normalizedThirdZeroCirclePath.trans A.normalizedThirdOneCirclePath))
      normalizedCuspProductClass := by
  have h := DFunLike.congr_fun A.actualCuspChosenThirdSweep_interior_homology
    normalizedCuspProductClass
  unfold normalizedCuspProductClass at h
  rw [integralSingularHomologyMap_comp_wang] at h
  have he :
      (A.centralToEllipticInterior.comp
        (A.actualCuspChosenThirdSweepCentral.comp
          ((circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).symm :
            C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)), UnitAddCircle × StdTorus 1)))).comp
        (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
          C(UnitAddCircle × StdTorus 1, CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) =
      A.centralToEllipticInterior.comp A.actualCuspChosenThirdSweepCentral := by
    ext1 z
    exact congrArg (A.centralToEllipticInterior ∘ A.actualCuspChosenThirdSweepCentral)
      ((circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1)).symm_apply_apply z)
  rw [he] at h
  exact h

public theorem actualCuspChosenThirdSweep_primitive_boundary {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (ConcreteCategory.hom ((BinaryOpenCover.openCoverHomologyComparisonOfCover
        (ellipticOpenCover R.twoDiscCover)).boundary 1)
        (integralSingularHomologyMap 2
          (A.centralToEllipticInterior.comp A.actualCuspChosenThirdSweepCentral)
          positiveCircleProductGenerator)) = alphaOneKernelGenerator := by
  rw [A.actualCuspChosenThirdSweep_interior_class]
  exact normalizedThirdCylinder_primitive_boundary R

open SectionSevenEllipticTwoDiscCoverData

public theorem cuspPulledBackBoundaryHom_eq_interiorBoundary {A : PaperAnalyticData}
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    D.cuspPulledBackBoundaryHom x =
      ConcreteCategory.hom (D.ellipticOpenCoverHomologyComparison.boundary 1)
        (integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom x) := by
  have hn := BinaryOpenCover.OpenCoverHomologyComparison.boundary_pullback_naturality
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)
    D.cuspOpenCoverHomologyComparison D.ellipticOpenCoverHomologyComparison
    D.cuspOpenCoverPullbackNaturality 1
  change ConcreteCategory.hom
    (D.cuspOpenCoverHomologyComparison.boundary 1 ≫
      BinaryOpenCover.openIntersectionPullbackHomologyMap D.cuspToEllipticInteriorMap
        (orderThreeOpen D) (orderFourOpen D) 1 ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (orderThreeOpen D) (orderFourOpen D) 1).inv) x = _
  erw [← Category.assoc, hn]
  have hi :
      (TopCat.isoOfHomeo (BinaryOpenCover.opensIntersectionHomeomorph
        (orderThreeOpen D) (orderFourOpen D))).inv =
      𝟙 (TopCat.of (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) := by
    ext y
    rfl
  have hm := congrArg (BinaryOpenCover.integralHomologyFunctor 1).map hi
  rw [(BinaryOpenCover.integralHomologyFunctor 1).map_id] at hm
  change (BinaryOpenCover.opensIntersectionHomologyIso
    (orderThreeOpen D) (orderFourOpen D) 1).inv = _ at hm
  rw [hm]
  rfl

public theorem cuspToEllipticInteriorMap_eq_central {A : PaperAnalyticData}
    (D : A.SectionSevenEllipticTwoDiscCoverData)
    (q : A.openEmbeddingStarData.collarSource 0) :
    D.cuspToEllipticInteriorMap q = A.centralToEllipticInterior (A.starToCentral 0 q) := by
  have h : A.sectionSevenEllipticCentralImageHomeomorph
      ⟨D.cuspToEllipticInteriorMap q, D.cuspToEllipticInteriorMap_mem_centralImage q⟩ =
      A.starToCentral 0 q := by
    apply A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.injective
    apply Subtype.ext
    rw [A.centralToSectionSevenEulerPiece_centralImage]
    exact (A.centralToSectionSevenEulerPiece_starToCentral 0 q).symm
  have h' := congrArg A.sectionSevenEllipticCentralImageHomeomorph.symm h
  rw [Homeomorph.symm_apply_apply] at h'
  exact congrArg Subtype.val h'

public theorem actualCuspChosenThirdSweep_pulledBack_primitive {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (R.twoDiscCover.cuspPulledBackBoundaryHom
        (integralSingularHomologyMap 2 A.actualCuspChosenThirdSweep positiveCircleProductGenerator)) =
      alphaOneKernelGenerator := by
  rw [cuspPulledBackBoundaryHom_eq_interiorBoundary, integralSingularHomologyMap_comp_wang]
  have hc : R.twoDiscCover.cuspToEllipticInteriorMap.hom.comp A.actualCuspChosenThirdSweep =
      A.centralToEllipticInterior.comp A.actualCuspChosenThirdSweepCentral := by
    ext1 z
    exact cuspToEllipticInteriorMap_eq_central R.twoDiscCover _
  rw [hc]
  exact actualCuspChosenThirdSweep_primitive_boundary R

public theorem actualCuspRawFour_pulledBack_primitive {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
      (R.twoDiscCover.cuspPulledBackBoundaryHom
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) =
      alphaOneKernelGenerator := by
  rw [actualCuspRawFour_pulledBack_boundary_eq_sweep,
    integralSingularHomologyMap_eq_of_homotopy 2 A.actualCuspThirdSweep_homotopic_chosen.some]
  exact actualCuspChosenThirdSweep_pulledBack_primitive R

public theorem actualCuspRawFour_pulledBack_scalar_one {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.cuspPulledBackBoundaryCoordinateHom R.homologyAlignment
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) = 1 := by
  rw [SectionSevenEllipticTwoDiscCoverData.cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate]
  change (EllipticBandHomologyAlignment.bandOne (D := R.twoDiscCover)
    (R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)))) 3 = 1
  rw [actualCuspRawFour_pulledBack_primitive]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData
end
