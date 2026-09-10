module
public import SphereSixComplex.Paper.Topology.EllipticFourthHomologySweep
public import SphereSixComplex.Paper.Topology.CuspTranslationHomologyComparison

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus GlobalTorusFamily EllipticFamilySpecialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open PositiveCircleCross CircleProductIdentityMappingTorus

public def fourthFirstCoordinateTorus : C(StdTorus 2, StdTorus 4) :=
  ⟨fun z ↦ ![z 1, 0, 0, z 0], by fun_prop⟩

public theorem fourthFirstCoordinateTorus_real (A : PaperAnalyticData) (t s : ℝ) :
    (additiveTorusStdHomeomorph A.duplicatedSectionSevenBandParameter
      A.duplicatedSectionSevenBandFullRank).symm
      (fourthFirstCoordinateTorus ![(t : UnitAddCircle), (s : UnitAddCircle)]) =
    additiveTorusProjection A.duplicatedSectionSevenBandParameter
      (t • periodVector A.duplicatedSectionSevenBandParameter ![0,0,0,1] +
        s • periodVector A.duplicatedSectionSevenBandParameter (Pi.single 0 1)) := by
  apply (additiveTorusStdHomeomorph _ A.duplicatedSectionSevenBandFullRank).injective
  rw [Homeomorph.apply_symm_apply]
  change _ = periodCoordMap _ _ _
  ext i
  simp only [periodCoordMap, map_add, map_smul, realEquiv_symm_periodVector]
  fin_cases i <;> simp [fourthFirstCoordinateTorus, integerToReal]

public def normalizedFourthFirstTorus (A : PaperAnalyticData) :
    C(StdTorus 2, A.CentralFamily) :=
  (A.regularFixedFiberMap A.sectionSevenAffineNormalizedMidpoint).comp
    (((additiveTorusStdHomeomorph A.duplicatedSectionSevenBandParameter
      A.duplicatedSectionSevenBandFullRank).symm : C(_, _)).comp fourthFirstCoordinateTorus)

public theorem normalizedFourthFirstTorus_real (A : PaperAnalyticData) (t s : ℝ) :
    A.normalizedFourthFirstTorus ![(t : UnitAddCircle), (s : UnitAddCircle)] =
    A.centralFourthTranslation ((t : UnitAddCircle),
      regularPeriodCircleInGlobal A.periods (Pi.single 0 1)
        ((s : UnitAddCircle), A.sectionSevenAffineNormalizedMidpoint)) := by
  change A.regularFixedFiberMap _ ((additiveTorusStdHomeomorph _ _).symm _) = _
  rw [A.fourthFirstCoordinateTorus_real]
  change A.regularFixedFiberCover _ _ = _
  rw [regularFixedFiberCover]
  change _ = invariantPeriodCircleTranslation A.periods _ _ (_, _)
  rw [invariantPeriodCircleTranslation_real]
  change _ = invariantPeriodRealTranslation A.periods _ _
    (t, Quotient.mk _ (regularPeriodCircle A.periods _ ((s : UnitAddCircle), _)))
  rw [regularPeriodCircle_real, invariantPeriodRealTranslation_mk]
  change A.centralQuotientProjection (TorusFamily.projection _ (_, _)) =
    A.centralQuotientProjection (TorusFamily.projection _
      (A.sectionSevenAffineNormalizedMidpoint,
        t • periodVector (regularParameterMap A.periods A.sectionSevenAffineNormalizedMidpoint).1 ![0,0,0,1] +
        s • periodVector (regularParameterMap A.periods A.sectionSevenAffineNormalizedMidpoint).1 (Pi.single 0 1)))
  apply congrArg A.centralQuotientProjection
  apply congrArg (TorusFamily.projection (regularParameterMap A.periods))
  congr 1
  apply_fun A.regularMovingToFixed A.sectionSevenAffineNormalizedMidpoint
    using (fun a b h ↦ by
      have := congrArg (A.regularFixedToMoving A.sectionSevenAffineNormalizedMidpoint) h
      simpa only [regularFixedToMoving_regularMovingToFixed] using this)
  rw [regularMovingToFixed_regularFixedToMoving]
  change _ = (fullRankDomain _).realEquiv ((fullRankDomain _).realEquiv.symm (_ + _))
  rw [map_add, map_add]
  exact (congrArg₂ (· + ·)
    (A.regularMovingToFixed_period_smul _ _ t)
    (A.regularMovingToFixed_period_smul _ _ s)).symm

public theorem ellipticFourthSweep_markedCircle_map (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.ellipticFourthTranslation.comp
      (circleProductMap (R.twoDiscCover.canonicalBandToEllipticInteriorInclusionMap.comp
        (normalizedMarkedPeriodBandCircle R (Pi.single 0 1)))) =
    A.fourthTranslationCentralInclusion.comp
      (A.normalizedFourthFirstTorus.comp (circleProdStandardCircleHomeomorph : C(_, _))) := by
  ext1 p
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective (p.2 0)
  have hp : p = ((t : UnitAddCircle), fun _ ↦ (s : UnitAddCircle)) := by
    ext i
    · exact ht.symm
    · fin_cases i
      exact hs.symm
  subst p
  change A.ellipticFourthTranslation ((t : UnitAddCircle),
    (normalizedMarkedPeriodBandCircle R (Pi.single 0 1) (fun _ ↦ (s : UnitAddCircle))).1) = _
  rw [normalizedMarkedPeriodBandCircle_interior]
  change A.ellipticFourthTranslation (_, A.fourthTranslationCentralInclusion _) = _
  rw [A.ellipticFourthTranslation_central]
  apply congrArg A.fourthTranslationCentralInclusion
  exact (A.normalizedFourthFirstTorus_real t s).symm

public theorem ellipticFourthSweep_markedCircle (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.ellipticFourthHomologySweep
      (integralSingularHomologyMap 1 R.twoDiscCover.canonicalBandToEllipticInteriorInclusionMap
        (integralSingularHomologyMap 1 (normalizedMarkedPeriodBandCircle R (Pi.single 0 1))
          standardCircleHomologyGenerator)) =
    integralSingularHomologyMap 2 A.fourthTranslationCentralInclusion
      (integralSingularHomologyMap 2 A.normalizedFourthFirstTorus
        standardTwoTorusHomologyGenerator) := by
  have hc := integralSingularHomologyMap_comp_wang 1
    (normalizedMarkedPeriodBandCircle R (Pi.single 0 1))
    R.twoDiscCover.canonicalBandToEllipticInteriorInclusionMap standardCircleHomologyGenerator
  erw [hc]
  change integralSingularHomologyMap 2 A.ellipticFourthTranslation
    (normalizedCircleCross 1 _) = _
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 A.ellipticFourthTranslation
    (integralSingularHomologyMap 2 _ positiveCircleProductGenerator) = _
  rw [integralSingularHomologyMap_comp_wang]
  erw [A.ellipticFourthSweep_markedCircle_map R]
  rw [← integralSingularHomologyMap_comp_wang, ← integralSingularHomologyMap_comp_wang]
  congr 2
  exact (integralSingularHomologyEquiv 2 circleProdStandardCircleHomeomorph).apply_symm_apply _

public theorem fourthFirstCoordinateTorus_homology :
    stdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 fourthFirstCoordinateTorus
        standardTwoTorusHomologyGenerator) = -Pi.single (2 : Fin 6) 1 := by
  have hm : fourthFirstCoordinateTorus = (standardFourTorusCoordinateTwoTorus 2).comp
      (standardTwoTorusMatrixMap !![0,1;1,0]) := by
    ext z i
    fin_cases i <;> simp [fourthFirstCoordinateTorus, standardFourTorusCoordinateTwoTorus,
      standardPeriodPairFirst, standardPeriodPairSecond, standardTwoTorusMatrixMap,
      Fin.sum_univ_two]
  rw [hm, ← integralSingularHomologyMap_comp_wang,
    standardTwoTorusMatrixDeterminantDegree]
  norm_num [Matrix.det_fin_two]
  change standardFourTorusCoordinateTwoTorusHom
    (standardFourTorusCoordinateTwoTorusHomologyClass 2) = _
  rw [standardFourTorusCoordinateTwoTorusHom_coordinateHomologyClass]

public def normalizedFourthFirstBandTorus {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    C(StdTorus 2, (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide : Set _)) where
  toFun z := A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.symm
    ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation).symm
        (sectionSevenAffineStripMidpoint,
          (additiveTorusStdHomeomorph A.duplicatedSectionSevenBandParameter
            A.duplicatedSectionSevenBandFullRank).symm (fourthFirstCoordinateTorus z)))
  continuous_toFun := A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.symm.continuous.comp
    ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation).symm.continuous.comp
      (continuous_const.prodMk ((additiveTorusStdHomeomorph _ _).symm.continuous.comp
        fourthFirstCoordinateTorus.continuous)))

public theorem normalizedFourthFirstBandTorus_interior {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.canonicalBandToEllipticInteriorInclusionMap.comp
      (normalizedFourthFirstBandTorus R) =
    A.fourthTranslationCentralInclusion.comp A.normalizedFourthFirstTorus := by
  ext1 z
  have h := A.sectionSevenAffineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    A.sectionSevenAffineCentralSeparation
    (sectionSevenAffineStripMidpoint, (additiveTorusStdHomeomorph
      A.duplicatedSectionSevenBandParameter A.duplicatedSectionSevenBandFullRank).symm
      (fourthFirstCoordinateTorus z))
  rw [← A.regularFixedFiberPoint_strip, A.sectionSevenAffineNamedStripLift_apply_midpoint] at h
  have h' := congrArg A.centralToEllipticInterior h
  dsimp only [centralToEllipticInterior, sectionSevenAffineCentralBandToCentralFamily,
    ContinuousMap.coe_mk] at h'
  rw [Homeomorph.symm_apply_apply] at h'
  exact h'

private theorem bandTwo_fixedCoordinates {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput)
    (x : IntegralSingularHomology 2 (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide : Set _)) :
    EllipticBandHomologyAlignment.bandTwo (D := R.twoDiscCover) x =
    additiveTorusHomologyDegreeTwo A.duplicatedSectionSevenBandParameter A.duplicatedSectionSevenBandFullRank
      (integralSingularHomologyMap 2 R.twoDiscCover.bandHomotopyEquiv.toFun x) := by
  let e := PaperEllipticReducedCentralFiberCoverModels.RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData A.periods)
  change additiveTorusHomologyDegreeTwo A.duplicatedSectionSevenBandParameter
    A.duplicatedSectionSevenBandFullRank
      (integralSingularHomologyMap 2 ⟨e, e.continuous⟩
        (integralSingularHomologyMap 2 ⟨e.symm, e.symm.continuous⟩
          (integralSingularHomologyMap 2 R.twoDiscCover.bandHomotopyEquiv.toFun
            x))) = _
  erw [integralSingularHomologyMap_comp_wang 2 ⟨e.symm, e.symm.continuous⟩]
  have he : (⟨e, e.continuous⟩ : C(_, _)).comp ⟨e.symm, e.symm.continuous⟩ =
      ContinuousMap.id _ := by ext1 z; exact e.apply_symm_apply z
  erw [he, integralSingularHomologyMap_id_wang]

private theorem additiveTorusTwo_apply (p : Parameters) (h : FullRank p)
    (x : IntegralSingularHomology 2 (AdditiveTorus p)) :
    additiveTorusHomologyDegreeTwo p h x = stdTorusFourHomologyTwo
      (integralSingularHomologyMap 2 (additiveTorusStdHomeomorph p h : C(_, _)) x) := rfl

public theorem normalizedFourthFirstBandTorus_bandTwo {A : PaperAnalyticData}
    (R : A.SectionSevenAffineRadialCompletionInput) :
    EllipticBandHomologyAlignment.bandTwo
      (D := R.twoDiscCover)
      (integralSingularHomologyMap 2 (normalizedFourthFirstBandTorus R)
        standardTwoTorusHomologyGenerator) = -Pi.single (2 : Fin 6) 1 := by
  rw [bandTwo_fixedCoordinates R]
  erw [additiveTorusTwo_apply A.duplicatedSectionSevenBandParameter
    A.duplicatedSectionSevenBandFullRank]
  rw [integralSingularHomologyMap_comp_wang]
  erw [integralSingularHomologyMap_comp_wang 2
    (R.twoDiscCover.bandHomotopyEquiv.toFun.comp (normalizedFourthFirstBandTorus R))]
  have hc : (additiveTorusStdHomeomorph A.duplicatedSectionSevenBandParameter
      A.duplicatedSectionSevenBandFullRank : C(AdditiveTorus A.duplicatedSectionSevenBandParameter, StdTorus 4)).comp
      (R.twoDiscCover.bandHomotopyEquiv.toFun.comp (normalizedFourthFirstBandTorus R)) =
      fourthFirstCoordinateTorus := by
    ext1 z
    change (additiveTorusStdHomeomorph _ _) ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation
        (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.symm
            ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
              A.sectionSevenAffineCentralSeparation).symm _)))).2) = _
    erw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  erw [hc]
  exact fourthFirstCoordinateTorus_homology

public theorem ellipticFourthSweep_translation_fiberCoordinate (A : PaperAnalyticData)
    (R : A.SectionSevenAffineRadialCompletionInput)
    (S : WangHomologyPresentation.NormalizedSplitting
      (SectionSevenEllipticTwoDiscHomologyCoordinates.presentationTwo (D := R.twoDiscCover))) :
    R.homologyAlignment.actualHomologyCoordinates.normalizedEllipticInteriorHomologyTwoEquiv S
      (A.ellipticFourthHomologySweep
        (integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
          (FirstHurewiczProof.hurewiczFunction A.actualCuspOverlapBase
            (Additive.toMul (A.actualCuspAffineBridgeTranslation (Pi.single 0 1)))))) 0 = -12 := by
  erw [A.actualCuspTranslation_homology_eq_band R (Pi.single 0 1)]
  rw [A.ellipticFourthSweep_markedCircle R]
  rw [integralSingularHomologyMap_comp_wang,
    ← normalizedFourthFirstBandTorus_interior R,
    ← integralSingularHomologyMap_comp_wang]
  change R.homologyAlignment.actualHomologyCoordinates.normalizedUnionHomologyTwoEquiv S
    ((integralSingularHomologyEquiv 2
      (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
        (R.twoDiscCover.orderThreeSide ∪ R.twoDiscCover.orderFourSide) R.twoDiscCover.sides_cover)).symm
      (integralSingularHomologyMap 2 R.twoDiscCover.canonicalBandToEllipticInteriorInclusionMap
        (integralSingularHomologyMap 2 (normalizedFourthFirstBandTorus R)
          standardTwoTorusHomologyGenerator))) 0 = -12
  rw [R.twoDiscCover.ellipticInteriorEquiv_symm_bandInclusion,
    R.twoDiscCover.actualHomologyCoordinates_normalizedUnionHomologyTwoEquiv_canonicalBand_zero]
  change 12 * EllipticBandHomologyAlignment.bandTwo
      (D := R.twoDiscCover) (integralSingularHomologyMap 2 (normalizedFourthFirstBandTorus R)
        standardTwoTorusHomologyGenerator) 2 +
    2 * EllipticBandHomologyAlignment.bandTwo
      (D := R.twoDiscCover) (integralSingularHomologyMap 2 (normalizedFourthFirstBandTorus R)
        standardTwoTorusHomologyGenerator) 3 = -12
  rw [normalizedFourthFirstBandTorus_bandTwo R]
  norm_num [Pi.single_apply]
  decide

end SphereSixComplex.Geometry.PaperAnalyticData
