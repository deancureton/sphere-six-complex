module
public import SphereSixComplex.Paper.Topology.CuspFullIterateWangComparison
public import SphereSixComplex.Paper.Topology.CuspNormalizedBandMarking
public import SphereSixComplex.Paper.Topology.PaperRegularFiberTransport

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree SphereSixComplex.StandardTorusHomology
open SphereSixComplex.Periods ComplexTorus EllipticFamilySpecialization GlobalTorusFamily
open AnalyticTorusFamily TorusFamily
variable (A : AnalyticData)

private def torusTranslate (a : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    C(AdditiveTorus A.duplicatedSectionSevenBandParameter,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  ⟨fun z ↦ z + a, continuous_id.add continuous_const⟩

private def torusTranslateHomotopy
    (a : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    (ContinuousMap.id _).Homotopy (torusTranslate A a) where
  toFun p := p.2 + DescendedAffineTorusAutomorphism.translationPath a p.1
  continuous_toFun := continuous_snd.add
    ((DescendedAffineTorusAutomorphism.translationPath a).continuous.comp continuous_fst)
  map_zero_left z := by simp [Path.source]
  map_one_left z := by simp [torusTranslate, Path.target]

private def cuspTranslatedFixedFiberMap :
    C(AdditiveTorus A.duplicatedSectionSevenBandParameter, A.CentralFamily) :=
  (A.regularFixedFiberMap A.cuspRegularCoverPoint.1).comp
    (torusTranslate A (additiveTorusProjection A.duplicatedSectionSevenBandParameter
      (A.regularMovingToFixed A.cuspRegularCoverPoint.1 A.cuspRegularCoverPoint.2)))

private theorem cuspTranslatedFixedFiberMap_homotopic :
    (cuspTranslatedFixedFiberMap A).Homotopic
      (A.regularFixedFiberMap A.affineNormalizedMidpoint) := by
  have h := ContinuousMap.Homotopic.comp
    (.refl (A.regularFixedFiberMap A.cuspRegularCoverPoint.1))
    ⟨torusTranslateHomotopy A (additiveTorusProjection A.duplicatedSectionSevenBandParameter
      (A.regularMovingToFixed A.cuspRegularCoverPoint.1 A.cuspRegularCoverPoint.2))⟩
  exact h.symm.trans (A.regularFixedFiberMap_homotopic _ _)

private theorem cuspTranslatedFixedFiberMap_period (n : IntegerPeriods) (t : ℝ) :
    cuspTranslatedFixedFiberMap A
      (integerPeriodCircle A.duplicatedSectionSevenBandParameter
        A.duplicatedSectionSevenBandFullRank n (fun _ ↦ (t : UnitAddCircle))) =
    regularFamilyQuotientMap A.periods (projection (regularParameterMap A.periods)
      (A.cuspRegularCoverPoint.1,
        t • periodVector (regularParameterMap A.periods A.cuspRegularCoverPoint.1).1 n +
          A.cuspRegularCoverPoint.2)) := by
  rw [integerPeriodCircle_real]
  change A.regularFixedFiberPoint A.cuspRegularCoverPoint.1
    (additiveTorusProjection _ (t • periodVector _ n) + additiveTorusProjection _
      (A.regularMovingToFixed _ A.cuspRegularCoverPoint.2)) = _
  rw [← additiveTorusProjection_add]
  change A.centralQuotientProjection (projection (regularParameterMap A.periods)
    (A.cuspRegularCoverPoint.1, A.regularFixedToMoving _
      (t • periodVector _ n + A.regularMovingToFixed _ A.cuspRegularCoverPoint.2))) = _
  congr 2
  congr 1
  rw [← A.regularMovingToFixed_period_smul A.cuspRegularCoverPoint.1]
  have hadd : ∀ v w, A.regularMovingToFixed A.cuspRegularCoverPoint.1 (v + w) =
      A.regularMovingToFixed A.cuspRegularCoverPoint.1 v +
        A.regularMovingToFixed A.cuspRegularCoverPoint.1 w := by
    intro v w
    change (fullRankDomain _).realEquiv ((fullRankDomain _).realEquiv.symm (v + w)) = _
    rw [map_add, map_add]
    rfl
  rw [← hadd]
  exact A.regularFixedToMoving_regularMovingToFixed _ _

public theorem cuspCentralPeriodLoop_homology (n : IntegerPeriods) :
    loopHomologyClass (A.cuspCentralPeriodLoop n) =
      integralSingularHomologyMap 1
        ((A.regularFixedFiberMap A.affineNormalizedMidpoint).comp
          (integerPeriodCircle A.duplicatedSectionSevenBandParameter
            A.duplicatedSectionSevenBandFullRank n)) standardCircleHomologyGenerator := by
  let c := integerPeriodCircle A.duplicatedSectionSevenBandParameter
    A.duplicatedSectionSevenBandFullRank n
  have h := ContinuousMap.Homotopic.comp (cuspTranslatedFixedFiberMap_homotopic A) (.refl c)
  erw [← integralSingularHomologyMap_congr_of_homotopic 1 h]
  rw [standardCircleHomologyGenerator, integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_pointwise
  intro t
  change regularFamilyQuotientMap A.periods
    (regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint n t) =
      cuspTranslatedFixedFiberMap A (c (standardCirclePositiveLoop t))
  rw [regularFamilyPeriodLoop_apply]
  have hc : standardCirclePositiveLoop t = fun _ ↦ ((t : ℝ) : UnitAddCircle) := by
    ext i
    change ((((t : ℝ) * (1 : ℤ) : ℝ)) : UnitAddCircle) = ((t : ℝ) : UnitAddCircle)
    simp
  rw [hc]
  exact (cuspTranslatedFixedFiberMap_period A n t).symm

public theorem cuspTranslation_homology_image
    (D : A.EllipticTwoDiscCoverData) (n : IntegerPeriods) :
    integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
      (hurewiczFunction A.cuspOverlapBase
        (Additive.toMul (A.cuspAffineBridgeTranslation n))) =
    integralSingularHomologyMap 1 A.centralToEllipticInterior
      (loopHomologyClass (A.cuspCentralPeriodLoop n)) := by
  have hc : integralSingularHomologyMap 1 A.cuspOverlapToCentral
      (hurewiczFunction A.cuspOverlapBase
        (Additive.toMul (A.cuspAffineBridgeTranslation n))) =
      loopHomologyClass (A.cuspCentralPeriodLoop n) := by
    erw [← hurewiczFunction_map]
    change hurewiczFunction _ (Additive.toMul (A.cuspCentralTranslation n)) = _
    erw [A.cuspCentralTranslation_eq_periodLoop]
    rfl
  have he : A.centralToEllipticInterior.comp A.cuspOverlapToCentral =
      A.cuspOverlapToEllipticInterior := by
    ext1 x
    obtain ⟨q, rfl⟩ := A.cuspCollarToStarOverlapHomeomorph.surjective x
    have hh := ContinuousMap.congr_fun (A.cuspOverlapToInterior_comp_collar D) q
    change A.cuspOverlapToEllipticInterior
      (A.cuspCollarToStarOverlapHomeomorph q) = D.cuspToEllipticInteriorMap q at hh
    change A.centralToEllipticInterior
      (A.cuspOverlapToCentral (A.cuspCollarToStarOverlapHomeomorph q)) = _
    rw [hh]
    apply Eq.trans ?_ (cuspToEllipticInteriorMap_eq_central D q).symm
    apply congrArg A.centralToEllipticInterior
    change CuspPuncturedCollarBridge.puncturedLocalCuspQuotientMap A.starCuspWitness
      (A.cuspCollarToStarOverlapHomeomorph.symm (A.cuspCollarToStarOverlapHomeomorph q)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  erw [← hc, integralSingularHomologyMap_comp_wang, he]

public theorem cuspTranslation_homology_eq_band
    (R : A.AffineRadialCompletionInput) (n : IntegerPeriods) :
    integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
      (hurewiczFunction A.cuspOverlapBase
        (Additive.toMul (A.cuspAffineBridgeTranslation n))) =
    integralSingularHomologyMap 1 R.twoDiscCover.canonicalBandToEllipticInteriorInclusionMap
      (integralSingularHomologyMap 1 (normalizedMarkedPeriodBandCircle R n)
        standardCircleHomologyGenerator) := by
  erw [A.cuspTranslation_homology_image R.twoDiscCover,
    A.cuspCentralPeriodLoop_homology,
    integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
  apply congrArg (fun f : C(StdTorus 1, A.ellipticInterior) ↦
    integralSingularHomologyMap 1 f standardCircleHomologyGenerator)
  ext1 z
  change A.centralToEllipticInterior
      (A.regularFixedFiberPoint A.affineNormalizedMidpoint
        (integerPeriodCircle _ _ n z)) = (normalizedMarkedPeriodBandCircle R n z).1
  erw [normalizedMarkedPeriodBandCircle_interior]
  congr 1
  conv_lhs => erw [← A.affineNamedStripLift_apply_midpoint]
  exact A.normalizedMarkedPeriodCircle_central n z

public theorem cuspTranslation_ellipticCoordinate
    (R : A.AffineRadialCompletionInput) (n : IntegerPeriods) :
    R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment
      (integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase
          (Additive.toMul (A.cuspAffineBridgeTranslation n)))) = 12 * n 0 := by
  erw [A.cuspTranslation_homology_eq_band R n]
  let D := R.twoDiscCover
  let B := R.homologyAlignment.actualHomologyCoordinates
  let y := integralSingularHomologyMap 1 (normalizedMarkedPeriodBandCircle R n)
    standardCircleHomologyGenerator
  let eTop := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change B.normalizedUnionHomologyOneEquiv
      (eTop.symm (integralSingularHomologyMap 1
        D.canonicalBandToEllipticInteriorInclusionMap y)) 0 = 12 * n 0
  erw [D.ellipticInteriorEquiv_symm_bandInclusion,
    D.actualHomologyCoordinates_normalizedUnionHomologyOneEquiv_canonicalBand_zero]
  change 12 * EllipticBandHomologyAlignment.bandOne (D := D) y 0 = _
  erw [normalizedMarkedPeriodBandCircle_bandOne]

public theorem cuspDegreeOneFullIterateRelation_proved
    (R : A.AffineRadialCompletionInput) :
    EstablishedSectionSevenCuspTopology.ActualCuspDegreeOneIndexTwoFullIterateRelation R := by
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  apply (EstablishedSectionSevenCuspTopology.actualCuspDegreeOneIndexTwo_iff_fullIterateRelation R).mp
  let f := R.twoDiscCover.ellipticInteriorDegreeOneCoordinateHom R.homologyAlignment
  let y := integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
    (hurewiczFunction A.cuspOverlapBase
      (Additive.toMul (A.cuspAffineBridgeTranslation (Pi.single (0 : Fin 4) 1))))
  have hy : f y = 12 := by
    exact (A.cuspTranslation_ellipticCoordinate R (Pi.single (0 : Fin 4) 1)).trans
      (by norm_num)
  have hm := A.cuspRawTwo_homology_image R.twoDiscCover
  have hr := (congrArg (fun x ↦ (12 : ℤ) • x) hm).trans
    A.cuspOverlap_homology_fullIterate
  have h := congrArg f hr
  rw [map_zsmul] at h
  change (12 : ℤ) * f
    (integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
      (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1))) = f y at h
  rw [hy] at h
  change f
    (integralSingularHomologyMap 1 R.twoDiscCover.cuspMappingTorusToEllipticInteriorMap
      (A.actualCuspRadialClutchingData.geometricWangSections.circleMappingTorusHOneAddEquiv.symm
        (Pi.single (2 : Fin 3) 1))) = 1
  omega

end SphereSixComplex.Geometry.AnalyticData
end
