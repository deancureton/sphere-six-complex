module
public import SphereSixComplex.Paper.Topology.EllipticFourthHomologySweep
public import SphereSixComplex.Paper.Topology.CuspChosenThirdSweep
public import SphereSixComplex.Paper.Topology.CuspFourthSweepNormalization
public import SphereSixComplex.Prerequisites.Topology.PositiveCircleProductSwap
public import SphereSixComplex.Paper.Topology.CuspFullIterateWangComparison

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open SectionSevenEllipticTwoDiscCoverData CircleProductIdentityMappingTorus
open StandardCircleHomologyLiftDegree Hurewicz.Chains

public def actualCuspChosenFourthSweep (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) :=
  A.cuspFixedCircleSweepAnchors (cuspFourthFixedCircle (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness))) A.actualCuspChosenAnchor

public theorem cuspFourthSweep_homotopic_chosen (A : PaperAnalyticData) :
    (cuspFourthSweep A).Homotopic A.actualCuspChosenFourthSweep :=
  A.cuspFixedCircleSweep_homotopic_anchor _ _

public theorem actualCuspChosenFourthSweep_central_real (A : PaperAnalyticData)
    (r : ℝ) (t : UnitAddCircle) :
    A.starToCentral 0 (A.actualCuspChosenFourthSweep ((r : UnitAddCircle), fun _ ↦ t)) =
      regularPeriodCircleInGlobal A.periods (Pi.single 3 1)
        (t, A.actualCuspChosenPositiveRegularBase r) := by
  change A.starToCentral 0 (A.cuspFixedCircleSweepAnchors _ _ _) = _
  rw [cuspFixedCircleSweepAnchors_real]
  have hs : cuspParameterOfPolar ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖
      (r + A.actualCuspBoundaryCoverBase.1.2.re) = A.actualCuspBoundaryCoverBase.1.2 + r := by
    calc
      _ = cuspParameterOfPolar ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖
          A.actualCuspBoundaryCoverBase.1.2.re + r := by
        simp only [cuspParameterOfPolar_eq, Complex.ofReal_add]
        ring
      _ = _ := by rw [cuspParameterOfPolar_norm_cuspQ]
  change A.starToCentral 0 (actualCuspFullFibreSlice
    (cuspParameterOfPolar ‖cuspQ A.actualCuspBoundaryCoverBase.1.2‖
      (r + A.actualCuspBoundaryCoverBase.1.2.re)) _ _) = _
  erw [actualCuspFullFibreSlice_coordinateCircle_central A 3]
  apply congrArg (fun b ↦ regularPeriodCircleInGlobal A.periods (Pi.single 3 1) (t, b))
  apply Subtype.ext
  exact congrArg A.cuspCoordinate.lift hs

public def actualCuspChosenZeroCircle (A : PaperAnalyticData) : C(StdTorus 1,A.CentralFamily) :=
  (⟨A.starToCentral 0,(A.starToCentral_isOpenEmbedding 0).continuous⟩ : C(_, _)).comp
    (A.actualCuspChosenFourthSweep.comp
      ⟨fun z ↦ (z 0,0), (continuous_apply 0).prodMk continuous_const⟩)

public theorem centralFourthTranslation_regular_zero (A : PaperAnalyticData)
    (t : UnitAddCircle) (b : RegularBase (U := A.paperTriangleUniformization)) :
    A.centralFourthTranslation (t,regularPeriodCircleInGlobal A.periods (Pi.single 3 1) (0,b)) =
      regularPeriodCircleInGlobal A.periods (Pi.single 3 1) (t,b) := by
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective t
  change invariantPeriodCircleTranslation _ _ _ _ = _
  rw [invariantPeriodCircleTranslation_real]
  change invariantPeriodRealTranslation _ _ _
    (r,Quotient.mk _ (regularPeriodCircle _ _ ((0 : ℝ),b))) = _
  rw [regularPeriodCircle_real, invariantPeriodRealTranslation_mk]
  change Quotient.mk _ (regularPeriodTranslation _ _
    (r,Quotient.mk _ (b,(0 : ℝ) • periodVector _ _))) = _
  rw [regularPeriodTranslation_mk]
  change Quotient.mk _ (projection _ (b,r • periodVector _ ![0,0,0,1] +
    (0 : ℝ) • periodVector _ (Pi.single 3 1))) =
    Quotient.mk _ (regularPeriodCircle _ _ ((r : UnitAddCircle),b))
  rw [regularPeriodCircle_real, zero_smul, add_zero]
  rfl

public theorem actualCuspChosenFourthSweep_action (A : PaperAnalyticData)
    (u t : UnitAddCircle) :
    A.centralFourthTranslation (t,A.actualCuspChosenZeroCircle (fun _ ↦ u)) =
      A.starToCentral 0 (A.actualCuspChosenFourthSweep (u,fun _ ↦ t)) := by
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective u
  change A.centralFourthTranslation
    (t,A.starToCentral 0 (A.actualCuspChosenFourthSweep ((r : UnitAddCircle),0))) = _
  rw [show (0 : StdTorus 1) = (fun _ ↦ (0 : UnitAddCircle)) from rfl,
    actualCuspChosenFourthSweep_central_real, actualCuspChosenFourthSweep_central_real]
  exact A.centralFourthTranslation_regular_zero t _

public theorem actualCuspChosenZeroCircle_negative (A : PaperAnalyticData) (t : unitInterval) :
    A.actualCuspChosenZeroCircle (fun _ ↦ ((-(t : ℝ) : ℝ) : UnitAddCircle)) =
      A.cuspAngularZeroSectionLoop t := by
  change A.starToCentral 0 (A.actualCuspChosenFourthSweep
    (((-(t : ℝ) : ℝ) : UnitAddCircle),fun _ ↦ 0)) = _
  rw [actualCuspChosenFourthSweep_central_real,
    cuspAngularZeroSectionLoop_apply]
  change Quotient.mk _ (regularPeriodCircle _ _ ((0 : ℝ),_)) = _
  rw [regularPeriodCircle_real]
  change A.centralQuotientProjection (projection _ (_, (0 : ℝ) • periodVector _ _)) = _
  rw [zero_smul]
  congr 2
  apply Prod.ext
  · apply Subtype.ext
    change A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 + ↑(-(t : ℝ))) =
      A.cuspCoordinate.lift (A.actualCuspBoundaryCoverBase.1.2 - ↑(t : ℝ))
    simp only [Complex.ofReal_neg, sub_eq_add_neg]
  · rfl

public theorem loopHomologyClass_symm_eq_neg {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) : loopHomologyClass p.symm = -loopHomologyClass p := by
  change hurewiczPi1 x (Additive.ofMul (show FundamentalGroup X x from Path.Homotopic.Quotient.mk p)⁻¹) = _
  exact map_inv (hurewiczPi1 x) (show FundamentalGroup X x from Path.Homotopic.Quotient.mk p)

public theorem actualCuspChosenZeroCircle_homology (A : PaperAnalyticData) :
    integralSingularHomologyMap 1 A.actualCuspChosenZeroCircle standardCircleHomologyGenerator =
      -loopHomologyClass A.cuspAngularZeroSectionLoop := by
  have h : loopHomologyClass
      (standardCirclePositiveLoop.symm.map A.actualCuspChosenZeroCircle.continuous) =
      loopHomologyClass A.cuspAngularZeroSectionLoop := by
    apply loopHomologyClass_eq_of_pointwise
    intro t
    change A.actualCuspChosenZeroCircle (fun _ ↦
      ((((1 : ℝ) - (t : ℝ)) * ((1 : ℤ) : ℝ) : ℝ) : UnitAddCircle)) = _
    rw [Int.cast_one, mul_one, show (((1 : ℝ) - (t : ℝ) : ℝ) : UnitAddCircle) =
        ((-(t : ℝ) : ℝ) : UnitAddCircle) by
      rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, AddCircle.coe_neg]]
    exact A.actualCuspChosenZeroCircle_negative t
  rw [← integralSingularHomologyMap_loopHomologyClass, loopHomologyClass_symm_eq_neg,
    map_neg] at h
  change integralSingularHomologyMap 1 A.actualCuspChosenZeroCircle
    (loopHomologyClass standardCirclePositiveLoop) = _
  exact neg_eq_iff_eq_neg.mp h

public theorem cuspAngularCentralLoop_homology_zero (A : PaperAnalyticData) :
    loopHomologyClass A.cuspAngularCentralLoop =
      loopHomologyClass A.cuspAngularZeroSectionLoop := by
  have h := A.cuspAngularCentralLoop_class_eq_zeroSectionWhisker
  have he := congrArg (fun p ↦ hurewiczPi1 A.actualCuspCentralBase (Additive.ofMul p)) h
  change loopHomologyClass A.cuspAngularCentralLoop = _ at he
  exact he.trans (loopHomologyClass_whisker _ _)

public def actualCuspChosenZeroCircleInterior (A : PaperAnalyticData) :
    C(StdTorus 1,A.SectionSevenEllipticInterior) :=
  A.fourthTranslationCentralInclusion.comp A.actualCuspChosenZeroCircle

public theorem actualCuspChosenZeroCircleInterior_homology (A : PaperAnalyticData)
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    integralSingularHomologyMap 1 A.actualCuspChosenZeroCircleInterior
      standardCircleHomologyGenerator =
    -integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
      (hurewiczFunction A.actualCuspOverlapBase A.actualCuspAffineBridgeMeridian) := by
  rw [actualCuspChosenZeroCircleInterior, ← integralSingularHomologyMap_comp_wang,
    actualCuspChosenZeroCircle_homology, map_neg,
    A.actualCuspBridgeMeridian_homology_image D,
    ← A.cuspAngularCentralLoop_homology_zero]
  congr 1
  erw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_pointwise
  intro t
  apply Subtype.ext
  change (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
    (A.actualCuspOverlapToCentral (A.cuspAngularProjectedLoop t))).val = _
  erw [A.centralToSectionSevenEulerPieceHomeomorph_actualCuspOverlapToCentral]
  rfl

public theorem actualCuspChosenFourthSweep_action_interior (A : PaperAnalyticData)
    (D : A.SectionSevenEllipticTwoDiscCoverData) (p : UnitAddCircle × StdTorus 1) :
    A.ellipticFourthTranslation (p.1,A.actualCuspChosenZeroCircleInterior p.2) =
      D.cuspToEllipticInteriorMap.hom
        (A.actualCuspChosenFourthSweep (p.2 0,fun _ ↦ p.1)) := by
  change A.ellipticFourthTranslation
    (p.1,A.fourthTranslationCentralInclusion (A.actualCuspChosenZeroCircle p.2)) = _
  rw [ellipticFourthTranslation_central]
  have hp : p.2 = (fun _ ↦ p.2 0) := by ext i; fin_cases i; rfl
  rw [hp, actualCuspChosenFourthSweep_action]
  rfl

public theorem actualCuspChosenFourthSweep_homology (A : PaperAnalyticData) :
    integralSingularHomologyMap 2 A.actualCuspChosenFourthSweep
      PositiveCircleCross.positiveCircleProductGenerator =
      A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) := by
  rw [← A.cuspFourthSweepClass_eq_rawFive]
  change integralSingularHomologyMap 2 A.actualCuspChosenFourthSweep _ =
    integralSingularHomologyMap 2 (cuspFourthSweep A) _
  have h := SphereSixComplex.integralSingularHomologyMap_eq_of_homotopic
    A.cuspFourthSweep_homotopic_chosen 2
  exact (congrArg (fun f ↦ f.hom PositiveCircleCross.positiveCircleProductGenerator) h).symm

public theorem ellipticFourthHomologySweep_cusp (A : PaperAnalyticData)
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    A.ellipticFourthHomologySweep
      (-integralSingularHomologyMap 1 A.actualCuspOverlapToEllipticInterior
        (hurewiczFunction A.actualCuspOverlapBase A.actualCuspAffineBridgeMeridian)) =
      -integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) := by
  rw [← A.actualCuspChosenZeroCircleInterior_homology D]
  change integralSingularHomologyMap 2 A.ellipticFourthTranslation
    (normalizedCircleCross 1 (integralSingularHomologyMap 1
      A.actualCuspChosenZeroCircleInterior standardCircleHomologyGenerator)) = _
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 A.ellipticFourthTranslation
    (integralSingularHomologyMap 2
      (PositiveCircleCross.circleProductMap A.actualCuspChosenZeroCircleInterior)
      PositiveCircleCross.positiveCircleProductGenerator) = _
  rw [integralSingularHomologyMap_comp_wang]
  have he : A.ellipticFourthTranslation.comp
      (PositiveCircleCross.circleProductMap A.actualCuspChosenZeroCircleInterior) =
      D.cuspToEllipticInteriorMap.hom.comp (A.actualCuspChosenFourthSweep.comp
        PositiveCircleCross.positiveCircleProductSwap) := by
    ext1 p
    exact A.actualCuspChosenFourthSweep_action_interior D p
  rw [he, ← integralSingularHomologyMap_comp_wang,
    ← integralSingularHomologyMap_comp_wang,
    PositiveCircleCross.positiveCircleProductSwap_generator,
    map_neg, map_neg, actualCuspChosenFourthSweep_homology]

end SphereSixComplex.Geometry.PaperAnalyticData
