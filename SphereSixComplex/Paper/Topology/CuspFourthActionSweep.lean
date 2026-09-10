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
open EllipticTwoDiscCoverData CircleProductIdentityMappingTorus
open StandardCircleHomologyLiftDegree Hurewicz.Chains

public def cuspChosenFourthSweep (A : PaperAnalyticData) :
    C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0) :=
  A.cuspFixedCircleSweepAnchors (cuspFourthFixedCircle (cuspBasePoint A.cuspCoordinate
    (markedCuspParameter A.starCuspWitness))) A.cuspChosenAnchor

public theorem cuspFourthSweep_homotopic_chosen (A : PaperAnalyticData) :
    (cuspFourthSweep A).Homotopic A.cuspChosenFourthSweep :=
  A.cuspFixedCircleSweep_homotopic_anchor _ _

public theorem cuspChosenFourthSweep_central_real (A : PaperAnalyticData)
    (r : ℝ) (t : UnitAddCircle) :
    A.starToCentral 0 (A.cuspChosenFourthSweep ((r : UnitAddCircle), fun _ ↦ t)) =
      regularPeriodCircleInGlobal A.periods (Pi.single 3 1)
        (t, A.cuspChosenPositiveRegularBase r) := by
  change A.starToCentral 0 (A.cuspFixedCircleSweepAnchors _ _ _) = _
  rw [cuspFixedCircleSweepAnchors_real]
  have hs : cuspParameterOfPolar ‖cuspQ A.cuspBoundaryCoverBase.1.2‖
      (r + A.cuspBoundaryCoverBase.1.2.re) = A.cuspBoundaryCoverBase.1.2 + r := by
    calc
      _ = cuspParameterOfPolar ‖cuspQ A.cuspBoundaryCoverBase.1.2‖
          A.cuspBoundaryCoverBase.1.2.re + r := by
        simp only [cuspParameterOfPolar_eq, Complex.ofReal_add]
        ring
      _ = _ := by rw [cuspParameterOfPolar_norm_cuspQ]
  change A.starToCentral 0 (actualCuspFullFibreSlice
    (cuspParameterOfPolar ‖cuspQ A.cuspBoundaryCoverBase.1.2‖
      (r + A.cuspBoundaryCoverBase.1.2.re)) _ _) = _
  erw [cuspFullFibreSlice_coordinateCircle_central A 3]
  apply congrArg (fun b ↦ regularPeriodCircleInGlobal A.periods (Pi.single 3 1) (t, b))
  apply Subtype.ext
  exact congrArg A.cuspCoordinate.lift hs

public def cuspChosenZeroCircle (A : PaperAnalyticData) : C(StdTorus 1,A.CentralFamily) :=
  (⟨A.starToCentral 0,(A.starToCentral_isOpenEmbedding 0).continuous⟩ : C(_, _)).comp
    (A.cuspChosenFourthSweep.comp
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

public theorem cuspChosenFourthSweep_action (A : PaperAnalyticData)
    (u t : UnitAddCircle) :
    A.centralFourthTranslation (t,A.cuspChosenZeroCircle (fun _ ↦ u)) =
      A.starToCentral 0 (A.cuspChosenFourthSweep (u,fun _ ↦ t)) := by
  obtain ⟨r,rfl⟩ := QuotientAddGroup.mk_surjective u
  change A.centralFourthTranslation
    (t,A.starToCentral 0 (A.cuspChosenFourthSweep ((r : UnitAddCircle),0))) = _
  rw [show (0 : StdTorus 1) = (fun _ ↦ (0 : UnitAddCircle)) from rfl,
    cuspChosenFourthSweep_central_real, cuspChosenFourthSweep_central_real]
  exact A.centralFourthTranslation_regular_zero t _

public theorem cuspChosenZeroCircle_negative (A : PaperAnalyticData) (t : unitInterval) :
    A.cuspChosenZeroCircle (fun _ ↦ ((-(t : ℝ) : ℝ) : UnitAddCircle)) =
      A.cuspAngularZeroSectionLoop t := by
  change A.starToCentral 0 (A.cuspChosenFourthSweep
    (((-(t : ℝ) : ℝ) : UnitAddCircle),fun _ ↦ 0)) = _
  rw [cuspChosenFourthSweep_central_real,
    cuspAngularZeroSectionLoop_apply]
  change Quotient.mk _ (regularPeriodCircle _ _ ((0 : ℝ),_)) = _
  rw [regularPeriodCircle_real]
  change A.centralQuotientProjection (projection _ (_, (0 : ℝ) • periodVector _ _)) = _
  rw [zero_smul]
  congr 2
  apply Prod.ext
  · apply Subtype.ext
    change A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 + ↑(-(t : ℝ))) =
      A.cuspCoordinate.lift (A.cuspBoundaryCoverBase.1.2 - ↑(t : ℝ))
    simp only [Complex.ofReal_neg, sub_eq_add_neg]
  · rfl

public theorem loopHomologyClass_symm_eq_neg {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) : loopHomologyClass p.symm = -loopHomologyClass p := by
  change hurewiczPi1 x (Additive.ofMul (show FundamentalGroup X x from Path.Homotopic.Quotient.mk p)⁻¹) = _
  exact map_inv (hurewiczPi1 x) (show FundamentalGroup X x from Path.Homotopic.Quotient.mk p)

public theorem cuspChosenZeroCircle_homology (A : PaperAnalyticData) :
    integralSingularHomologyMap 1 A.cuspChosenZeroCircle standardCircleHomologyGenerator =
      -loopHomologyClass A.cuspAngularZeroSectionLoop := by
  have h : loopHomologyClass
      (standardCirclePositiveLoop.symm.map A.cuspChosenZeroCircle.continuous) =
      loopHomologyClass A.cuspAngularZeroSectionLoop := by
    apply loopHomologyClass_eq_of_pointwise
    intro t
    change A.cuspChosenZeroCircle (fun _ ↦
      ((((1 : ℝ) - (t : ℝ)) * ((1 : ℤ) : ℝ) : ℝ) : UnitAddCircle)) = _
    rw [Int.cast_one, mul_one, show (((1 : ℝ) - (t : ℝ) : ℝ) : UnitAddCircle) =
        ((-(t : ℝ) : ℝ) : UnitAddCircle) by
      rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, AddCircle.coe_neg]]
    exact A.cuspChosenZeroCircle_negative t
  rw [← integralSingularHomologyMap_loopHomologyClass, loopHomologyClass_symm_eq_neg,
    map_neg] at h
  change integralSingularHomologyMap 1 A.cuspChosenZeroCircle
    (loopHomologyClass standardCirclePositiveLoop) = _
  exact neg_eq_iff_eq_neg.mp h

public theorem cuspAngularCentralLoop_homology_zero (A : PaperAnalyticData) :
    loopHomologyClass A.cuspAngularCentralLoop =
      loopHomologyClass A.cuspAngularZeroSectionLoop := by
  have h := A.cuspAngularCentralLoop_class_eq_zeroSectionWhisker
  have he := congrArg (fun p ↦ hurewiczPi1 A.cuspCentralBase (Additive.ofMul p)) h
  change loopHomologyClass A.cuspAngularCentralLoop = _ at he
  exact he.trans (loopHomologyClass_whisker _ _)

public def cuspChosenZeroCircleInterior (A : PaperAnalyticData) :
    C(StdTorus 1,A.ellipticInterior) :=
  A.fourthTranslationCentralInclusion.comp A.cuspChosenZeroCircle

public theorem cuspChosenZeroCircleInterior_homology (A : PaperAnalyticData)
    (D : A.EllipticTwoDiscCoverData) :
    integralSingularHomologyMap 1 A.cuspChosenZeroCircleInterior
      standardCircleHomologyGenerator =
    -integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
      (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian) := by
  rw [cuspChosenZeroCircleInterior, ← integralSingularHomologyMap_comp_wang,
    cuspChosenZeroCircle_homology, map_neg,
    A.cuspBridgeMeridian_homology_image D,
    ← A.cuspAngularCentralLoop_homology_zero]
  congr 1
  erw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass]
  apply loopHomologyClass_eq_of_pointwise
  intro t
  apply Subtype.ext
  change (A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
    (A.cuspOverlapToCentral (A.cuspAngularProjectedLoop t))).val = _
  erw [A.centralToSectionSevenEulerPieceHomeomorph_cuspOverlapToCentral]
  rfl

public theorem cuspChosenFourthSweep_action_interior (A : PaperAnalyticData)
    (D : A.EllipticTwoDiscCoverData) (p : UnitAddCircle × StdTorus 1) :
    A.ellipticFourthTranslation (p.1,A.cuspChosenZeroCircleInterior p.2) =
      D.cuspToEllipticInteriorMap.hom
        (A.cuspChosenFourthSweep (p.2 0,fun _ ↦ p.1)) := by
  change A.ellipticFourthTranslation
    (p.1,A.fourthTranslationCentralInclusion (A.cuspChosenZeroCircle p.2)) = _
  rw [ellipticFourthTranslation_central]
  have hp : p.2 = (fun _ ↦ p.2 0) := by ext i; fin_cases i; rfl
  rw [hp, cuspChosenFourthSweep_action]
  rfl

public theorem cuspChosenFourthSweep_homology (A : PaperAnalyticData) :
    integralSingularHomologyMap 2 A.cuspChosenFourthSweep
      PositiveCircleCross.positiveCircleProductGenerator =
      A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1) := by
  rw [← A.cuspFourthSweepClass_eq_rawFive]
  change integralSingularHomologyMap 2 A.cuspChosenFourthSweep _ =
    integralSingularHomologyMap 2 (cuspFourthSweep A) _
  have h := SphereSixComplex.integralSingularHomologyMap_eq_of_homotopic
    A.cuspFourthSweep_homotopic_chosen 2
  exact (congrArg (fun f ↦ f.hom PositiveCircleCross.positiveCircleProductGenerator) h).symm

public theorem ellipticFourthHomologySweep_cusp (A : PaperAnalyticData)
    (D : A.EllipticTwoDiscCoverData) :
    A.ellipticFourthHomologySweep
      (-integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian)) =
      -integralSingularHomologyMap 2 D.cuspToEllipticInteriorMap.hom
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1)) := by
  rw [← A.cuspChosenZeroCircleInterior_homology D]
  change integralSingularHomologyMap 2 A.ellipticFourthTranslation
    (normalizedCircleCross 1 (integralSingularHomologyMap 1
      A.cuspChosenZeroCircleInterior standardCircleHomologyGenerator)) = _
  rw [← positiveCircleCross_eq_normalized]
  change integralSingularHomologyMap 2 A.ellipticFourthTranslation
    (integralSingularHomologyMap 2
      (PositiveCircleCross.circleProductMap A.cuspChosenZeroCircleInterior)
      PositiveCircleCross.positiveCircleProductGenerator) = _
  rw [integralSingularHomologyMap_comp_wang]
  have he : A.ellipticFourthTranslation.comp
      (PositiveCircleCross.circleProductMap A.cuspChosenZeroCircleInterior) =
      D.cuspToEllipticInteriorMap.hom.comp (A.cuspChosenFourthSweep.comp
        PositiveCircleCross.positiveCircleProductSwap) := by
    ext1 p
    exact A.cuspChosenFourthSweep_action_interior D p
  rw [he, ← integralSingularHomologyMap_comp_wang,
    ← integralSingularHomologyMap_comp_wang,
    PositiveCircleCross.positiveCircleProductSwap_generator,
    map_neg, map_neg, cuspChosenFourthSweep_homology]

end SphereSixComplex.Geometry.PaperAnalyticData
