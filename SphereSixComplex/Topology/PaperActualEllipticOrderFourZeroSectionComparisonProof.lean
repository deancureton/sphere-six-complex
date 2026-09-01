module

public import SphereSixComplex.Topology.PaperActualEllipticOrderFourFactorComparisonProof
public import SphereSixComplex.Topology.FreeLoopChangeBasepointHomotopy

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open SphereSixComplex.Geometry
open SphereSixComplex.Periods
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

private theorem orderFourCayleyChartRadialHomotopy_trace
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) (s : unitInterval) :
    A.orderFourCayleyChartRadialHomotopy c hc hc1 (s, 0) =
      A.orderFourCayleyChartRadialHomotopy c hc hc1 (s, 1) := by
  apply Subtype.ext
  change ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint
        (A.orderFourAlignedCayleyRadialPoint c (s, 0)) - 1 =
    ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint
        (A.orderFourAlignedCayleyRadialPoint c (s, 1)) - 1
  congr 2
  unfold orderFourAlignedCayleyRadialPoint
  rw [show localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue 0 =
      localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue 1 by
    unfold localDegreeCirclePoint
    norm_num]

private theorem exactLocalFactorizationCircleHomotopyTwoPunctures_trace
    (u : ℂ → ℂ) (n : ℕ) (a b : ℂ) (ha : a ≠ 0)
    (hu : ContinuousOn u (Metric.closedBall (0 : ℂ) ‖a‖))
    (hune : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖a‖, u z ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ n * ‖u z‖ < ‖b‖)
    (s : unitInterval) :
    exactLocalFactorizationCircleHomotopyTwoPunctures
        u n a b ha hu hune hbound (s, 0) =
      exactLocalFactorizationCircleHomotopyTwoPunctures
        u n a b ha hu hune hbound (s, 1) := by
  apply Subtype.ext
  change localDegreeCirclePoint a 0 ^ n * u (localDegreeRadialPoint a (s, 0)) =
    localDegreeCirclePoint a 1 ^ n * u (localDegreeRadialPoint a (s, 1))
  rw [show localDegreeCirclePoint a 0 = localDegreeCirclePoint a 1 by
    unfold localDegreeCirclePoint
    norm_num]
  congr 2
  unfold localDegreeRadialPoint
  rw [show localDegreeCirclePoint a 0 = localDegreeCirclePoint a 1 by
    unfold localDegreeCirclePoint
    norm_num]

private theorem positiveOneQuadrupleCoefficientHomotopy_trace
    (d : ℂ) (hd : d ≠ 0) (hd1 : ‖d‖ < 1) (s : unitInterval) :
    positiveOneQuadrupleCoefficientHomotopy d hd hd1 (s, 0) =
      positiveOneQuadrupleCoefficientHomotopy d hd hd1 (s, 1) := by
  apply Subtype.ext
  change positiveOneQuadrupleCoefficientHomotopyValue d (s, 0) =
    positiveOneQuadrupleCoefficientHomotopyValue d (s, 1)
  unfold positiveOneQuadrupleCoefficientHomotopyValue
  norm_num
  have he : Complex.exp ((2 : ℂ) * Real.pi * 4 * Complex.I) = 1 := by
    rw [show (2 : ℂ) * Real.pi * 4 * Complex.I =
      (4 : ℕ) * (2 * Real.pi * Complex.I) by norm_num; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I 4
  rw [he, mul_one]

private theorem orderFourActualCayleyBaseCoordinate_quadrupleHomotopy_with_trace :
    ∃ H : ContinuousMap.Homotopy
        (twoPunctureComplementNegOneMap.comp
          (A.orderFourCayleyChartSubOneCircleMap
            A.orderFourFillingRelationCayleyBaseValue
            (norm_pos_iff.mpr A.orderFourFillingRelationCayleyBaseValue_ne_zero)
            (by
              rw [A.orderFourFillingRelationCayleyBaseValue_norm]
              exact A.orderFourActualEllipticBoundaryBase.1.2.2)))
        twicePuncturedCounterclockwiseOneQuadruple.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  obtain ⟨u, a, c, hc, hc1, haeq, hu, hune, hfac, hbound⟩ :=
    A.exists_orderFourCayleyBaseCoordinate_alignedSmallCircleData
  subst a
  let a : ℂ := (c : ℂ) * A.orderFourFillingRelationCayleyBaseValue
  have ha : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
      A.orderFourFillingRelationCayleyBaseValue_ne_zero
  have hbound' : ∀ z ∈ Metric.closedBall (0 : ℂ) ‖a‖,
      ‖a‖ ^ 4 * ‖u z‖ < ‖(-1 : ℂ)‖ := by
    simpa [a] using hbound
  have har : ‖a‖ < A.starSeparation.orderFour.radius := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_lt_mul_of_pos_right hc1
      (norm_pos_iff.mpr
        A.orderFourFillingRelationCayleyBaseValue_ne_zero)).trans (by
          rw [A.orderFourFillingRelationCayleyBaseValue_norm]
          simpa using A.orderFourActualEllipticBoundaryBase.1.2.2)
  have hsmall :
      A.orderFourCayleyChartSubOneCircleMap a (norm_pos_iff.mpr ha) har =
        factorizedLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hu hune hbound' := by
    ext t
    change ellipticChartFunction A.modular.sourceCoordinate.coordinate
          fuchsianTwoFixedPoint (localDegreeCirclePoint a t) - 1 =
      localDegreeCirclePoint a t ^ 4 * u (localDegreeCirclePoint a t)
    exact hfac _ (by
      rw [Metric.mem_closedBall, dist_zero_right, localDegreeCirclePoint_norm])
  let Hrad := A.orderFourCayleyChartRadialHomotopy c hc hc1
  have htarget :
      A.orderFourCayleyChartSubOneCircleMap
          ((c : ℂ) * A.orderFourFillingRelationCayleyBaseValue)
          (by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact mul_pos hc
              (norm_pos_iff.mpr
                A.orderFourFillingRelationCayleyBaseValue_ne_zero))
          (by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            exact (mul_lt_mul_of_pos_right hc1
              (norm_pos_iff.mpr
                A.orderFourFillingRelationCayleyBaseValue_ne_zero)).trans (by
                  rw [A.orderFourFillingRelationCayleyBaseValue_norm]
                  simpa using A.orderFourActualEllipticBoundaryBase.1.2.2)) =
        factorizedLocalDegreeCircleTwoPunctures
          u 4 a (-1) ha hu hune hbound' := by
    exact hsmall
  let Hlocal := exactLocalFactorizationCircleHomotopyTwoPunctures
    u 4 a (-1) ha hu hune hbound'
  let Hfirst := (Hrad.cast rfl htarget).trans Hlocal
  have hHfirst : ∀ s : unitInterval, Hfirst (s, 0) = Hfirst (s, 1) := by
    intro s
    apply freeLoopHomotopyTrans_trace
    · intro r
      exact A.orderFourCayleyChartRadialHomotopy_trace c hc hc1 r
    · intro r
      exact exactLocalFactorizationCircleHomotopyTwoPunctures_trace
        u 4 a (-1) ha hu hune hbound' r
  let Hmap := twoPunctureComplementNegOneHomotopyMap Hfirst
  let d : ℂ := a ^ 4 * u 0
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 ‖a‖ := by
    rw [Metric.mem_closedBall, dist_self]
    exact norm_nonneg a
  have hd : d ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 ha) (hune 0 hzero)
  have hd1 : ‖d‖ < 1 := by
    dsimp [d]
    rw [norm_mul, norm_pow]
    simpa using hbound' 0 hzero
  have hfrozen :
      twoPunctureComplementNegOneMap.comp
          (frozenLocalDegreeCircleTwoPunctures
            u 4 a (-1) ha hune hbound') =
        twicePuncturedPositiveOneQuadrupleCircle d hd hd1 := by
    simpa [d] using
      frozenLocalDegreeCircleTwoPunctures_map_eq_positiveOneQuadruple
        u a ha hune hbound'
  let Hcoefficient := positiveOneQuadrupleCoefficientHomotopy d hd hd1
  let H := (Hmap.cast rfl hfrozen).trans Hcoefficient
  refine ⟨H, ?_⟩
  intro s
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact congrArg twoPunctureComplementNegOneHomeomorph (hHfirst r)
  · intro r
    exact positiveOneQuadrupleCoefficientHomotopy_trace d hd hd1 r

/-- The restricted order-four inverse chart has the product coordinate with which it was fed. -/
public theorem orderFourPuncturedProductToRegularMap_productCoordinate
    (zq : A.OrderFourCayleyPuncturedDisc × A.orderFourTorus) :
    letI := A.orderFourActualEllipticBoundaryAction
    orderFourRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderFourPuncturedProductToRegularMap
            (A.orderFourPuncturedProductCarrierMap zq))) = (zq.1.1, zq.2) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let q := (orderFourPuncturedProductHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
    A.starSeparation.orderFour.radius_lt_one).symm
      (A.orderFourPuncturedProductCarrierMap zq)
  have hmap : A.orderFourPuncturedProductToRegularMap
      (A.orderFourPuncturedProductCarrierMap zq) =
      orderFourCollarToRegular A.periods hproper
        A.starSeparation.orderFour.sourceData q := by rfl
  rw [hmap]
  have hinc := regularFamilyInclusion_orderFourCollarToRegular A.periods hproper
    A.starSeparation.orderFour.sourceData q
  rw [hinc]
  exact congrArg Subtype.val
    ((orderFourPuncturedProductHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).apply_symm_apply
        (A.orderFourPuncturedProductCarrierMap zq))

/-- A zero torus coordinate in the order-four restricted chart is the regular-family zero
section over the base of the realized point. -/
public theorem orderFourPuncturedProductToRegularMap_zero_eq_zeroSection
    (z : A.OrderFourCayleyPuncturedDisc) :
    letI := A.orderFourActualEllipticBoundaryAction
    let x := A.orderFourPuncturedProductToRegularMap
      (A.orderFourPuncturedProductCarrierMap (z, 0))
    x = regularFamilyZeroSection A.periods
      (regularTotalSpaceBase A.periods x) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let x := A.orderFourPuncturedProductToRegularMap
    (A.orderFourPuncturedProductCarrierMap (z, 0))
  have hcoord := A.orderFourPuncturedProductToRegularMap_productCoordinate (z, 0)
  have hbase := congrArg Prod.fst hcoord
  rw [orderFourRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hbase
  apply regularFamilyInclusion_injective A.periods
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  rw [hcoord]
  simp only [regularFamilyZeroSection_apply, regularFamilyInclusion_mk,
    regularBundleInclusion, orderFourRealPeriodProductHomeomorph_mk]
  apply Prod.ext
  · exact hbase.symm
  · simp only [movingToFixedCover, periodCoordinates, map_zero]
    exact (additiveTorus_mk_zero _).symm

/-- The zero-fibre local realization is the global zero-section lift of the same order-four
Cayley base loop. -/
public theorem orderFourCentralZeroFibreBasePath_eq_zeroSectionBasePath :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourCentralZeroFibreBasePath.toContinuousMap =
      A.orderFourZeroSectionBaseMap := by
  let _ := A.orderFourActualEllipticBoundaryAction
  ext t
  let z := A.orderFourFillingRelationCayleyPuncturedLoop t
  let x := A.orderFourPuncturedProductToRegularMap
    (A.orderFourPuncturedProductCarrierMap (z, 0))
  let b := regularTotalSpaceBase A.periods x
  have hxzero : x = regularFamilyZeroSection A.periods b := by
    exact A.orderFourPuncturedProductToRegularMap_zero_eq_zeroSection z
  have hlocal : A.orderFourCentralZeroFibreBasePath t =
      A.centralZeroSection (regularBaseQuotientMap b) := by
    change A.centralQuotientProjection x =
      puncturedGlobalZeroSection A.periods (regularBaseQuotientMap b)
    rw [hxzero, puncturedGlobalZeroSection_mk]
    rfl
  change A.orderFourCentralZeroFibreBasePath t = A.orderFourZeroSectionBaseMap t
  rw [hlocal]
  change A.centralZeroSection (regularBaseQuotientMap b) =
    A.centralZeroSection
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (A.orderFourFillingRelationBaseCoordinateMap t))
  apply congrArg A.centralZeroSection
  apply A.puncturedBaseHomeomorphTwicePuncturedComplex.injective
  rw [puncturedBaseHomeomorphTwicePuncturedComplex_mk,
    A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply]
  apply Subtype.ext
  rw [A.orderFourFillingRelationBaseCoordinateMap_eq_cayley]
  change A.modular.sourceCoordinate.coordinate b.1 =
    (ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianTwoFixedPoint
      (localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue t) - 1) + 1
  rw [sub_add_cancel]
  rw [← A.orderFourCayleyRegularCoordinate_chartFunction b.1]
  apply congrArg (ellipticChartFunction A.modular.sourceCoordinate.coordinate
    fuchsianTwoFixedPoint)
  have hcoord := A.orderFourPuncturedProductToRegularMap_productCoordinate (z, 0)
  have hbase := congrArg Prod.fst hcoord
  rw [orderFourRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hbase
  calc
    ((orderFourCayleyHomeomorph b.1 :
        SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) =
        ((z.1 : SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) :=
      congrArg (fun w : SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc ↦
        (w : ℂ)) hbase
    _ = localDegreeCirclePoint A.orderFourFillingRelationCayleyBaseValue t := by
      simp [z, orderFourFillingRelationCayleyPuncturedLoop,
        orderFourFillingRelationCayleyDiscLoop,
        orderFourFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
        puncturedComplexIntegerCirclePoint]
      unfold localDegreeCirclePoint
      congr 2

/-- The zero-section lift of the quartic base homotopy has equal endpoint traces. -/
public theorem orderFourZeroSectionBase_quadrupleHomotopy_with_trace :
    ∃ H : ContinuousMap.Homotopy A.orderFourZeroSectionBaseMap
        A.orderFourZeroSectionQuadruplePath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  rcases A.orderFourActualCayleyBaseCoordinate_quadrupleHomotopy_with_trace with
    ⟨H, htrace⟩
  let H' := H.cast A.orderFourFillingRelationBaseCoordinateMap_eq_cayley.symm rfl
  let K : ContinuousMap.Homotopy A.orderFourZeroSectionBaseMap
      A.orderFourZeroSectionQuadruplePath.toContinuousMap :=
    { toFun := fun st ↦ A.markedBaseToCentralZeroSection (H' st)
      continuous_toFun := A.markedBaseToCentralZeroSection.continuous.comp H'.continuous
      map_zero_left := by
        intro t
        exact congrArg A.markedBaseToCentralZeroSection (H'.map_zero_left t)
      map_one_left := by
        intro t
        exact congrArg A.markedBaseToCentralZeroSection (H'.map_one_left t) }
  refine ⟨K, ?_⟩
  intro s
  exact congrArg A.markedBaseToCentralZeroSection (htrace s)

/-- Pointwise form of the equal endpoint trace for the local fibre contraction. -/
public theorem orderFourCentralBaseFactor_zeroFibreHomotopy_point_trace
    (s : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    let H := A.orderFourCentralBaseFactor_zeroFibreHomotopy
    H (s, 0) = H (s, 1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  change A.orderFourPuncturedProductCentralRealizationMap
      (A.orderFourFillingRelationCayleyPuncturedLoop 0, _) =
    A.orderFourPuncturedProductCentralRealizationMap
      (A.orderFourFillingRelationCayleyPuncturedLoop 1, _)
  rw [A.orderFourFillingRelationCayleyPuncturedLoop.source,
    A.orderFourFillingRelationCayleyPuncturedLoop.target]

/-- The local order-four base factor reaches the standard zero-section four-turn loop by
the explicit fibre contraction followed by the global base homotopy. -/
public theorem orderFourCentralBaseFactor_homotopy_zeroSectionQuadruple :
    letI := A.orderFourActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      A.orderFourCentralBaseFactor.toContinuousMap
      A.orderFourZeroSectionQuadruplePath.toContinuousMap) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let Hzero := A.orderFourCentralBaseFactor_zeroFibreHomotopy
  let Hzero' := Hzero.cast rfl
    A.orderFourCentralZeroFibreBasePath_eq_zeroSectionBasePath
  rcases A.orderFourZeroSectionBase_quadrupleHomotopy with ⟨Hfour⟩
  exact ⟨Hzero'.trans Hfour⟩

/-- The local order-four base factor reaches the standard zero-section four-turn loop through
a genuine free homotopy. -/
public theorem orderFourCentralBaseFactor_homotopy_zeroSectionQuadruple_with_trace :
    letI := A.orderFourActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        A.orderFourCentralBaseFactor.toContinuousMap
        A.orderFourZeroSectionQuadruplePath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let Hzero := A.orderFourCentralBaseFactor_zeroFibreHomotopy
  let Hzero' := Hzero.cast rfl
    A.orderFourCentralZeroFibreBasePath_eq_zeroSectionBasePath
  rcases A.orderFourZeroSectionBase_quadrupleHomotopy_with_trace with
    ⟨Hfour, hfourTrace⟩
  let H := Hzero'.trans Hfour
  refine ⟨H, fun s ↦ ?_⟩
  apply freeLoopHomotopyTrans_trace
  · intro r
    exact A.orderFourCentralBaseFactor_zeroFibreHomotopy_point_trace r
  · exact hfourTrace

/-- The rebased zero-section quadruple displayed at the final affine basepoint. -/
public noncomputable def orderFourCentralAffineZeroSectionQuadruplePath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.orderFourActualCuspZeroSectionQuadruplePath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

/-- The local order-four base factor reaches the globally based zero-section quadruple through
one genuine free homotopy. -/
public theorem orderFourCentralBaseFactor_homotopy_globalZeroSectionQuadruple :
    letI := A.orderFourActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        A.orderFourCentralBaseFactor.toContinuousMap
        A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rcases A.orderFourCentralBaseFactor_homotopy_zeroSectionQuadruple_with_trace with
    ⟨Hlocal, hlocalTrace⟩
  rcases exists_freeLoopChangeBasepointHomotopy A.orderFourZeroSectionQuadruplePath
      A.actualCuspMarkedCentralWhisker with ⟨Hrebase, hrebaseTrace⟩
  have htarget :
      (A.actualCuspMarkedCentralWhisker.symm.trans
        (A.orderFourZeroSectionQuadruplePath.trans
          A.actualCuspMarkedCentralWhisker)).toContinuousMap =
        A.orderFourActualCuspZeroSectionQuadruplePath.toContinuousMap := by
    rfl
  have hcast : A.orderFourActualCuspZeroSectionQuadruplePath.toContinuousMap =
      A.orderFourCentralAffineZeroSectionQuadruplePath.toContinuousMap := by
    ext t
    rfl
  let Hglobal := Hrebase.cast rfl (htarget.trans hcast)
  let H := Hlocal.trans Hglobal
  refine ⟨H, fun s ↦ ?_⟩
  apply freeLoopHomotopyTrans_trace
  · exact hlocalTrace
  · exact hrebaseTrace

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
