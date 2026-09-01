module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeLocalGlobalFactorHomotopyReduction
public import SphereSixComplex.Topology.FreeLoopChangeBasepointHomotopy

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- A chosen vector lift of the fixed torus coordinate carried by the local base factor. -/
public noncomputable def orderThreeLocalOffsetBaseVector : ComplexTwoSpace :=
  A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 +
    A.orderThreeActualEllipticBoundaryBase.2.2

public theorem orderThreePrincipalGaugeWithOffsetPath_zero_eq_mk :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreePrincipalGaugeWithOffsetPath 0 =
      (Quotient.mk _ A.orderThreeLocalOffsetBaseVector : A.orderThreeTorus) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  unfold orderThreePrincipalGaugeWithOffsetPath
    orderThreePrincipalGaugeWithOffsetMap orderThreeLocalOffsetBaseVector
  change A.orderThreeFillingRelationPrincipalGaugeLoop 0 +
      Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2 =
    Quotient.mk _ (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 +
      A.orderThreeActualEllipticBoundaryBase.2.2)
  rw [A.orderThreeFillingRelationPrincipalGaugeLoop.source]
  rfl

/-- The local base circle realized with zero torus coordinate. -/
public noncomputable def orderThreeLocalZeroBaseCentralMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    C(unitInterval, A.CentralFamily) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact
    { toFun := fun t ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeFillingRelationCayleyPuncturedLoop t, 0)
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (A.orderThreeFillingRelationCayleyPuncturedLoop.continuous.prodMk
          continuous_const) }

/-- Contract the fixed local torus coordinate to zero through its chosen vector lift. -/
public def orderThreeLocalBaseFiberContractionHomotopy :
    letI := A.orderThreeActualEllipticBoundaryAction
    ContinuousMap.Homotopy
      A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeLocalZeroBaseCentralMap := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne).1
  exact
    { toFun := fun st ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeFillingRelationCayleyPuncturedLoop st.2,
          (Quotient.mk _
            (((1 - (st.1 : ℝ) : ℝ) : ℂ) • A.orderThreeLocalOffsetBaseVector) :
              AdditiveTorus p))
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        ((A.orderThreeFillingRelationCayleyPuncturedLoop.continuous.comp
          continuous_snd).prodMk
            ((continuous_quot_mk : Continuous (torusProjection p)).comp (by fun_prop)))
      map_zero_left := by
        intro t
        change A.orderThreePuncturedProductToCentralMap
            (A.orderThreeFillingRelationCayleyPuncturedLoop t,
              Quotient.mk _ (((1 - (0 : ℝ) : ℝ) : ℂ) •
                A.orderThreeLocalOffsetBaseVector)) =
          A.orderThreePuncturedProductToCentralMap
            (A.orderThreeFillingRelationCayleyPuncturedLoop t,
              A.orderThreePrincipalGaugeWithOffsetPath 0)
        rw [show (((1 - (0 : ℝ) : ℝ) : ℂ) •
          A.orderThreeLocalOffsetBaseVector) =
            A.orderThreeLocalOffsetBaseVector by simp]
        rw [A.orderThreePrincipalGaugeWithOffsetPath_zero_eq_mk]
      map_one_left := by
        intro t
        change A.orderThreePuncturedProductToCentralMap
            (A.orderThreeFillingRelationCayleyPuncturedLoop t,
              Quotient.mk _ (((1 - (1 : ℝ) : ℝ) : ℂ) •
                A.orderThreeLocalOffsetBaseVector)) =
          A.orderThreePuncturedProductToCentralMap
            (A.orderThreeFillingRelationCayleyPuncturedLoop t, 0)
        rw [show (((1 - (1 : ℝ) : ℝ) : ℂ) •
          A.orderThreeLocalOffsetBaseVector) = 0 by simp]
        rw [additiveTorus_mk_zero p] }

/-- The fibre contraction moves the two endpoints of the base loop along exactly the same
point-set path. -/
public theorem orderThreeLocalBaseFiberContractionHomotopy_trace
    (s : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeLocalBaseFiberContractionHomotopy (s, 0) =
      A.orderThreeLocalBaseFiberContractionHomotopy (s, 1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  unfold orderThreeLocalBaseFiberContractionHomotopy
  apply congrArg A.orderThreePuncturedProductToCentralMap
  apply Prod.ext
  · exact A.orderThreeFillingRelationCayleyPuncturedLoop.source.trans
      A.orderThreeFillingRelationCayleyPuncturedLoop.target.symm
  · rfl

/-- The restricted inverse chart has exactly the product coordinate with which it was fed. -/
public theorem orderThreePuncturedProductToRegularMap_productCoordinate
    (zq : A.OrderThreeCayleyPuncturedDisc × A.orderThreeTorus) :
    letI := A.orderThreeActualEllipticBoundaryAction
    orderThreeRealPeriodProductHomeomorph A.periods
        (regularFamilyInclusion A.periods
          (A.orderThreePuncturedProductToRegularMap
            (A.orderThreePuncturedProductCarrierMap zq))) = (zq.1.1, zq.2) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let q := (orderThreePuncturedProductHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one).symm
      (A.orderThreePuncturedProductCarrierMap zq)
  have hmap : A.orderThreePuncturedProductToRegularMap
      (A.orderThreePuncturedProductCarrierMap zq) =
      orderThreeCollarToRegular A.periods hproper
        A.starSeparation.orderThree.sourceData q := by rfl
  rw [hmap]
  have hinc := regularFamilyInclusion_orderThreeCollarToRegular A.periods hproper
    A.starSeparation.orderThree.sourceData q
  rw [hinc]
  exact congrArg Subtype.val
    ((orderThreePuncturedProductHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).apply_symm_apply
        (A.orderThreePuncturedProductCarrierMap zq))

/-- A zero torus coordinate in the restricted chart is the actual regular-family zero section
over the base of the realized point. -/
public theorem orderThreePuncturedProductToRegularMap_zero_eq_zeroSection
    (z : A.OrderThreeCayleyPuncturedDisc) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let x := A.orderThreePuncturedProductToRegularMap
      (A.orderThreePuncturedProductCarrierMap (z, 0))
    x = regularFamilyZeroSection A.periods
      (regularTotalSpaceBase A.periods x) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let x := A.orderThreePuncturedProductToRegularMap
    (A.orderThreePuncturedProductCarrierMap (z, 0))
  have hcoord := A.orderThreePuncturedProductToRegularMap_productCoordinate (z, 0)
  have hbase := congrArg Prod.fst hcoord
  rw [orderThreeRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hbase
  apply regularFamilyInclusion_injective A.periods
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  rw [hcoord]
  simp only [regularFamilyZeroSection_apply, regularFamilyInclusion_mk,
    regularBundleInclusion, orderThreeRealPeriodProductHomeomorph_mk]
  apply Prod.ext
  · exact hbase.symm
  · simp only [movingToFixedCover, periodCoordinates, map_zero]
    exact (additiveTorus_mk_zero _).symm

/-- With zero torus coordinate, the local punctured-product realization is literally the
global zero-section lift of the same Cayley base loop. -/
public theorem orderThreeLocalZeroBaseCentralMap_eq_zeroSectionBaseMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeLocalZeroBaseCentralMap = A.orderThreeZeroSectionBaseMap := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  ext t
  let z := A.orderThreeFillingRelationCayleyPuncturedLoop t
  let x := A.orderThreePuncturedProductToRegularMap
    (A.orderThreePuncturedProductCarrierMap (z, 0))
  let b := regularTotalSpaceBase A.periods x
  have hxzero : x = regularFamilyZeroSection A.periods b := by
    exact A.orderThreePuncturedProductToRegularMap_zero_eq_zeroSection z
  have hlocal : A.orderThreeLocalZeroBaseCentralMap t =
      A.centralZeroSection (regularBaseQuotientMap b) := by
    change A.centralQuotientProjection x =
      puncturedGlobalZeroSection A.periods (regularBaseQuotientMap b)
    rw [hxzero, puncturedGlobalZeroSection_mk]
    rfl
  rw [hlocal]
  change A.centralZeroSection (regularBaseQuotientMap b) =
    A.centralZeroSection
      (A.puncturedBaseHomeomorphTwicePuncturedComplex.symm
        (A.orderThreeFillingRelationBaseCoordinateMap t))
  apply congrArg A.centralZeroSection
  apply A.puncturedBaseHomeomorphTwicePuncturedComplex.injective
  rw [puncturedBaseHomeomorphTwicePuncturedComplex_mk,
    A.puncturedBaseHomeomorphTwicePuncturedComplex.apply_symm_apply]
  apply Subtype.ext
  rw [A.orderThreeFillingRelationBaseCoordinateMap_eq_cayley]
  change A.modular.sourceCoordinate.coordinate b.1 =
    ellipticChartFunction A.modular.sourceCoordinate.coordinate
      fuchsianOneFixedPoint
      (localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue t)
  rw [← A.orderThreeCayleyRegularCoordinate_chartFunction b.1]
  apply congrArg (ellipticChartFunction A.modular.sourceCoordinate.coordinate
    fuchsianOneFixedPoint)
  have hcoord := A.orderThreePuncturedProductToRegularMap_productCoordinate (z, 0)
  have hbase := congrArg Prod.fst hcoord
  rw [orderThreeRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion] at hbase
  calc
    ((orderThreeCayleyHomeomorph b.1 :
        SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) =
        ((z.1 : SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc) : ℂ) :=
      congrArg (fun w : SphereSixComplex.Geometry.EllipticLocalCoordinates.ComplexUnitDisc ↦
        (w : ℂ)) hbase
    _ = localDegreeCirclePoint A.orderThreeFillingRelationCayleyBaseValue t := by
      simp [z, orderThreeFillingRelationCayleyPuncturedLoop,
        orderThreeFillingRelationCayleyDiscLoop,
        orderThreeFillingRelationCayleyLoop, puncturedComplexIntegerCircle,
        puncturedComplexIntegerCirclePoint]
      unfold localDegreeCirclePoint
      congr 2

/-- Before the final change of basepoint, the local base factor is freely homotopic to the
global zero-section triple by explicit zero-fibre contraction followed by the cubic base
homotopy. -/
public theorem orderThreeLocalOffsetBaseCentralPath_homotopy_zeroSectionTriple :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (ContinuousMap.Homotopy
      A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeZeroSectionTriplePath.toContinuousMap) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let Hzero := A.orderThreeLocalBaseFiberContractionHomotopy
  let Hzero' := Hzero.cast rfl
    A.orderThreeLocalZeroBaseCentralMap_eq_zeroSectionBaseMap
  rcases A.orderThreeZeroSectionBase_tripleHomotopy with ⟨Htriple⟩
  exact ⟨Hzero'.trans Htriple⟩

/-- The local base factor reaches the globally based zero-section triple through one genuine
free homotopy. -/
public theorem orderThreeLocalOffsetBaseCentralPath_homotopy_globalZeroSectionTriple :
    letI := A.orderThreeActualEllipticBoundaryAction
    ∃ H : ContinuousMap.Homotopy
        A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
        A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let Hzero := A.orderThreeLocalBaseFiberContractionHomotopy
  let Hzero' := Hzero.cast rfl
    A.orderThreeLocalZeroBaseCentralMap_eq_zeroSectionBaseMap
  rcases A.orderThreeZeroSectionBase_tripleHomotopy_with_trace with
    ⟨Htriple, htripleTrace⟩
  let Hlocal := Hzero'.trans Htriple
  have hlocalTrace : ∀ s : unitInterval, Hlocal (s, 0) = Hlocal (s, 1) := by
    intro s
    apply freeLoopHomotopyTrans_trace
    · intro r
      exact A.orderThreeLocalBaseFiberContractionHomotopy_trace r
    · exact htripleTrace
  rcases exists_freeLoopChangeBasepointHomotopy A.orderThreeZeroSectionTriplePath
      A.actualCuspMarkedCentralWhisker with ⟨Hrebase, hrebaseTrace⟩
  have htarget :
      (A.actualCuspMarkedCentralWhisker.symm.trans
        (A.orderThreeZeroSectionTriplePath.trans
          A.actualCuspMarkedCentralWhisker)).toContinuousMap =
        A.orderThreeActualCuspZeroSectionTriplePath.toContinuousMap := by
    rfl
  have hcast : A.orderThreeActualCuspZeroSectionTriplePath.toContinuousMap =
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap := by
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
