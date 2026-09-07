module
public import SphereSixComplex.Topology.PaperEllipticSynchronizedEnteringSheet
public import SphereSixComplex.Topology.RegularFamilyPeriodPathClassTransport

@[expose] public section
noncomputable section

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.LatticeData

namespace SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

public theorem movingToFixedCover_scaled_period
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (z₀ z : UpperHalfPlane) (a : IntegerPeriods) (t : ℝ) (v : ComplexTwoSpace) :
    movingToFixedCover F z₀ (z, t • periodVector (parameterMap F z).1 a + v) =
      (z, t • periodVector (parameterMap F z₀).1 a +
        (movingToFixedCover F z₀ (z, v)).2) := by
  apply Prod.ext
  · rfl
  · change (fullRankDomain (parameterMap F z₀)).realEquiv
        ((fullRankDomain (parameterMap F z)).realEquiv.symm
          (t • periodVector (parameterMap F z).1 a + v)) = _
    rw [map_add, map_smul]
    rw [show (fullRankDomain (parameterMap F z)).realEquiv.symm
        (periodVector (parameterMap F z).1 a) = integerToReal a from
      periodCoordinates_periodVector (parameterMap F z) a]
    rw [map_add, map_smul, (fullRankDomain (parameterMap F z₀)).map_integer]
    rfl

end SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology
variable (A : PaperAnalyticData)

public theorem orderFour_fixedToMoving_period_realization
    (z : A.OrderFourCayleyPuncturedDisc)
    (b : RegularBase (U := A.paperTriangleUniformization))
    (hb : orderFourCayleyHomeomorph b.1 = z.1)
    (v : ComplexTwoSpace) (a : IntegerPeriods) (t : ℝ) :
    letI := A.orderFourActualEllipticBoundaryAction
    regularFamilyCoverProjection A.periods
      (b, t • periodVector (parameterMap A.periods b.1).1 a +
        (fixedToMovingCover A.periods A.paperTriangleUniformization.zTwo (b.1, v)).2) =
      A.orderFourPuncturedProductToRegularMap
        (A.orderFourPuncturedProductCarrierMap
          (z, Quotient.mk _ (t • periodVector
            (parameterMap A.periods A.paperTriangleUniformization.zTwo).1 a + v))) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  apply regularFamilyInclusion_injective A.periods
  apply (orderFourRealPeriodProductHomeomorph A.periods).injective
  rw [A.orderFourPuncturedProductToRegularMap_productCoordinate]
  change orderFourRealPeriodProductHomeomorph A.periods
    (Quotient.mk _ (b.1, t • periodVector (parameterMap A.periods b.1).1 a +
      (fixedToMovingCover A.periods A.paperTriangleUniformization.zTwo (b.1, v)).2)) = _
  rw [orderFourRealPeriodProductHomeomorph_mk, movingToFixedCover_scaled_period]
  have hcancel : movingToFixedCover A.periods A.paperTriangleUniformization.zTwo
      (b.1, (fixedToMovingCover A.periods A.paperTriangleUniformization.zTwo (b.1, v)).2) =
        (b.1, v) := by
    change movingToFixedCover A.periods A.paperTriangleUniformization.zTwo
      (fixedToMovingCover A.periods A.paperTriangleUniformization.zTwo (b.1, v)) = _
    exact movingToFixedCover_fixedToMovingCover A.periods _ _
  rw [hcancel]
  exact Prod.ext hb rfl

public theorem orderFourActualRegularBase_cayley :
    letI := A.orderFourActualEllipticBoundaryAction
    orderFourCayleyHomeomorph
      (regularTotalSpaceBase A.periods
        (A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase)).1 =
      A.orderFourCayleyPuncturedBasepoint.1 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have h := congrArg Prod.fst (A.orderFourRegularLoop_cayleyGaugeProductCoordinate 0)
  rw [orderFourRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion,
    A.orderFourFillingRelationRegularLoop.source,
    A.orderFourFillingRelationCayleyDiscLoop.source] at h
  exact h

public def orderFourActualStraightCoverPoint :
    RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
  let b := regularTotalSpaceBase A.periods
    (A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase)
  (b, (fixedToMovingCover A.periods A.paperTriangleUniformization.zTwo
    (b.1, A.orderFourFillingRelationPrincipalGaugeCoverLift 0 +
      A.orderFourActualEllipticBoundaryBase.2.2)).2)

public theorem orderFourActualStraightCoverPoint_period_projects (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    regularFamilyCoverProjection A.periods
      (regularFamilyPeriodLiftPath A.periods A.orderFourActualStraightCoverPoint (-epsilon') t) =
      A.orderFourPuncturedProductToRegularMap
        (A.orderFourPuncturedProductCarrierMap
          (A.orderFourCayleyPuncturedBasepoint,
            A.orderFourPrincipalGaugeStraightLoop t +
              Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rw [show regularFamilyCoverProjection A.periods
      (regularFamilyPeriodLiftPath A.periods A.orderFourActualStraightCoverPoint (-epsilon') t) =
      A.orderFourPuncturedProductToRegularMap
        (A.orderFourPuncturedProductCarrierMap
          (A.orderFourCayleyPuncturedBasepoint,
            Quotient.mk _ ((t : ℝ) • periodVector
              (parameterMap A.periods A.paperTriangleUniformization.zTwo).1 (-epsilon') +
              (A.orderFourFillingRelationPrincipalGaugeCoverLift 0 +
                A.orderFourActualEllipticBoundaryBase.2.2)))) from
    A.orderFour_fixedToMoving_period_realization _ _ A.orderFourActualRegularBase_cayley _ _ _]
  congr 2
  apply Prod.ext
  · rfl
  change Quotient.mk _ ((t : ℝ) • periodVector
      (parameterMap A.periods A.paperTriangleUniformization.zTwo).1 (-epsilon') +
      (A.orderFourFillingRelationPrincipalGaugeCoverLift 0 +
        A.orderFourActualEllipticBoundaryBase.2.2)) = _
  have hstraight : A.orderFourPrincipalGaugeStraightLoop t =
      (Quotient.mk _ ((t : ℝ) • periodVector
        (parameterMap A.periods A.paperTriangleUniformization.zTwo).1 (-epsilon') +
        A.orderFourFillingRelationPrincipalGaugeCoverLift 0) : A.orderFourTorus) := by
    change Quotient.mk _ (A.orderFourPrincipalGaugeStraightLiftPath t) = _
    apply congrArg (Quotient.mk _)
    unfold orderFourPrincipalGaugeStraightLiftPath
    rw [Path.segment_apply, AffineMap.lineMap_apply_module,
      orderFourFillingRelationPrincipalGaugeDeck_smul]
    module
  rw [hstraight]
  change Quotient.mk _ _ = Quotient.mk _ _
  apply congrArg (Quotient.mk _)
  abel

public theorem orderFourMappedActualStraightPeriod_eq_actualBasedStraightFiber :
    letI := A.orderFourActualEllipticBoundaryAction
    ((regularFamilyPeriodLoop A.periods A.orderFourActualStraightCoverPoint (-epsilon')).map
      (regularFamilyQuotientMap A.periods).continuous).toContinuousMap =
      A.orderFourCentralActualBasedStraightFiberPath.toContinuousMap := by
  let _ := A.orderFourActualEllipticBoundaryAction
  ext t
  change regularFamilyQuotientMap A.periods
    (regularFamilyCoverProjection A.periods
      (regularFamilyPeriodLiftPath A.periods A.orderFourActualStraightCoverPoint (-epsilon') t)) = _
  rw [A.orderFourActualStraightCoverPoint_period_projects]
  rfl

public theorem orderFourActualStraightCoverPoint_projects :
    letI := A.orderFourActualEllipticBoundaryAction
    regularFamilyCoverProjection A.periods A.orderFourActualStraightCoverPoint =
      A.orderFourCollarRegularRepresentativeMap A.orderFourActualEllipticBoundaryBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have h := A.orderFourActualStraightCoverPoint_period_projects 0
  rw [(regularFamilyPeriodLiftPath A.periods A.orderFourActualStraightCoverPoint (-epsilon')).source] at h
  rw [h]
  have hzero : A.orderFourPrincipalGaugeStraightLoop 0 =
      A.orderFourFillingRelationPrincipalGaugeLoop 0 := by
    rw [A.orderFourPrincipalGaugeStraightLoop.source]
    rfl
  rw [hzero]
  have hreal := A.orderFourRegularLoop_eq_puncturedProductRealization 0
  rw [A.orderFourFillingRelationCayleyPuncturedLoop.source,
    A.orderFourPrincipalGaugeWithOffsetPath.source,
    A.orderFourFillingRelationRegularLoop.source] at hreal
  exact hreal

public def orderThreeCentralActualBasedStraightFiberPath :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let g : C(A.orderThreeTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderThreePuncturedProductToCentralMap
        (A.orderThreeCayleyPuncturedBasepoint,
          q + Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2)
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)) }
  have hbase : A.orderThreeActualEllipticCentralBase =
      g (A.orderThreeFillingRelationPrincipalGaugeLoop 0) :=
    A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
  exact (A.orderThreePrincipalGaugeStraightLoop.map g.continuous).cast hbase hbase

public theorem orderThree_fixedToMoving_period_realization
    (z : A.OrderThreeCayleyPuncturedDisc)
    (b : RegularBase (U := A.paperTriangleUniformization))
    (hb : orderThreeCayleyHomeomorph b.1 = z.1)
    (v : ComplexTwoSpace) (a : IntegerPeriods) (t : ℝ) :
    letI := A.orderThreeActualEllipticBoundaryAction
    regularFamilyCoverProjection A.periods
      (b, t • periodVector (parameterMap A.periods b.1).1 a +
        (fixedToMovingCover A.periods A.paperTriangleUniformization.zOne (b.1, v)).2) =
      A.orderThreePuncturedProductToRegularMap
        (A.orderThreePuncturedProductCarrierMap
          (z, Quotient.mk _ (t • periodVector
            (parameterMap A.periods A.paperTriangleUniformization.zOne).1 a + v))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  apply regularFamilyInclusion_injective A.periods
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  rw [A.orderThreePuncturedProductToRegularMap_productCoordinate]
  change orderThreeRealPeriodProductHomeomorph A.periods
    (Quotient.mk _ (b.1, t • periodVector (parameterMap A.periods b.1).1 a +
      (fixedToMovingCover A.periods A.paperTriangleUniformization.zOne (b.1, v)).2)) = _
  rw [orderThreeRealPeriodProductHomeomorph_mk, movingToFixedCover_scaled_period]
  have hcancel : movingToFixedCover A.periods A.paperTriangleUniformization.zOne
      (b.1, (fixedToMovingCover A.periods A.paperTriangleUniformization.zOne (b.1, v)).2) =
        (b.1, v) := by
    change movingToFixedCover A.periods A.paperTriangleUniformization.zOne
      (fixedToMovingCover A.periods A.paperTriangleUniformization.zOne (b.1, v)) = _
    exact movingToFixedCover_fixedToMovingCover A.periods _ _
  rw [hcancel]
  exact Prod.ext hb rfl

public theorem orderThreeActualRegularBase_cayley :
    letI := A.orderThreeActualEllipticBoundaryAction
    orderThreeCayleyHomeomorph
      (regularTotalSpaceBase A.periods
        (A.orderThreeCollarRegularRepresentativeMap A.orderThreeActualEllipticBoundaryBase)).1 =
      A.orderThreeCayleyPuncturedBasepoint.1 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have h := congrArg Prod.fst (A.orderThreeRegularLoop_cayleyGaugeProductCoordinate 0)
  rw [orderThreeRealPeriodProductHomeomorph_fst,
    familyTotalSpaceBase_regularFamilyInclusion,
    A.orderThreeFillingRelationRegularLoop.source,
    A.orderThreeFillingRelationCayleyDiscLoop.source] at h
  exact h

public def orderThreeActualStraightCoverPoint :
    RegularBase (U := A.paperTriangleUniformization) × ComplexTwoSpace :=
  let b := regularTotalSpaceBase A.periods
    (A.orderThreeCollarRegularRepresentativeMap A.orderThreeActualEllipticBoundaryBase)
  (b, (fixedToMovingCover A.periods A.paperTriangleUniformization.zOne
    (b.1, A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 +
      A.orderThreeActualEllipticBoundaryBase.2.2)).2)

public theorem orderThreeActualStraightCoverPoint_period_projects (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    regularFamilyCoverProjection A.periods
      (regularFamilyPeriodLiftPath A.periods A.orderThreeActualStraightCoverPoint epsilon t) =
      A.orderThreePuncturedProductToRegularMap
        (A.orderThreePuncturedProductCarrierMap
          (A.orderThreeCayleyPuncturedBasepoint,
            A.orderThreePrincipalGaugeStraightLoop t +
              Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rw [show regularFamilyCoverProjection A.periods
      (regularFamilyPeriodLiftPath A.periods A.orderThreeActualStraightCoverPoint epsilon t) =
      A.orderThreePuncturedProductToRegularMap
        (A.orderThreePuncturedProductCarrierMap
          (A.orderThreeCayleyPuncturedBasepoint,
            Quotient.mk _ ((t : ℝ) • periodVector
              (parameterMap A.periods A.paperTriangleUniformization.zOne).1 epsilon +
              (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 +
                A.orderThreeActualEllipticBoundaryBase.2.2)))) from
    A.orderThree_fixedToMoving_period_realization _ _ A.orderThreeActualRegularBase_cayley _ _ _]
  congr 2
  apply Prod.ext
  · rfl
  change Quotient.mk _ ((t : ℝ) • periodVector
      (parameterMap A.periods A.paperTriangleUniformization.zOne).1 epsilon +
      (A.orderThreeFillingRelationPrincipalGaugeCoverLift 0 +
        A.orderThreeActualEllipticBoundaryBase.2.2)) = _
  have hstraight : A.orderThreePrincipalGaugeStraightLoop t =
      (Quotient.mk _ ((t : ℝ) • periodVector
        (parameterMap A.periods A.paperTriangleUniformization.zOne).1 epsilon +
        A.orderThreeFillingRelationPrincipalGaugeCoverLift 0) : A.orderThreeTorus) := by
    change Quotient.mk _ (A.orderThreePrincipalGaugeStraightLiftPath t) = _
    apply congrArg (Quotient.mk _)
    unfold orderThreePrincipalGaugeStraightLiftPath
    rw [Path.segment_apply, AffineMap.lineMap_apply_module,
      orderThreeFillingRelationPrincipalGaugeDeck_smul]
    module
  rw [hstraight]
  change Quotient.mk _ _ = Quotient.mk _ _
  apply congrArg (Quotient.mk _)
  abel

public theorem orderThreeMappedActualStraightPeriod_eq_actualBasedStraightFiber :
    letI := A.orderThreeActualEllipticBoundaryAction
    ((regularFamilyPeriodLoop A.periods A.orderThreeActualStraightCoverPoint epsilon).map
      (regularFamilyQuotientMap A.periods).continuous).toContinuousMap =
      A.orderThreeCentralActualBasedStraightFiberPath.toContinuousMap := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  ext t
  change regularFamilyQuotientMap A.periods
    (regularFamilyCoverProjection A.periods
      (regularFamilyPeriodLiftPath A.periods A.orderThreeActualStraightCoverPoint epsilon t)) = _
  rw [A.orderThreeActualStraightCoverPoint_period_projects]
  rfl

public theorem orderThreeActualStraightCoverPoint_projects :
    letI := A.orderThreeActualEllipticBoundaryAction
    regularFamilyCoverProjection A.periods A.orderThreeActualStraightCoverPoint =
      A.orderThreeCollarRegularRepresentativeMap A.orderThreeActualEllipticBoundaryBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have h := A.orderThreeActualStraightCoverPoint_period_projects 0
  rw [(regularFamilyPeriodLiftPath A.periods A.orderThreeActualStraightCoverPoint epsilon).source] at h
  rw [h]
  have hzero : A.orderThreePrincipalGaugeStraightLoop 0 =
      A.orderThreeFillingRelationPrincipalGaugeLoop 0 := by
    rw [A.orderThreePrincipalGaugeStraightLoop.source]
    rfl
  rw [hzero]
  have hreal := A.orderThreeRegularLoop_eq_puncturedProductRealization 0
  rw [A.orderThreeFillingRelationCayleyPuncturedLoop.source,
    A.orderThreePrincipalGaugeWithOffsetPath.source,
    A.orderThreeFillingRelationRegularLoop.source] at hreal
  exact hreal

public theorem orderThreeLocalOffsetFiberCentralPath_homotopic_actualBasedStraight :
    letI := A.orderThreeActualEllipticBoundaryAction
    Nonempty (Path.Homotopy A.orderThreeLocalOffsetFiberCentralPath
      A.orderThreeCentralActualBasedStraightFiberPath) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have hclass := A.orderThreeFillingRelationPrincipalGaugeLoop_class_eq_straight
  change Path.Homotopic.Quotient.mk A.orderThreeFillingRelationPrincipalGaugeLoop =
    Path.Homotopic.Quotient.mk A.orderThreePrincipalGaugeStraightLoop at hclass
  rcases (Quotient.exact hclass : Path.Homotopic
    A.orderThreeFillingRelationPrincipalGaugeLoop
      A.orderThreePrincipalGaugeStraightLoop) with ⟨Htorus⟩
  let x := A.orderThreeCayleyPuncturedBasepoint
  let offset : A.orderThreeTorus := Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2
  let g : C(A.orderThreeTorus, A.CentralFamily) :=
    { toFun := fun q ↦ A.orderThreePuncturedProductToCentralMap (x, q + offset)
      continuous_toFun := A.orderThreePuncturedProductToCentralMap.continuous.comp
        (continuous_const.prodMk (continuous_id.add continuous_const)) }
  have hbase : A.orderThreeActualEllipticCentralBase =
      g (A.orderThreeFillingRelationPrincipalGaugeLoop 0) :=
    A.orderThreeActualEllipticCentralBase_eq_puncturedProductBase
  let Hmapped := (Htorus.map g).pathCast hbase hbase
  have hsource :
      (A.orderThreeFillingRelationPrincipalGaugeLoop.map g.continuous).cast hbase hbase =
        A.orderThreeLocalOffsetFiberCentralPath := by
    apply Path.ext
    funext t
    rfl
  have htarget :
      (A.orderThreePrincipalGaugeStraightLoop.map g.continuous).cast hbase hbase =
        A.orderThreeCentralActualBasedStraightFiberPath := by
    apply Path.ext
    funext t
    rfl
  exact ⟨Hmapped.cast hsource htarget⟩

end SphereSixComplex.Geometry.PaperAnalyticData
