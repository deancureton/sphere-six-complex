module

public import SphereSixComplex.Topology.PaperActualEllipticLocalGlobalAffineProductCompatibility

/-!
# Class-level elliptic connector marking

The complete filling relation only needs one deck-map evaluation at each prescribed geometric
connector.  Naturality and injectivity of the universal-cover fundamental-group equivalence then
identify the projected regular-loop class with the global affine-presentation class.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus

variable (A : PaperAnalyticData)

/-- The order-four collar comparison pinned by a path from the global affine base. -/
public noncomputable def orderFourActualCentralCoverComparisonOfPath
    (beta : Path A.actualCuspCentralBase A.orderFourActualEllipticCentralBase) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData
      (G := OrderFourAffineMappingTorusDeck A.periods)
      (H := paperCentralFreeAffineDeck)
      A.orderFourActualEllipticBoundaryProjection D.data.projection := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact quotientCoverMapDataOfBaseMap
    A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
    D.data.quotientCovering A.orderFourActualOverlapToCentral
    A.orderFourActualEllipticBoundaryBase
    (A.centralAffineUniversalCoverPointOfPath beta)
    (by
      rw [A.centralAffineUniversalCoverPointOfPath_projects]
      rfl)

/-- The connector-pinned order-four comparison sends the local basepoint to the based-path
universal-cover point represented by that connector. -/
public theorem orderFourActualCentralCoverComparisonOfPath_lift_base
    (beta : Path A.actualCuspCentralBase A.orderFourActualEllipticCentralBase) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    let C := A.orderFourActualCentralCoverComparisonOfPath beta
    C.lift A.orderFourActualEllipticBoundaryBase =
      A.centralAffineUniversalCoverPointOfPath beta := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  apply quotientCoverMapDataOfBaseMap_lift_base
  rw [A.centralAffineUniversalCoverPointOfPath_projects]
  rfl

private theorem quotientCoverFundamentalGroupNaturality_of_lift_eq_to_eq
    {E E' X X' G H : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
    [Group G] [Group H] [MulAction G E] [MulAction H E']
    [SimplyConnectedSpace E] [SimplyConnectedSpace E']
    {p : C(E, X)} {q : C(E', X')}
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (C : QuotientCoverMapData (G := G) (H := H) p q) (e : E) (e' : E')
    (he' : C.lift e = e') {x' : X'} (hproj : q e' = x')
    (g : FundamentalGroup X (p e)) :
    hq.fundamentalGroupEquiv ⟨e', hproj⟩
        (FundamentalGroup.mapOfEq C.baseMap
          (((C.commutes e).trans (congrArg q he')).trans hproj) g) =
      (MonoidHom.op C.deckMap) (hp.fundamentalGroupEquiv ⟨e, rfl⟩ g) := by
  subst x'
  simpa using
    (establishedQuotientCoverFundamentalGroupNaturality_of_lift_eq
      hp hq C e e' he' g).symm

/-- Naturality computes the class of every order-four physical deck loop at the lift represented
by `beta`. -/
public theorem orderFourActualCentralCoverComparisonOfPath_ofDeck
    (beta : Path A.actualCuspCentralBase A.orderFourActualEllipticCentralBase)
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.orderFourActualCentralCoverComparisonOfPath beta
    let hbase := (C.commutes A.orderFourActualEllipticBoundaryBase).trans
      ((congrArg D.data.projection
        (A.orderFourActualCentralCoverComparisonOfPath_lift_base beta)).trans
          (A.centralAffineUniversalCoverPointOfPath_projects beta))
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPointOfPath beta,
          A.centralAffineUniversalCoverPointOfPath_projects beta⟩
        (FundamentalGroup.mapOfEq C.baseMap hbase
          (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderFourActualEllipticBoundaryBase g)) =
      MulOpposite.op (C.deckMap g) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.orderFourActualCentralCoverComparisonOfPath beta
  let hbase := (C.commutes A.orderFourActualEllipticBoundaryBase).trans
    ((congrArg D.data.projection
      (A.orderFourActualCentralCoverComparisonOfPath_lift_base beta)).trans
        (A.centralAffineUniversalCoverPointOfPath_projects beta))
  change _ = (MonoidHom.op C.deckMap) (MulOpposite.op g)
  simpa only [fundamentalGroupEquiv_ofDeck] using
    (quotientCoverFundamentalGroupNaturality_of_lift_eq_to_eq
      A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
      D.data.quotientCovering C A.orderFourActualEllipticBoundaryBase
      (A.centralAffineUniversalCoverPointOfPath beta)
      (A.orderFourActualCentralCoverComparisonOfPath_lift_base beta)
      (A.centralAffineUniversalCoverPointOfPath_projects beta)
      (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase g))

/-- One complete filling-relation deck evaluation proves the order-three path-class marking. -/
public theorem orderThreeActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation
    (hdeck :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderThreeActualEllipticCentralProductPathClassIdentity := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  let C := A.orderThreeActualCentralCoverComparisonOfPath beta
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  change Path.Homotopic.Quotient.mk _ = _
  apply E.injective
  rw [← A.orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection]
  rw [← A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class]
  rw [A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
  have hnat := A.orderThreeActualCentralCoverComparisonOfPath_ofDeck beta
    A.orderThreeActualEllipticBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
      (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) at hnat
  rw [hnat, hdeck]
  exact (A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta
    orderThreeFillingRelationClassifiedCentralProductDeck).symm

/-- One complete filling-relation deck evaluation proves the order-four path-class marking. -/
public theorem orderFourActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation
    (hdeck :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderFourActualEllipticCentralProductPathClassIdentity := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  let C := A.orderFourActualCentralCoverComparisonOfPath beta
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  change Path.Homotopic.Quotient.mk _ = _
  apply E.injective
  rw [← A.orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection]
  rw [← A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_class]
  rw [A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
  have hnat := A.orderFourActualCentralCoverComparisonOfPath_ofDeck beta
    A.orderFourActualEllipticBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
      (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation) at hnat
  rw [hnat, hdeck]
  exact (A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta
    orderFourFillingRelationClassifiedCentralProductDeck).symm

/-- The order-three filling-relation deck evaluation also gives the equivalent cover-product
comparison. -/
public theorem orderThreeActualEllipticCentralCoverProductLiftComparison_of_deckMap_fillingRelation
    (hdeck :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderThreeActualEllipticCentralCoverProductLiftComparison :=
  A.orderThreeCentralCoverProductLiftComparison_iff_pathClassIdentity.mpr
    (A.orderThreeActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation hdeck)

/-- The order-four filling-relation deck evaluation also gives the equivalent cover-product
comparison. -/
public theorem orderFourActualEllipticCentralCoverProductLiftComparison_of_deckMap_fillingRelation
    (hdeck :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderFourActualEllipticCentralCoverProductLiftComparison :=
  A.orderFourCentralCoverProductLiftComparison_iff_pathClassIdentity.mpr
    (A.orderFourActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation hdeck)

/-- The two connector-pinned filling-relation deck evaluations imply the remaining elliptic
normal-closure residual. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_productConnectorDeckMaps
    (hThree :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹)
    (hFour :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_centralProductPathClassIdentities
    (A.orderThreeActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation hThree)
    (A.orderFourActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation hFour)

/-- The same two evaluations supply the exact nonempty residual previously requested as an
established input. -/
public theorem actualEllipticRelatorNormalClosureResidual_nonempty_of_productConnectorDeckMaps
    (hThree :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹)
    (hFour :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    Nonempty
      (ActualEllipticRelatorNormalClosureResidual
        A A.actualCuspCentralNaturality) :=
  ⟨A.actualEllipticRelatorNormalClosureResidual_of_productConnectorDeckMaps hThree hFour⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
