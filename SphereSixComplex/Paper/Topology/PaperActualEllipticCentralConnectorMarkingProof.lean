module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticLocalGlobalAffineProductCompatibility

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
public noncomputable def ellipticFourCentralCoverComparisonOfPath
    (beta : Path A.cuspCentralBase A.ellipticFourCentralBase) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    QuotientCoverMapData
      (G := OrderFourAffineMappingTorusDeck A.periods)
      (H := PaperCentralFreeAffineDeck)
      A.ellipticFourBoundaryProjection D.data.projection := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : LocallyPathConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    let _ : LocallyPathConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius) :=
      isOpen_Ioo.locallyPathConnectedSpace
    inferInstance
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  exact quotientCoverMapDataOfBaseMap
    A.ellipticFourBoundaryProjection_isQuotientCoveringMap
    D.data.quotientCovering A.ellipticFourOverlapToCentral
    A.ellipticFourBoundaryBase
    (A.centralAffineUniversalCoverPointOfPath beta)
    (by
      rw [A.centralAffineUniversalCoverPointOfPath_projects]
      rfl)

/-- The connector-pinned order-four comparison sends the local basepoint to the based-path
universal-cover point represented by that connector. -/
public theorem ellipticFourCentralCoverComparisonOfPath_lift_base
    (beta : Path A.cuspCentralBase A.ellipticFourCentralBase) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    let C := A.ellipticFourCentralCoverComparisonOfPath beta
    C.lift A.ellipticFourBoundaryBase =
      A.centralAffineUniversalCoverPointOfPath beta := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
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
    (QuotientCoverMapData.fundamentalGroupEquiv_natural_of_lift_eq
      hp hq C e e' he' g).symm

/-- Naturality computes the class of every order-four physical deck loop at the lift represented
by `beta`. -/
public theorem ellipticFourCentralCoverComparisonOfPath_ofDeck
    (beta : Path A.cuspCentralBase A.ellipticFourCentralBase)
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    letI : SimplyConnectedSpace D.Cover := D.data.simplyConnected
    let C := A.ellipticFourCentralCoverComparisonOfPath beta
    let hbase := (C.commutes A.ellipticFourBoundaryBase).trans
      ((congrArg D.data.projection
        (A.ellipticFourCentralCoverComparisonOfPath_lift_base beta)).trans
          (A.centralAffineUniversalCoverPointOfPath_projects beta))
    D.data.quotientCovering.fundamentalGroupEquiv
        ⟨A.centralAffineUniversalCoverPointOfPath beta,
          A.centralAffineUniversalCoverPointOfPath_projects beta⟩
        (FundamentalGroup.mapOfEq C.baseMap hbase
          (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
            A.ellipticFourBoundaryBase g)) =
      MulOpposite.op (C.deckMap g) := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let C := A.ellipticFourCentralCoverComparisonOfPath beta
  let hbase := (C.commutes A.ellipticFourBoundaryBase).trans
    ((congrArg D.data.projection
      (A.ellipticFourCentralCoverComparisonOfPath_lift_base beta)).trans
        (A.centralAffineUniversalCoverPointOfPath_projects beta))
  change _ = (MonoidHom.op C.deckMap) (MulOpposite.op g)
  simpa only [fundamentalGroupEquiv_ofDeck] using
    (quotientCoverFundamentalGroupNaturality_of_lift_eq_to_eq
      A.ellipticFourBoundaryProjection_isQuotientCoveringMap
      D.data.quotientCovering C A.ellipticFourBoundaryBase
      (A.centralAffineUniversalCoverPointOfPath beta)
      (A.ellipticFourCentralCoverComparisonOfPath_lift_base beta)
      (A.centralAffineUniversalCoverPointOfPath_projects beta)
      (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase g))

/-- One complete filling-relation deck evaluation proves the order-three path-class marking. -/
public theorem ellipticThreeCentralProductPathClassIdentity_of_deckMap_fillingRelation
    (hdeck :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderThreeActualEllipticCentralProductPathClassIdentity := by
  let _ := A.ellipticThreeBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.ellipticThreeCentralProductConnector
  let C := A.ellipticThreeCentralCoverComparisonOfPath beta
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  change Path.Homotopic.Quotient.mk _ = _
  apply E.injective
  rw [← A.orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection]
  rw [← A.ellipticThreeBoundaryDeckStraightCentralLoop_class]
  rw [A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck]
  have hnat := A.ellipticThreeCentralCoverComparisonOfPath_ofDeck beta
    A.ellipticThreeBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
      (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase
        A.ellipticThreeBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation) at hnat
  rw [hnat, hdeck]
  exact (A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta
    orderThreeFillingRelationClassifiedCentralProductDeck).symm

/-- One complete filling-relation deck evaluation proves the order-four path-class marking. -/
public theorem ellipticFourCentralProductPathClassIdentity_of_deckMap_fillingRelation
    (hdeck :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderFourActualEllipticCentralProductPathClassIdentity := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let beta := A.ellipticFourCentralProductConnector
  let C := A.ellipticFourCentralCoverComparisonOfPath beta
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.centralAffineUniversalCoverPointOfPath beta,
      A.centralAffineUniversalCoverPointOfPath_projects beta⟩
  change Path.Homotopic.Quotient.mk _ = _
  apply E.injective
  rw [← A.orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection]
  rw [← A.ellipticFourBoundaryDeckStraightCentralLoop_class]
  rw [A.ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck]
  have hnat := A.ellipticFourCentralCoverComparisonOfPath_ofDeck beta
    A.ellipticFourBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
      (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase
        A.ellipticFourBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation) at hnat
  rw [hnat, hdeck]
  exact (A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta
    orderFourFillingRelationClassifiedCentralProductDeck).symm

/-- The order-three filling-relation deck evaluation also gives the equivalent cover-product
comparison. -/
public theorem ellipticThreeCentralCoverProductLiftComparison_of_deckMap_fillingRelation
    (hdeck :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderThreeActualEllipticCentralCoverProductLiftComparison :=
  A.orderThreeCentralCoverProductLiftComparison_iff_pathClassIdentity.mpr
    (A.ellipticThreeCentralProductPathClassIdentity_of_deckMap_fillingRelation hdeck)

/-- The order-four filling-relation deck evaluation also gives the equivalent cover-product
comparison. -/
public theorem ellipticFourCentralCoverProductLiftComparison_of_deckMap_fillingRelation
    (hdeck :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.OrderFourActualEllipticCentralCoverProductLiftComparison :=
  A.orderFourCentralCoverProductLiftComparison_iff_pathClassIdentity.mpr
    (A.ellipticFourCentralProductPathClassIdentity_of_deckMap_fillingRelation hdeck)

/-- The two connector-pinned filling-relation deck evaluations imply the remaining elliptic
normal-closure residual. -/
public theorem ellipticRelatorMembership_of_productConnectorDeckMaps
    (hThree :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹)
    (hFour :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    A.EllipticRelatorMembership A.cuspCentralNaturality :=
  A.ellipticRelatorMembership_of_centralProductPathClassIdentities
    (A.ellipticThreeCentralProductPathClassIdentity_of_deckMap_fillingRelation hThree)
    (A.ellipticFourCentralProductPathClassIdentity_of_deckMap_fillingRelation hFour)

/-- The same two evaluations supply the exact nonempty residual previously requested as an
established input. -/
public theorem ellipticRelatorMembership_nonempty_of_productConnectorDeckMaps
    (hThree :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹)
    (hFour :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) :
    Nonempty
      (EllipticRelatorMembership
        A A.cuspCentralNaturality) :=
  ⟨A.ellipticRelatorMembership_of_productConnectorDeckMaps hThree hFour⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
