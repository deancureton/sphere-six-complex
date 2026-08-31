module

public import SphereSixComplex.Topology.PaperActualEllipticConnectorDeckEvaluationCompletion

/-!
# Exact endpoint reduction for the actual elliptic relators

The canonical comparison lift has an unconditional based-path endpoint formula.  This file
identifies the remaining connector-pinned deck evaluations exactly with the corresponding
global affine-presentation classes.  Thus no point-set equality of chosen representatives is
needed, but a class-level marking of each chosen van Kampen connector is still necessary.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The order-three global path-class marking also forces the exact deck value of the
connector-pinned comparison. -/
public theorem
    orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity
    (h : A.OrderThreeActualEllipticCentralProductPathClassIdentity) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderThreeActualCentralProductConnector
    let C := A.orderThreeActualCentralCoverComparisonOfPath beta
    C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
      orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ := by
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
  change Path.Homotopic.Quotient.mk _ = _ at h
  rw [← A.orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection,
    ← A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class,
    A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck] at h
  have hnat := A.orderThreeActualCentralCoverComparisonOfPath_ofDeck beta
    A.orderThreeActualEllipticBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
      (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) at hnat
  apply MulOpposite.op_injective
  calc
    MulOpposite.op (C.deckMap
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) =
        E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)) := hnat.symm
    _ = E (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck)) := congrArg E h
    _ = MulOpposite.op orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ :=
      A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta _

/-- The order-four global path-class marking forces the corresponding exact deck value. -/
public theorem
    orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity
    (h : A.OrderFourActualEllipticCentralProductPathClassIdentity) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderFourActualCentralProductConnector
    let C := A.orderFourActualCentralCoverComparisonOfPath beta
    C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
      orderFourFillingRelationClassifiedCentralProductDeck⁻¹ := by
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
  change Path.Homotopic.Quotient.mk _ = _ at h
  rw [← A.orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection,
    ← A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_class,
    A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck] at h
  have hnat := A.orderFourActualCentralCoverComparisonOfPath_ofDeck beta
    A.orderFourActualEllipticBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
      (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation) at hnat
  apply MulOpposite.op_injective
  calc
    MulOpposite.op (C.deckMap
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation) =
        E (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl
          (ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderFourActualEllipticBoundaryBase
            A.orderFourActualEllipticBoundaryDeckData.fillingRelation)) := hnat.symm
    _ = E (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck)) := congrArg E h
    _ = MulOpposite.op orderFourFillingRelationClassifiedCentralProductDeck⁻¹ :=
      A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta _

/-- The order-three deck evaluation is exactly the remaining transported path-class identity. -/
public theorem
    orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_iff_pathClassIdentity :
    (letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) ↔
      A.OrderThreeActualEllipticCentralProductPathClassIdentity :=
  ⟨A.orderThreeActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation,
    A.orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity⟩

/-- The order-four deck evaluation is exactly the remaining transported path-class identity. -/
public theorem
    orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_iff_pathClassIdentity :
    (letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) ↔
      A.OrderFourActualEllipticCentralProductPathClassIdentity :=
  ⟨A.orderFourActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation,
    A.orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity⟩

/-- The order-three connector-pinned lift endpoint is equivalent to the exact remaining
fundamental-group marking. -/
public theorem
    orderThreeActualCentralProductCoverComparison_endpoint_iff_pathClassIdentity :
    (letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
            A.orderThreeActualEllipticBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderThreeActualEllipticBoundaryBase) ↔
      A.OrderThreeActualEllipticCentralProductPathClassIdentity := by
  rw [← A.orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint]
  constructor
  · exact A.orderThreeActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation
  · exact A.orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity

/-- The order-four connector-pinned lift endpoint is equivalent to its exact remaining
fundamental-group marking. -/
public theorem
    orderFourActualCentralProductCoverComparison_endpoint_iff_pathClassIdentity :
    (letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
            A.orderFourActualEllipticBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderFourActualEllipticBoundaryBase) ↔
      A.OrderFourActualEllipticCentralProductPathClassIdentity := by
  rw [← A.orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint]
  constructor
  · exact A.orderFourActualEllipticCentralProductPathClassIdentity_of_deckMap_fillingRelation
  · exact A.orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity

/-- The two concrete class-level markings give the requested nonempty residual. -/
public theorem
    actualEllipticRelatorNormalClosureResidual_nonempty_of_centralProductPathClassIdentities
    (hThree : A.OrderThreeActualEllipticCentralProductPathClassIdentity)
    (hFour : A.OrderFourActualEllipticCentralProductPathClassIdentity) :
    Nonempty
      (ActualEllipticRelatorNormalClosureResidual
        A A.actualCuspCentralNaturality) :=
  ⟨A.actualEllipticRelatorNormalClosureResidual_of_centralProductPathClassIdentities
    hThree hFour⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
