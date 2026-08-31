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

/-- A path-class comparison along any explicit order-three connector gives the
connector-invariant whole-relator identity. -/
public theorem orderThreeWholeFillingRelatorChartIdentity_of_pathClassIdentity_at
    (beta : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase)
    (h :
      letI := A.orderThreeActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck)) :
    A.OrderThreeWholeFillingRelatorChartIdentity := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let alpha := beta.cast A.centralAffineBase_eq_actualCuspCentralBase rfl
  have hcast :
      alpha.cast A.centralAffineBase_eq_actualCuspCentralBase.symm rfl = beta := by
    apply Path.ext
    funext t
    rfl
  have htransport :
      FundamentalGroup.fundamentalGroupMulEquivOfPath
          alpha A.orderThreeCentralExpectedRelator =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck) := by
    rw [A.orderThreeCentralExpectedRelator_eq_classifiedPresentation]
    rw [show A.actualCuspToCentralAffineBaseEquiv
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck) =
        fundamentalGroupElementOfBaseEq
          A.centralAffineBase_eq_actualCuspCentralBase.symm
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck) by
      simp [actualCuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq]]
    rw [fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left, hcast]
  let hover := A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
  refine ⟨alpha.cast rfl hover.symm, ?_⟩
  rw [A.orderThreeActualCanonicalRelatorInCentral_eq_regularLoopProjection]
  change fundamentalGroupElementOfBaseEq hover (Path.Homotopic.Quotient.mk _) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (alpha.cast rfl hover.symm) A.orderThreeCentralExpectedRelator
  rw [h, ← htransport]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    alpha hover.symm A.orderThreeCentralExpectedRelator).symm

/-- The order-four analogue for an arbitrary explicit connector. -/
public theorem orderFourWholeFillingRelatorChartIdentity_of_pathClassIdentity_at
    (beta : Path A.actualCuspCentralBase A.orderFourActualEllipticCentralBase)
    (h :
      letI := A.orderFourActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck)) :
    A.OrderFourWholeFillingRelatorChartIdentity := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let alpha := beta.cast A.centralAffineBase_eq_actualCuspCentralBase rfl
  have hcast :
      alpha.cast A.centralAffineBase_eq_actualCuspCentralBase.symm rfl = beta := by
    apply Path.ext
    funext t
    rfl
  have htransport :
      FundamentalGroup.fundamentalGroupMulEquivOfPath
          alpha A.orderFourCentralExpectedRelator =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck) := by
    rw [A.orderFourCentralExpectedRelator_eq_classifiedPresentation]
    rw [show A.actualCuspToCentralAffineBaseEquiv
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck) =
        fundamentalGroupElementOfBaseEq
          A.centralAffineBase_eq_actualCuspCentralBase.symm
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck) by
      simp [actualCuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq]]
    rw [fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left, hcast]
  let hover := A.orderFourActualEllipticCentralBase_eq_overlapCentralBase
  refine ⟨alpha.cast rfl hover.symm, ?_⟩
  rw [A.orderFourActualCanonicalRelatorInCentral_eq_regularLoopProjection]
  change fundamentalGroupElementOfBaseEq hover (Path.Homotopic.Quotient.mk _) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (alpha.cast rfl hover.symm) A.orderFourCentralExpectedRelator
  rw [h, ← htransport]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    alpha hover.symm A.orderFourCentralExpectedRelator).symm

/-- Explicit connectors with the two correct path classes suffice for the invariant residual;
they need not be the arbitrary connectors stored in the van Kampen cover. -/
public theorem actualEllipticRelatorNormalClosureResidual_nonempty_of_pathClassIdentities_at
    (betaThree : Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase)
    (betaFour : Path A.actualCuspCentralBase A.orderFourActualEllipticCentralBase)
    (hThree :
      letI := A.orderThreeActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath betaThree
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck))
    (hFour :
      letI := A.orderFourActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath betaFour
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck)) :
    Nonempty (ActualEllipticRelatorNormalClosureResidual
      A A.actualCuspCentralNaturality) :=
  ⟨A.actualEllipticRelatorNormalClosureResidual_of_wholeFillingRelatorChartIdentities
    (A.orderThreeWholeFillingRelatorChartIdentity_of_pathClassIdentity_at betaThree hThree)
    (A.orderFourWholeFillingRelatorChartIdentity_of_pathClassIdentity_at betaFour hFour)⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
