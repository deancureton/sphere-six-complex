module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticConnectorDeckEvaluationCompletion

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
    ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity
    (h : A.OrderThreeActualEllipticCentralProductPathClassIdentity) :
    letI := A.ellipticThreeBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.ellipticThreeCentralProductConnector
    let C := A.ellipticThreeCentralCoverComparisonOfPath beta
    C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
      orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ := by
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
  change Path.Homotopic.Quotient.mk _ = _ at h
  rw [← A.orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection,
    ← A.ellipticThreeBoundaryDeckStraightCentralLoop_class,
    A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck] at h
  have hnat := A.ellipticThreeCentralCoverComparisonOfPath_ofDeck beta
    A.ellipticThreeBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
      (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase
        A.ellipticThreeBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap
      A.ellipticThreeBoundaryDeckData.fillingRelation) at hnat
  apply MulOpposite.op_injective
  calc
    MulOpposite.op (C.deckMap
        A.ellipticThreeBoundaryDeckData.fillingRelation) =
        E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
          (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
            A.ellipticThreeBoundaryBase
            A.ellipticThreeBoundaryDeckData.fillingRelation)) := hnat.symm
    _ = E (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck)) := congrArg E h
    _ = MulOpposite.op orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ :=
      A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta _

/-- The order-four global path-class marking forces the corresponding exact deck value. -/
public theorem
    ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity
    (h : A.OrderFourActualEllipticCentralProductPathClassIdentity) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.ellipticFourCentralProductConnector
    let C := A.ellipticFourCentralCoverComparisonOfPath beta
    C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
      orderFourFillingRelationClassifiedCentralProductDeck⁻¹ := by
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
  change Path.Homotopic.Quotient.mk _ = _ at h
  rw [← A.orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection,
    ← A.ellipticFourBoundaryDeckStraightCentralLoop_class,
    A.ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck] at h
  have hnat := A.ellipticFourCentralCoverComparisonOfPath_ofDeck beta
    A.ellipticFourBoundaryDeckData.fillingRelation
  change E (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
      (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase
        A.ellipticFourBoundaryDeckData.fillingRelation)) =
    MulOpposite.op (C.deckMap
      A.ellipticFourBoundaryDeckData.fillingRelation) at hnat
  apply MulOpposite.op_injective
  calc
    MulOpposite.op (C.deckMap
        A.ellipticFourBoundaryDeckData.fillingRelation) =
        E (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
          (ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
            A.ellipticFourBoundaryBase
            A.ellipticFourBoundaryDeckData.fillingRelation)) := hnat.symm
    _ = E (FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck)) := congrArg E h
    _ = MulOpposite.op orderFourFillingRelationClassifiedCentralProductDeck⁻¹ :=
      A.centralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv beta _

/-- The order-three deck evaluation is exactly the remaining transported path-class identity. -/
public theorem
    ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_iff_pathClassIdentity :
    (letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) ↔
      A.OrderThreeActualEllipticCentralProductPathClassIdentity :=
  ⟨A.ellipticThreeCentralProductPathClassIdentity_of_deckMap_fillingRelation,
    A.ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity⟩

/-- The order-four deck evaluation is exactly the remaining transported path-class identity. -/
public theorem
    ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_iff_pathClassIdentity :
    (letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) ↔
      A.OrderFourActualEllipticCentralProductPathClassIdentity :=
  ⟨A.ellipticFourCentralProductPathClassIdentity_of_deckMap_fillingRelation,
    A.ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity⟩

/-- The order-three connector-pinned lift endpoint is equivalent to the exact remaining
fundamental-group marking. -/
public theorem
    ellipticThreeCentralProductCoverComparison_endpoint_iff_pathClassIdentity :
    (letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticThreeBoundaryDeckData.fillingRelation •
            A.ellipticThreeBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticThreeBoundaryBase) ↔
      A.OrderThreeActualEllipticCentralProductPathClassIdentity := by
  rw [← A.ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint]
  constructor
  · exact A.ellipticThreeCentralProductPathClassIdentity_of_deckMap_fillingRelation
  · exact A.ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity

/-- The order-four connector-pinned lift endpoint is equivalent to its exact remaining
fundamental-group marking. -/
public theorem
    ellipticFourCentralProductCoverComparison_endpoint_iff_pathClassIdentity :
    (letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticFourBoundaryDeckData.fillingRelation •
            A.ellipticFourBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticFourBoundaryBase) ↔
      A.OrderFourActualEllipticCentralProductPathClassIdentity := by
  rw [← A.ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint]
  constructor
  · exact A.ellipticFourCentralProductPathClassIdentity_of_deckMap_fillingRelation
  · exact A.ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_of_pathClassIdentity

/-- The two concrete class-level markings give the requested nonempty residual. -/
public theorem
    ellipticRelatorMembership_nonempty_of_centralProductPathClassIdentities
    (hThree : A.OrderThreeActualEllipticCentralProductPathClassIdentity)
    (hFour : A.OrderFourActualEllipticCentralProductPathClassIdentity) :
    Nonempty
      (EllipticRelatorMembership
        A A.cuspCentralNaturality) :=
  ⟨A.ellipticRelatorMembership_of_centralProductPathClassIdentities
    hThree hFour⟩

/-- A path-class comparison along any explicit order-three connector gives the
connector-invariant whole-relator identity. -/
public theorem orderThreeWholeFillingRelatorChartIdentity_of_pathClassIdentity_at
    (beta : Path A.cuspCentralBase A.ellipticThreeCentralBase)
    (h :
      letI := A.ellipticThreeBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck)) :
    A.OrderThreeWholeFillingRelatorChartIdentity := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let alpha := beta.cast A.centralAffineBase_eq_cuspCentralBase rfl
  have hcast :
      alpha.cast A.centralAffineBase_eq_cuspCentralBase.symm rfl = beta := by
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
    rw [show A.cuspToCentralAffineBaseEquiv
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck) =
        fundamentalGroupElementOfBaseEq
          A.centralAffineBase_eq_cuspCentralBase.symm
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck) by
      simp [cuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq]]
    rw [fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left, hcast]
  let hover := A.ellipticThreeCentralBase_eq_overlapCentralBase
  refine ⟨alpha.cast rfl hover.symm, ?_⟩
  rw [A.ellipticThreeCanonicalRelatorInCentral_eq_regularLoopProjection]
  change fundamentalGroupElementOfBaseEq hover (Path.Homotopic.Quotient.mk _) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (alpha.cast rfl hover.symm) A.orderThreeCentralExpectedRelator
  rw [h, ← htransport]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    alpha hover.symm A.orderThreeCentralExpectedRelator).symm

/-- The order-four analogue for an arbitrary explicit connector. -/
public theorem orderFourWholeFillingRelatorChartIdentity_of_pathClassIdentity_at
    (beta : Path A.cuspCentralBase A.ellipticFourCentralBase)
    (h :
      letI := A.ellipticFourBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath beta
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck)) :
    A.OrderFourWholeFillingRelatorChartIdentity := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let alpha := beta.cast A.centralAffineBase_eq_cuspCentralBase rfl
  have hcast :
      alpha.cast A.centralAffineBase_eq_cuspCentralBase.symm rfl = beta := by
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
    rw [show A.cuspToCentralAffineBaseEquiv
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck) =
        fundamentalGroupElementOfBaseEq
          A.centralAffineBase_eq_cuspCentralBase.symm
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck) by
      simp [cuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq]]
    rw [fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left, hcast]
  let hover := A.ellipticFourCentralBase_eq_overlapCentralBase
  refine ⟨alpha.cast rfl hover.symm, ?_⟩
  rw [A.ellipticFourCanonicalRelatorInCentral_eq_regularLoopProjection]
  change fundamentalGroupElementOfBaseEq hover (Path.Homotopic.Quotient.mk _) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      (alpha.cast rfl hover.symm) A.orderFourCentralExpectedRelator
  rw [h, ← htransport]
  exact (fundamentalGroupMulEquivOfPath_cast_right
    alpha hover.symm A.orderFourCentralExpectedRelator).symm

/-- Explicit connectors with the two correct path classes suffice for the invariant residual;
they need not be the arbitrary connectors stored in the van Kampen cover. -/
public theorem ellipticRelatorMembership_nonempty_of_pathClassIdentities_at
    (betaThree : Path A.cuspCentralBase A.ellipticThreeCentralBase)
    (betaFour : Path A.cuspCentralBase A.ellipticFourCentralBase)
    (hThree :
      letI := A.ellipticThreeBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath betaThree
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderThreeFillingRelationClassifiedCentralProductDeck))
    (hFour :
      letI := A.ellipticFourBoundaryAction
      Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath betaFour
          (paperPuncturedGlobalFamilyAffinePresentation A
            orderFourFillingRelationClassifiedCentralProductDeck)) :
    Nonempty (EllipticRelatorMembership
      A A.cuspCentralNaturality) :=
  ⟨A.ellipticRelatorMembership_of_wholeFillingRelatorChartIdentities
    (A.orderThreeWholeFillingRelatorChartIdentity_of_pathClassIdentity_at betaThree hThree)
    (A.orderFourWholeFillingRelatorChartIdentity_of_pathClassIdentity_at betaFour hFour)⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
