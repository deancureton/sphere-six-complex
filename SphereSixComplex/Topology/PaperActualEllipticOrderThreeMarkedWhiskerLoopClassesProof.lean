module

public import SphereSixComplex.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

/-!
# Order-three straight loops in the marked-whisker deck coordinates
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The arbitrary central base whisker, with its source transported to the literal cusp base. -/
public noncomputable def orderThreeCentralMarkedWhiskerPath :
    Path A.actualCuspCentralBase A.orderThreeActualEllipticCentralBase :=
  A.orderThreeCentralBaseWhisker.cast
    A.centralAffineBase_eq_actualCuspCentralBase.symm rfl

/-- Pointwise form of the remaining chart calculation.  The explicitly based lift of the
overlap chart must carry the endpoints of the two straight deck segments to the corresponding
affine deck translates. -/
public def OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility : Prop :=
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let β := A.orderThreeCentralMarkedWhiskerPath
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  C.lift
      (A.orderThreeActualEllipticBoundaryDeckData.meridian •
        A.orderThreeActualEllipticBoundaryBase) =
      (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ •
        C.lift A.orderThreeActualEllipticBoundaryBase ∧
    C.lift
      (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)) •
        A.orderThreeActualEllipticBoundaryBase) =
      Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon) •
        C.lift A.orderThreeActualEllipticBoundaryBase

/-- The endpoint calculation is exactly the two required deck-map evaluations for the lift
pinned by the marked whisker. -/
public theorem OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility.deckMap
    (h : A.OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    let β := A.orderThreeCentralMarkedWhiskerPath
    let C := A.orderThreeActualCentralCoverComparisonOfPath β
    C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian =
        (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ ∧
      C.deckMap (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))) =
        Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let β := A.orderThreeCentralMarkedWhiskerPath
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  let _ : IsCancelSMul paperCentralFreeAffineDeck D.Cover :=
    D.data.quotientCovering.isCancelSMul
  change _ ∧ _ at h
  change _ ∧ _
  constructor
  · apply IsCancelSMul.right_cancel _ _ (C.lift A.orderThreeActualEllipticBoundaryBase)
    exact (C.equivariant _ _).symm.trans h.1
  · apply IsCancelSMul.right_cancel _ _ (C.lift A.orderThreeActualEllipticBoundaryBase)
    exact (C.equivariant _ _).symm.trans h.2

/-- The two pointwise endpoint formulas give the exact marked-whisker loop classes. -/
public theorem OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility.toLoopIdentities
    (h : A.OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility) :
    A.OrderThreeCentralBoundaryMarkedStraightLoopIdentities := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let β := A.orderThreeCentralMarkedWhiskerPath
  let C := A.orderThreeActualCentralCoverComparisonOfPath β
  let E := D.data.quotientCovering.fundamentalGroupEquiv
    ⟨A.orderThreeCentralAffineUniversalCoverPointOfPath β,
      A.orderThreeCentralAffineUniversalCoverPointOfPath_projects β⟩
  have hdeck := h.deckMap A
  change _ ∧ _ at hdeck
  change _ ∧ _
  constructor
  · have hmarked :
        FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker A.centralAffineCorePiOneData.rhoOne =
          FundamentalGroup.fundamentalGroupMulEquivOfPath β
            (paperPuncturedGlobalFamilyAffinePresentation A
              (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)) := by
      simpa [β, orderThreeCentralMarkedWhiskerPath, centralAffineCorePiOneData_rhoOne,
        paperPuncturedGlobalFamilyAffinePresentation, actualCuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
        fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
          A.orderThreeCentralBaseWhisker
          A.centralAffineBase_eq_actualCuspCentralBase.symm A.geometricCentralRhoOne
    have hnat := A.orderThreeActualCentralCoverComparisonOfPath_ofDeck β
      A.orderThreeActualEllipticBoundaryDeckData.meridian
    change E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.meridian)) =
      MulOpposite.op
        (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian) at hnat
    rw [A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck, hmarked]
    apply E.injective
    calc
      E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            A.orderThreeActualEllipticBoundaryDeckData.meridian)) =
          MulOpposite.op
            (C.deckMap A.orderThreeActualEllipticBoundaryDeckData.meridian) := by
              exact hnat
      _ = MulOpposite.op
          (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ := by
            rw [hdeck.1]
      _ = E (FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian))) :=
        (A.orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv β
          (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)).symm
  · have hmarked :
        FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderThreeCentralBaseWhisker
            (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) =
          FundamentalGroup.fundamentalGroupMulEquivOfPath β
            (paperPuncturedGlobalFamilyAffinePresentation A
              (Additive.toMul
                (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon)))) := by
      simpa [β, orderThreeCentralMarkedWhiskerPath,
        centralAffineCorePiOneData_translation,
        paperPuncturedGlobalFamilyAffinePresentation, actualCuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
        fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
          A.orderThreeCentralBaseWhisker
          A.centralAffineBase_eq_actualCuspCentralBase.symm
          (Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon)))
    have hnat := A.orderThreeActualCentralCoverComparisonOfPath_ofDeck β
      (Additive.toMul
        (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))
    change E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
        (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) =
      MulOpposite.op
        (C.deckMap (Additive.toMul
          (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) at hnat
    rw [A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck, hmarked]
    apply E.injective
    calc
      E (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl
          (ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
            A.orderThreeActualEllipticBoundaryBase
            (Additive.toMul
              (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))) =
          MulOpposite.op
            (C.deckMap (Additive.toMul
              (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) := by
              exact hnat
      _ = MulOpposite.op
          (Additive.toMul
            (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon)) := by
              rw [hdeck.2]
      _ = E (FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (paperPuncturedGlobalFamilyAffinePresentation A
            (Additive.toMul
              (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon))))) := by
        simpa only [map_neg, toMul_neg, inv_inv] using
          (A.orderThreeCentralAffineUniversalCoverPointOfPath_fundamentalGroupEquiv β
            (Additive.toMul
              (freeAffineTranslation (M := paperCentralFreeMonodromy) (-epsilon)))).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
