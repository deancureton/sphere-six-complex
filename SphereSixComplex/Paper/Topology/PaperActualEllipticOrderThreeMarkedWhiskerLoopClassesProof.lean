module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

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
    Path A.cuspCentralBase A.ellipticThreeCentralBase :=
  A.orderThreeCentralBaseWhisker.cast
    A.centralAffineBase_eq_actualCuspCentralBase.symm rfl

/-- Pointwise form of the remaining chart calculation.  The explicitly based lift of the
overlap chart must carry the endpoints of the two straight deck segments to the corresponding
affine deck translates. -/
public def OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility : Prop :=
  let _ := A.ellipticThreeBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let β := A.orderThreeCentralMarkedWhiskerPath
  let C := A.ellipticThreeCentralCoverComparisonOfPath β
  C.lift
      (A.ellipticThreeBoundaryDeckData.meridian •
        A.ellipticThreeBoundaryBase) =
      (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ •
        C.lift A.ellipticThreeBoundaryBase ∧
    C.lift
      (Additive.toMul
          (A.ellipticThreeBoundaryDeckData.translation (-epsilon)) •
        A.ellipticThreeBoundaryBase) =
      Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon) •
        C.lift A.ellipticThreeBoundaryBase

/-- The endpoint calculation is exactly the two required deck-map evaluations for the lift
pinned by the marked whisker. -/
public theorem OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility.deckMap
    (h : A.OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility) :
    letI := A.ellipticThreeBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    let β := A.orderThreeCentralMarkedWhiskerPath
    let C := A.ellipticThreeCentralCoverComparisonOfPath β
    C.deckMap A.ellipticThreeBoundaryDeckData.meridian =
        (freeAffineLift (M := paperCentralFreeMonodromy) firstMeridian)⁻¹ ∧
      C.deckMap (Additive.toMul
          (A.ellipticThreeBoundaryDeckData.translation (-epsilon))) =
        Additive.toMul
          (freeAffineTranslation (M := paperCentralFreeMonodromy) epsilon) := by
  let _ := A.ellipticThreeBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let β := A.orderThreeCentralMarkedWhiskerPath
  let C := A.ellipticThreeCentralCoverComparisonOfPath β
  let _ : IsCancelSMul paperCentralFreeAffineDeck D.Cover :=
    D.data.quotientCovering.isCancelSMul
  change _ ∧ _ at h
  change _ ∧ _
  constructor
  · apply IsCancelSMul.right_cancel _ _ (C.lift A.ellipticThreeBoundaryBase)
    exact (C.equivariant _ _).symm.trans h.1
  · apply IsCancelSMul.right_cancel _ _ (C.lift A.ellipticThreeBoundaryBase)
    exact (C.equivariant _ _).symm.trans h.2

/-- The two pointwise endpoint formulas give the exact marked-whisker loop classes. -/
public theorem OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility.toLoopIdentities
    (h : A.OrderThreeCentralMarkedWhiskerLiftEndpointCompatibility) :
    A.OrderThreeCentralBoundaryMarkedStraightLoopIdentities := by
  let _ := A.ellipticThreeBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let _ : SimplyConnectedSpace D.Cover := D.data.simplyConnected
  let β := A.orderThreeCentralMarkedWhiskerPath
  let C := A.ellipticThreeCentralCoverComparisonOfPath β
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
        paperPuncturedGlobalFamilyAffinePresentation, cuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
        fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
          A.orderThreeCentralBaseWhisker
          A.centralAffineBase_eq_actualCuspCentralBase.symm A.geometricCentralRhoOne
    have hnat := A.ellipticThreeCentralCoverComparisonOfPath_ofDeck β
      A.ellipticThreeBoundaryDeckData.meridian
    change E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
        (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
          A.ellipticThreeBoundaryDeckData.meridian)) =
      MulOpposite.op
        (C.deckMap A.ellipticThreeBoundaryDeckData.meridian) at hnat
    rw [A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck, hmarked]
    apply E.injective
    calc
      E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
          (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
            A.ellipticThreeBoundaryBase
            A.ellipticThreeBoundaryDeckData.meridian)) =
          MulOpposite.op
            (C.deckMap A.ellipticThreeBoundaryDeckData.meridian) := by
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
        paperPuncturedGlobalFamilyAffinePresentation, cuspToCentralAffineBaseEquiv,
        fundamentalGroupMulEquivOfEq_eq_elementOfBaseEq] using
        fundamentalGroupMulEquivOfPath_elementOfBaseEq_eq_cast_left
          A.orderThreeCentralBaseWhisker
          A.centralAffineBase_eq_actualCuspCentralBase.symm
          (Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon)))
    have hnat := A.ellipticThreeCentralCoverComparisonOfPath_ofDeck β
      (Additive.toMul
        (A.ellipticThreeBoundaryDeckData.translation (-epsilon)))
    change E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
        (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
          (Additive.toMul
            (A.ellipticThreeBoundaryDeckData.translation (-epsilon))))) =
      MulOpposite.op
        (C.deckMap (Additive.toMul
          (A.ellipticThreeBoundaryDeckData.translation (-epsilon)))) at hnat
    rw [A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck, hmarked]
    apply E.injective
    calc
      E (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl
          (ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
            A.ellipticThreeBoundaryBase
            (Additive.toMul
              (A.ellipticThreeBoundaryDeckData.translation (-epsilon))))) =
          MulOpposite.op
            (C.deckMap (Additive.toMul
              (A.ellipticThreeBoundaryDeckData.translation (-epsilon)))) := by
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
