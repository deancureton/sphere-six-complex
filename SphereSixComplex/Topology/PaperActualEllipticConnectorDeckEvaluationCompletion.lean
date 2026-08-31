module

public import SphereSixComplex.Topology.PaperActualEllipticCentralConnectorMarkingProof

/-!
# Connector-pinned elliptic deck evaluations

The canonical cover comparison is constructed by the unique lifting property.  Its deck value on
the complete filling relation is therefore fixed by one endpoint equality for that lift.  This
file converts those two concrete endpoint equalities into the order-three and order-four deck
evaluations, path-class identities, cover comparisons, and the exact normal-closure residual.
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

/-- Along a straight order-three deck path, the canonical comparison lift is the unique path
lift of its image in the central family. -/
public theorem orderThreeActualCentralProductCoverComparison_lift_deckTranslate_eq_liftPath
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderThreeActualCentralProductConnector
    let C := A.orderThreeActualCentralCoverComparisonOfPath beta
    let delta := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g
    let e := A.centralAffineUniversalCoverPointOfPath beta
    C.lift (g • A.orderThreeActualEllipticBoundaryBase) =
      D.data.quotientCovering.isCoveringMap.liftPath delta e
        (delta.source.trans
          (A.centralAffineUniversalCoverPointOfPath_projects beta).symm) 1 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  let C := A.orderThreeActualCentralCoverComparisonOfPath beta
  let Gamma := A.orderThreeActualEllipticBoundaryDeckStraightLift g
  let delta := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g
  let e := A.centralAffineUniversalCoverPointOfPath beta
  let hzero : delta 0 = D.data.projection e :=
    delta.source.trans
      (A.centralAffineUniversalCoverPointOfPath_projects beta).symm
  have hlift :
      (fun t => C.lift (Gamma t)) =
        D.data.quotientCovering.isCoveringMap.liftPath delta e hzero := by
    apply (D.data.quotientCovering.isCoveringMap.eq_liftPath_iff _).2
    refine ⟨C.lift.continuous.comp Gamma.continuous, ?_, ?_⟩
    · funext t
      change D.data.projection (C.lift (Gamma t)) = delta t
      rw [← C.commutes]
      rfl
    · change C.lift (Gamma 0) = e
      rw [Gamma.source]
      exact A.orderThreeActualCentralCoverComparisonOfPath_lift_base beta
  have hone := congrFun hlift 1
  simpa [Gamma, delta, e, hzero] using hone

/-- Along a straight order-four deck path, the canonical comparison lift is the unique path
lift of its image in the central family. -/
public theorem orderFourActualCentralProductCoverComparison_lift_deckTranslate_eq_liftPath
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderFourActualCentralProductConnector
    let C := A.orderFourActualCentralCoverComparisonOfPath beta
    let delta := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g
    let e := A.centralAffineUniversalCoverPointOfPath beta
    C.lift (g • A.orderFourActualEllipticBoundaryBase) =
      D.data.quotientCovering.isCoveringMap.liftPath delta e
        (delta.source.trans
          (A.centralAffineUniversalCoverPointOfPath_projects beta).symm) 1 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  let C := A.orderFourActualCentralCoverComparisonOfPath beta
  let Gamma := A.orderFourActualEllipticBoundaryDeckStraightLift g
  let delta := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g
  let e := A.centralAffineUniversalCoverPointOfPath beta
  let hzero : delta 0 = D.data.projection e :=
    delta.source.trans
      (A.centralAffineUniversalCoverPointOfPath_projects beta).symm
  have hlift :
      (fun t => C.lift (Gamma t)) =
        D.data.quotientCovering.isCoveringMap.liftPath delta e hzero := by
    apply (D.data.quotientCovering.isCoveringMap.eq_liftPath_iff _).2
    refine ⟨C.lift.continuous.comp Gamma.continuous, ?_, ?_⟩
    · funext t
      change D.data.projection (C.lift (Gamma t)) = delta t
      rw [← C.commutes]
      rfl
    · change C.lift (Gamma 0) = e
      rw [Gamma.source]
      exact A.orderFourActualCentralCoverComparisonOfPath_lift_base beta
  have hone := congrFun hlift 1
  simpa [Gamma, delta, e, hzero] using hone

/-- The actual order-three comparison endpoint is the based-path class obtained by appending
the mapped straight loop to the prescribed connector. -/
public theorem orderThreeActualCentralProductCoverComparison_lift_deckTranslate_eq_append
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderThreeActualCentralProductConnector
    let C := A.orderThreeActualCentralCoverComparisonOfPath beta
    let delta := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g
    let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
    C.lift (g • A.orderThreeActualEllipticBoundaryBase) =
      TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.append (BasedPath.ofPath beta) eta) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : LocallyPathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_locallyPathConnected
      A.modular.modularParameter A.periods
  let _ : PathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_pathConnected
      A.modular.modularParameter A.periods
  let _ : TauCeti.SemilocallySimplyConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_semilocallySimplyConnected
      A.modular.modularParameter A.periods
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  let C := A.orderThreeActualCentralCoverComparisonOfPath beta
  let delta := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g
  let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
  change C.lift (g • A.orderThreeActualEllipticBoundaryBase) =
    TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
      (BasedPath.append (BasedPath.ofPath beta) eta)
  rw [A.orderThreeActualCentralProductCoverComparison_lift_deckTranslate_eq_liftPath g]
  change (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath delta
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.ofPath beta)) _ 1 = _
  calc
    _ = (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath eta
        (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
          (BasedPath.ofPath beta)) (by simp) 1 := by congr 1
    _ = _ := TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append eta

/-- The actual order-four comparison endpoint has the same connector-append description. -/
public theorem orderFourActualCentralProductCoverComparison_lift_deckTranslate_eq_append
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.orderFourActualCentralProductConnector
    let C := A.orderFourActualCentralCoverComparisonOfPath beta
    let delta := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g
    let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
    C.lift (g • A.orderFourActualEllipticBoundaryBase) =
      TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.append (BasedPath.ofPath beta) eta) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : LocallyPathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_locallyPathConnected
      A.modular.modularParameter A.periods
  let _ : PathConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_pathConnected
      A.modular.modularParameter A.periods
  let _ : TauCeti.SemilocallySimplyConnectedSpace A.CentralFamily :=
    fuchsianPuncturedGlobalFamily_semilocallySimplyConnected
      A.modular.modularParameter A.periods
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  let C := A.orderFourActualCentralCoverComparisonOfPath beta
  let delta := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g
  let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
  change C.lift (g • A.orderFourActualEllipticBoundaryBase) =
    TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
      (BasedPath.append (BasedPath.ofPath beta) eta)
  rw [A.orderFourActualCentralProductCoverComparison_lift_deckTranslate_eq_liftPath g]
  change (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath delta
      (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
        (BasedPath.ofPath beta)) _ 1 = _
  calc
    _ = (TauCeti.UniversalCover.isCoveringMap A.actualCuspCentralBase).liftPath eta
        (TauCeti.UniversalCover.ofBasedPath A.actualCuspCentralBase
          (BasedPath.ofPath beta)) (by simp) 1 := by congr 1
    _ = _ := TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append eta

/-- The endpoint of the connector-pinned order-three lift determines its deck value on the
complete filling relation. -/
public theorem orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint
    (hendpoint :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
            A.orderThreeActualEllipticBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderThreeActualEllipticBoundaryBase) :
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
  let _ : IsCancelSMul paperCentralFreeAffineDeck D.Cover :=
    D.data.quotientCovering.isCancelSMul
  let beta := A.orderThreeActualCentralProductConnector
  let C := A.orderThreeActualCentralCoverComparisonOfPath beta
  apply IsCancelSMul.right_cancel _ _ (C.lift A.orderThreeActualEllipticBoundaryBase)
  exact (C.equivariant A.orderThreeActualEllipticBoundaryDeckData.fillingRelation
    A.orderThreeActualEllipticBoundaryBase).symm.trans hendpoint

/-- The endpoint of the connector-pinned order-four lift determines its deck value on the
complete filling relation. -/
public theorem orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint
    (hendpoint :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
            A.orderFourActualEllipticBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderFourActualEllipticBoundaryBase) :
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
  let _ : IsCancelSMul paperCentralFreeAffineDeck D.Cover :=
    D.data.quotientCovering.isCancelSMul
  let beta := A.orderFourActualCentralProductConnector
  let C := A.orderFourActualCentralCoverComparisonOfPath beta
  apply IsCancelSMul.right_cancel _ _ (C.lift A.orderFourActualEllipticBoundaryBase)
  exact (C.equivariant A.orderFourActualEllipticBoundaryDeckData.fillingRelation
    A.orderFourActualEllipticBoundaryBase).symm.trans hendpoint

/-- The order-three endpoint equality is exactly equivalent to the requested deck evaluation. -/
public theorem orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint :
    (letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) ↔
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
            C.lift A.orderThreeActualEllipticBoundaryBase) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let beta := A.orderThreeActualCentralProductConnector
  let C := A.orderThreeActualCentralCoverComparisonOfPath beta
  constructor
  · intro hdeck
    change C.deckMap A.orderThreeActualEllipticBoundaryDeckData.fillingRelation =
      orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ at hdeck
    change C.lift
        (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
          A.orderThreeActualEllipticBoundaryBase) = _
    rw [C.equivariant, hdeck]
  · exact A.orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint

/-- The order-four endpoint equality is exactly equivalent to the requested deck evaluation. -/
public theorem orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint :
    (letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) ↔
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
            C.lift A.orderFourActualEllipticBoundaryBase) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let beta := A.orderFourActualCentralProductConnector
  let C := A.orderFourActualCentralCoverComparisonOfPath beta
  constructor
  · intro hdeck
    change C.deckMap A.orderFourActualEllipticBoundaryDeckData.fillingRelation =
      orderFourFillingRelationClassifiedCentralProductDeck⁻¹ at hdeck
    change C.lift
        (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
          A.orderFourActualEllipticBoundaryBase) = _
    rw [C.equivariant, hdeck]
  · exact A.orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint

/-- The two connector-pinned endpoint equalities give the exact remaining elliptic residual. -/
public theorem actualEllipticRelatorNormalClosureResidual_of_productConnectorLiftEndpoints
    (hThree :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
            A.orderThreeActualEllipticBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderThreeActualEllipticBoundaryBase)
    (hFour :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
            A.orderFourActualEllipticBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderFourActualEllipticBoundaryBase) :
    A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality :=
  A.actualEllipticRelatorNormalClosureResidual_of_productConnectorDeckMaps
    (A.orderThreeActualCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint hThree)
    (A.orderFourActualCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint hFour)

/-- The same two endpoint equalities supply the exact nonempty established-input target. -/
public theorem
    actualEllipticRelatorNormalClosureResidual_nonempty_of_productConnectorLiftEndpoints
    (hThree :
      letI := A.orderThreeActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderThreeActualCentralProductConnector
      let C := A.orderThreeActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
            A.orderThreeActualEllipticBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderThreeActualEllipticBoundaryBase)
    (hFour :
      letI := A.orderFourActualEllipticBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.orderFourActualCentralProductConnector
      let C := A.orderFourActualCentralCoverComparisonOfPath beta
      C.lift
          (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
            A.orderFourActualEllipticBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.orderFourActualEllipticBoundaryBase) :
    Nonempty
      (ActualEllipticRelatorNormalClosureResidual
        A A.actualCuspCentralNaturality) :=
  ⟨A.actualEllipticRelatorNormalClosureResidual_of_productConnectorLiftEndpoints
    hThree hFour⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
