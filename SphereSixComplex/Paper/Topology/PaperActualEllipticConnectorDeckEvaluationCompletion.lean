module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralConnectorMarkingProof

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
public theorem ellipticThreeCentralProductCoverComparison_lift_deckTranslate_eq_liftPath
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.ellipticThreeCentralProductConnector
    let C := A.ellipticThreeCentralCoverComparisonOfPath beta
    let delta := A.ellipticThreeBoundaryDeckStraightCentralLoop g
    let e := A.centralAffineUniversalCoverPointOfPath beta
    C.lift (g • A.ellipticThreeBoundaryBase) =
      D.data.quotientCovering.isCoveringMap.liftPath delta e
        (delta.source.trans
          (A.centralAffineUniversalCoverPointOfPath_projects beta).symm) 1 := by
  let _ := A.ellipticThreeBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let beta := A.ellipticThreeCentralProductConnector
  let C := A.ellipticThreeCentralCoverComparisonOfPath beta
  let Gamma := A.ellipticThreeBoundaryDeckStraightLift g
  let delta := A.ellipticThreeBoundaryDeckStraightCentralLoop g
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
      exact A.ellipticThreeCentralCoverComparisonOfPath_lift_base beta
  have hone := congrFun hlift 1
  simpa [Gamma, delta, e, hzero] using hone

/-- Along a straight order-four deck path, the canonical comparison lift is the unique path
lift of its image in the central family. -/
public theorem ellipticFourCentralProductCoverComparison_lift_deckTranslate_eq_liftPath
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.ellipticFourCentralProductConnector
    let C := A.ellipticFourCentralCoverComparisonOfPath beta
    let delta := A.ellipticFourBoundaryDeckStraightCentralLoop g
    let e := A.centralAffineUniversalCoverPointOfPath beta
    C.lift (g • A.ellipticFourBoundaryBase) =
      D.data.quotientCovering.isCoveringMap.liftPath delta e
        (delta.source.trans
          (A.centralAffineUniversalCoverPointOfPath_projects beta).symm) 1 := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let beta := A.ellipticFourCentralProductConnector
  let C := A.ellipticFourCentralCoverComparisonOfPath beta
  let Gamma := A.ellipticFourBoundaryDeckStraightLift g
  let delta := A.ellipticFourBoundaryDeckStraightCentralLoop g
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
      exact A.ellipticFourCentralCoverComparisonOfPath_lift_base beta
  have hone := congrFun hlift 1
  simpa [Gamma, delta, e, hzero] using hone

/-- The actual order-three comparison endpoint is the based-path class obtained by appending
the mapped straight loop to the prescribed connector. -/
public theorem ellipticThreeCentralProductCoverComparison_lift_deckTranslate_eq_append
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.ellipticThreeCentralProductConnector
    let C := A.ellipticThreeCentralCoverComparisonOfPath beta
    let delta := A.ellipticThreeBoundaryDeckStraightCentralLoop g
    let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
    C.lift (g • A.ellipticThreeBoundaryBase) =
      TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
        (BasedPath.append (BasedPath.ofPath beta) eta) := by
  let _ := A.ellipticThreeBoundaryAction
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
    A.ellipticThreeBoundaryCover_simplyConnected
  let beta := A.ellipticThreeCentralProductConnector
  let C := A.ellipticThreeCentralCoverComparisonOfPath beta
  let delta := A.ellipticThreeBoundaryDeckStraightCentralLoop g
  let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
  change C.lift (g • A.ellipticThreeBoundaryBase) =
    TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
      (BasedPath.append (BasedPath.ofPath beta) eta)
  rw [A.ellipticThreeCentralProductCoverComparison_lift_deckTranslate_eq_liftPath g]
  change (TauCeti.UniversalCover.isCoveringMap A.cuspCentralBase).liftPath delta
      (TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
        (BasedPath.ofPath beta)) _ 1 = _
  calc
    _ = (TauCeti.UniversalCover.isCoveringMap A.cuspCentralBase).liftPath eta
        (TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
          (BasedPath.ofPath beta)) (by simp) 1 := by congr 1
    _ = _ := TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append eta

/-- The actual order-four comparison endpoint has the same connector-append description. -/
public theorem ellipticFourCentralProductCoverComparison_lift_deckTranslate_eq_append
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    let D := A.centralAffineUniversalCover
    letI := D.topology
    letI := D.action
    let beta := A.ellipticFourCentralProductConnector
    let C := A.ellipticFourCentralCoverComparisonOfPath beta
    let delta := A.ellipticFourBoundaryDeckStraightCentralLoop g
    let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
    C.lift (g • A.ellipticFourBoundaryBase) =
      TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
        (BasedPath.append (BasedPath.ofPath beta) eta) := by
  let _ := A.ellipticFourBoundaryAction
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
    A.ellipticFourBoundaryCover_simplyConnected
  let beta := A.ellipticFourCentralProductConnector
  let C := A.ellipticFourCentralCoverComparisonOfPath beta
  let delta := A.ellipticFourBoundaryDeckStraightCentralLoop g
  let eta := delta.cast (BasedPath.endpoint_ofPath beta) rfl
  change C.lift (g • A.ellipticFourBoundaryBase) =
    TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
      (BasedPath.append (BasedPath.ofPath beta) eta)
  rw [A.ellipticFourCentralProductCoverComparison_lift_deckTranslate_eq_liftPath g]
  change (TauCeti.UniversalCover.isCoveringMap A.cuspCentralBase).liftPath delta
      (TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
        (BasedPath.ofPath beta)) _ 1 = _
  calc
    _ = (TauCeti.UniversalCover.isCoveringMap A.cuspCentralBase).liftPath eta
        (TauCeti.UniversalCover.ofBasedPath A.cuspCentralBase
          (BasedPath.ofPath beta)) (by simp) 1 := by congr 1
    _ = _ := TauCeti.UniversalCover.liftPath_apply_one_eq_ofBasedPath_append eta

/-- The endpoint of the connector-pinned order-three lift determines its deck value on the
complete filling relation. -/
public theorem ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint
    (hendpoint :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticThreeBoundaryDeckData.fillingRelation •
            A.ellipticThreeBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticThreeBoundaryBase) :
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
  let _ : IsCancelSMul paperCentralFreeAffineDeck D.Cover :=
    D.data.quotientCovering.isCancelSMul
  let beta := A.ellipticThreeCentralProductConnector
  let C := A.ellipticThreeCentralCoverComparisonOfPath beta
  apply IsCancelSMul.right_cancel _ _ (C.lift A.ellipticThreeBoundaryBase)
  exact (C.equivariant A.ellipticThreeBoundaryDeckData.fillingRelation
    A.ellipticThreeBoundaryBase).symm.trans hendpoint

/-- The endpoint of the connector-pinned order-four lift determines its deck value on the
complete filling relation. -/
public theorem ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint
    (hendpoint :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticFourBoundaryDeckData.fillingRelation •
            A.ellipticFourBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticFourBoundaryBase) :
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
  let _ : IsCancelSMul paperCentralFreeAffineDeck D.Cover :=
    D.data.quotientCovering.isCancelSMul
  let beta := A.ellipticFourCentralProductConnector
  let C := A.ellipticFourCentralCoverComparisonOfPath beta
  apply IsCancelSMul.right_cancel _ _ (C.lift A.ellipticFourBoundaryBase)
  exact (C.equivariant A.ellipticFourBoundaryDeckData.fillingRelation
    A.ellipticFourBoundaryBase).symm.trans hendpoint

/-- The order-three endpoint equality is exactly equivalent to the requested deck evaluation. -/
public theorem ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint :
    (letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹) ↔
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
            C.lift A.ellipticThreeBoundaryBase) := by
  let _ := A.ellipticThreeBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let beta := A.ellipticThreeCentralProductConnector
  let C := A.ellipticThreeCentralCoverComparisonOfPath beta
  constructor
  · intro hdeck
    change C.deckMap A.ellipticThreeBoundaryDeckData.fillingRelation =
      orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ at hdeck
    change C.lift
        (A.ellipticThreeBoundaryDeckData.fillingRelation •
          A.ellipticThreeBoundaryBase) = _
    rw [C.equivariant, hdeck]
  · exact A.ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint

/-- The order-four endpoint equality is exactly equivalent to the requested deck evaluation. -/
public theorem ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_iff_endpoint :
    (letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹) ↔
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
            C.lift A.ellipticFourBoundaryBase) := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let beta := A.ellipticFourCentralProductConnector
  let C := A.ellipticFourCentralCoverComparisonOfPath beta
  constructor
  · intro hdeck
    change C.deckMap A.ellipticFourBoundaryDeckData.fillingRelation =
      orderFourFillingRelationClassifiedCentralProductDeck⁻¹ at hdeck
    change C.lift
        (A.ellipticFourBoundaryDeckData.fillingRelation •
          A.ellipticFourBoundaryBase) = _
    rw [C.equivariant, hdeck]
  · exact A.ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint

/-- The two connector-pinned endpoint equalities give the exact remaining elliptic residual. -/
public theorem ellipticRelatorMembership_of_productConnectorLiftEndpoints
    (hThree :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticThreeBoundaryDeckData.fillingRelation •
            A.ellipticThreeBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticThreeBoundaryBase)
    (hFour :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticFourBoundaryDeckData.fillingRelation •
            A.ellipticFourBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticFourBoundaryBase) :
    A.EllipticRelatorMembership A.cuspCentralNaturality :=
  A.ellipticRelatorMembership_of_productConnectorDeckMaps
    (A.ellipticThreeCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint hThree)
    (A.ellipticFourCentralProductCoverComparison_deckMap_fillingRelation_of_endpoint hFour)

/-- The same two endpoint equalities supply the exact nonempty established-input target. -/
public theorem
    actualEllipticRelatorNormalClosureResidual_nonempty_of_productConnectorLiftEndpoints
    (hThree :
      letI := A.ellipticThreeBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticThreeCentralProductConnector
      let C := A.ellipticThreeCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticThreeBoundaryDeckData.fillingRelation •
            A.ellipticThreeBoundaryBase) =
        orderThreeFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticThreeBoundaryBase)
    (hFour :
      letI := A.ellipticFourBoundaryAction
      let D := A.centralAffineUniversalCover
      letI := D.topology
      letI := D.action
      let beta := A.ellipticFourCentralProductConnector
      let C := A.ellipticFourCentralCoverComparisonOfPath beta
      C.lift
          (A.ellipticFourBoundaryDeckData.fillingRelation •
            A.ellipticFourBoundaryBase) =
        orderFourFillingRelationClassifiedCentralProductDeck⁻¹ •
          C.lift A.ellipticFourBoundaryBase) :
    Nonempty
      (EllipticRelatorMembership
        A A.cuspCentralNaturality) :=
  ⟨A.ellipticRelatorMembership_of_productConnectorLiftEndpoints
    hThree hFour⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
