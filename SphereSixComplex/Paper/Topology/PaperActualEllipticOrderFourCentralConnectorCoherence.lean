module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralConnectorCoherence
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourCommonGaugeGeometry
public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorCommonGaugeReduction

/-!
# Connector coherence for the actual order-four elliptic chart

The order-four overlap marking and the constructed cusp marking differ by one common inner
conjugation after transport to the actual core.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open SphereSixComplex.LatticeData

variable (A : PaperAnalyticData)

public theorem ellipticFourCentralBase_eq_overlapCentralBase :
    A.ellipticFourCentralBase = A.ellipticFourOverlapCentralBase := by
  exact congrArg A.ellipticFourOverlapToCentral
    A.ellipticFourBoundaryProjection_base

public theorem cuspCentralToCorePair_simultaneouslyConjugate_orderFour
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    let source := A.orderFourCentralBaseWhisker.cast rfl
      A.ellipticFourCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.cuspCentralToCoreEquiv a, A.cuspCentralToCoreEquiv b)
      (A.ellipticFourCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a),
        A.ellipticFourCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)) := by
  let H := A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
  let f : C(A.CentralFamily, A.actualVanKampenFourPieceCover.core) := ⟨H, H.continuous⟩
  let cuspConnector :=
    (A.actualVanKampenFourPieceCover.connectorInCore
      A.actualVanKampenFourPieceCover.cuspConnector
      A.actualVanKampenFourPieceCover.cuspConnector_mem
      A.actualVanKampenFourPieceCover.cuspPoint_mem.1).symm
  let fourConnector :=
    (A.actualVanKampenFourPieceCover.connectorInCore
      A.actualVanKampenFourPieceCover.ellipticFourConnector
      A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1).symm
  let source := A.orderFourCentralBaseWhisker.cast rfl
    A.ellipticFourCentralBase_eq_overlapCentralBase.symm
  have hcusp : H A.centralAffineBase =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.cusp A.cuspOverlapBase := by
    rw [A.centralAffineBase_eq_cuspCentralBase]
    exact A.centralToSectionSevenEulerPieceHomeomorph_cuspOverlapToCentral
      A.cuspOverlapBase
  have hfour : H A.ellipticFourOverlapCentralBase =
      A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticFour
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
    A.centralToSectionSevenEulerPiece_ellipticFourOverlapToCentral _
  let p := cuspConnector.cast hcusp rfl
  let q := fourConnector.cast hfour rfl
  have h := fundamentalGroupMappedPair_simultaneouslyConjugate_of_sourcePath
    f source p q a b
  have hcuspA := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hcusp cuspConnector a
  have hcuspB := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hcusp cuspConnector b
  have hfourA := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hfour fourConnector
      (FundamentalGroup.fundamentalGroupMulEquivOfPath source a)
  have hfourB := fundamentalGroupMulEquivOfPath_mapOfEq_eq_cast
    f hfour fourConnector
      (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)
  change SimultaneouslyConjugate
    (A.cuspCentralToCoreEquiv a, A.cuspCentralToCoreEquiv b) _
  change SimultaneouslyConjugate
    (FundamentalGroup.fundamentalGroupMulEquivOfPath cuspConnector
        (FundamentalGroup.mapOfEq f hcusp a),
      FundamentalGroup.fundamentalGroupMulEquivOfPath cuspConnector
        (FundamentalGroup.mapOfEq f hcusp b))
    (FundamentalGroup.fundamentalGroupMulEquivOfPath fourConnector
        (FundamentalGroup.mapOfEq f hfour
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a)),
      FundamentalGroup.fundamentalGroupMulEquivOfPath fourConnector
        (FundamentalGroup.mapOfEq f hfour
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)))
  convert h using 1
  · exact Prod.ext hcuspA hcuspB
  · exact Prod.ext hfourA hfourB

public theorem cuspCentralNaturalityPair_simultaneouslyConjugate_orderFour
    (a b : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    let source := A.orderFourCentralBaseWhisker.cast rfl
      A.ellipticFourCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.cuspCentralNaturality.centralToCore a,
        A.cuspCentralNaturality.centralToCore b)
      (A.ellipticFourCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source a),
        A.ellipticFourCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source b)) := by
  exact (A.cuspCentralNaturalityPair_simultaneouslyConjugate_actualCusp a b).trans
    (A.cuspCentralToCorePair_simultaneouslyConjugate_orderFour a b)

public theorem orderFourCentralMeridianAtOverlap_eq_pathTransport :
    A.orderFourCentralMeridianAtOverlap =
      FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderFourCentralBaseWhisker
        A.centralAffineCorePiOneData.rhoTwo := by
  unfold orderFourCentralMeridianAtOverlap
  rfl

public theorem orderFourCentralTranslationAtOverlap_eq_pathTransport :
    A.orderFourCentralTranslationAtOverlap =
      FundamentalGroup.fundamentalGroupMulEquivOfPath A.orderFourCentralBaseWhisker
        (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon')) := by
  unfold orderFourCentralTranslationAtOverlap
  rfl

public theorem OrderFourCentralMarkedLoopCompatibility.toActualCorePair
    (H : A.OrderFourCentralMarkedLoopCompatibility) :
    let source := A.orderFourCentralBaseWhisker.cast rfl
      A.ellipticFourCentralBase_eq_overlapCentralBase.symm
    SimultaneouslyConjugate
      (A.ellipticFourCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source
            A.centralAffineCorePiOneData.rhoTwo),
        A.ellipticFourCentralToCoreEquiv
          (FundamentalGroup.fundamentalGroupMulEquivOfPath source
            (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))))
      (A.ellipticFourPhysicalMeridianToCore,
        Additive.toMul (A.ellipticFourPhysicalTranslationToCore epsilon')) := by
  let _ := A.ellipticFourBoundaryAction
  let D := A.centralAffineUniversalCover
  let _ := D.topology
  let _ := D.action
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × SphereSixComplex.Geometry.ComplexTorus.ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let C := A.ellipticFourCentralCoverComparison
  dsimp only [OrderFourCentralMarkedLoopCompatibility] at H
  let hbase := C.commutes A.ellipticFourBoundaryBase
  let hoverlap := A.ellipticFourCentralBase_eq_overlapCentralBase
  have hpoint : D.data.projection (C.lift A.ellipticFourBoundaryBase) =
      A.ellipticFourOverlapCentralBase := by
    calc
      _ = C.baseMap
          (A.ellipticFourBoundaryProjection
            A.ellipticFourBoundaryBase) :=
        (C.commutes A.ellipticFourBoundaryBase).symm
      _ = A.ellipticFourCentralBase := rfl
      _ = A.ellipticFourOverlapCentralBase :=
        A.ellipticFourCentralBase_eq_overlapCentralBase
  let E := fundamentalGroupMulEquivOfEq hpoint
  let source := A.orderFourCentralBaseWhisker.cast rfl hoverlap.symm
  have hcomp : hbase.trans hpoint = hoverlap := Subsingleton.elim _ _
  have hleftAny (a : FundamentalGroup A.CentralFamily A.centralAffineBase) :
      E (fundamentalGroupElementOfBaseEq hbase
          (FundamentalGroup.fundamentalGroupMulEquivOfPath
            A.orderFourCentralBaseWhisker a)) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath source a := by
    have ht := fundamentalGroupMulEquivOfEq_elementOfBaseEq_trans hbase hpoint
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderFourCentralBaseWhisker a)
    rw [hcomp] at ht
    exact ht.trans
      (fundamentalGroupMulEquivOfPath_cast_right A.orderFourCentralBaseWhisker
        hoverlap.symm a).symm
  rw [A.orderFourCentralMeridianAtOverlap_eq_pathTransport,
    A.orderFourCentralTranslationAtOverlap_eq_pathTransport] at H
  let meridianLoop :=
    ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
      A.ellipticFourBoundaryBase
      A.ellipticFourBoundaryDeckData.meridian
  let translationLoop :=
    ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
      A.ellipticFourBoundaryBase
      (Additive.toMul
        (A.ellipticFourBoundaryDeckData.translation epsilon'))
  let boundaryEq := A.ellipticFourCanonicalChosenCover_boundaryBase_eq
  have htransportRightMeridian :
      E (FundamentalGroup.mapOfEq C.baseMap hbase meridianLoop) =
        FundamentalGroup.mapOfEq C.baseMap hoverlap meridianLoop := by
    have ht := fundamentalGroupMulEquivOfEq_mapOfEq_trans C.baseMap hbase hpoint
      meridianLoop
    rw [hcomp] at ht
    exact ht
  have hrightMeridian :
      E (FundamentalGroup.mapOfEq C.baseMap hbase meridianLoop) =
        FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq boundaryEq meridianLoop) := by
    rw [htransportRightMeridian]
    symm
    exact mapOfEq_fundamentalGroupElementOfBaseEq boundaryEq
      A.ellipticFourOverlapToCentral hoverlap rfl meridianLoop
  have htransportRightTranslation :
      E (FundamentalGroup.mapOfEq C.baseMap hbase translationLoop) =
        FundamentalGroup.mapOfEq C.baseMap hoverlap translationLoop := by
    have ht := fundamentalGroupMulEquivOfEq_mapOfEq_trans C.baseMap hbase hpoint
      translationLoop
    rw [hcomp] at ht
    exact ht
  have hrightTranslation :
      E (FundamentalGroup.mapOfEq C.baseMap hbase translationLoop) =
        FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl
          (fundamentalGroupElementOfBaseEq boundaryEq translationLoop) := by
    rw [htransportRightTranslation]
    symm
    exact mapOfEq_fundamentalGroupElementOfBaseEq boundaryEq
      A.ellipticFourOverlapToCentral hoverlap rfl translationLoop
  have hcoreMeridian :
      A.ellipticFourCentralToCoreEquiv
          (E (FundamentalGroup.mapOfEq C.baseMap hbase meridianLoop)) =
        A.ellipticFourPhysicalMeridianToCore := by
    rw [hrightMeridian, ← A.ellipticFourOverlapToCore_eq_central]
    rfl
  have hcoreTranslation :
      A.ellipticFourCentralToCoreEquiv
          (E (FundamentalGroup.mapOfEq C.baseMap hbase translationLoop)) =
        Additive.toMul
          (A.ellipticFourPhysicalTranslationToCore epsilon') := by
    rw [hrightTranslation, ← A.ellipticFourOverlapToCore_eq_central]
    rfl
  have h := H.map (E.trans A.ellipticFourCentralToCoreEquiv).toMonoidHom
  convert h using 1
  · exact Prod.ext
      (congrArg A.ellipticFourCentralToCoreEquiv
        (hleftAny A.centralAffineCorePiOneData.rhoTwo)).symm
      (congrArg A.ellipticFourCentralToCoreEquiv
        (hleftAny (Additive.toMul
          (A.centralAffineCorePiOneData.translation epsilon')))).symm
  · exact Prod.ext hcoreMeridian.symm hcoreTranslation.symm

public theorem OrderFourCentralMarkedLoopCompatibility.toActualCommonGaugeComparison
    (H : A.OrderFourCentralMarkedLoopCompatibility) :
    A.OrderFourCommonGaugeComparison A.cuspCentralNaturality := by
  have hcentral :=
    A.cuspCentralNaturalityPair_simultaneouslyConjugate_orderFour
      A.centralAffineCorePiOneData.rhoTwo
      (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))
  have hphysical := H.toActualCorePair A
  exact hcentral.trans hphysical

public theorem ellipticRelatorMembership_of_markedLoopCompatibilities
    (H3 : A.OrderThreeCentralMarkedLoopCompatibility)
    (H4 : A.OrderFourCentralMarkedLoopCompatibility) :
    A.EllipticRelatorMembership A.cuspCentralNaturality :=
  A.ellipticRelatorMembership_of_commonGaugeComparisons
    (H3.toActualCommonGaugeComparison A)
    (H4.toActualCommonGaugeComparison A)

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
