module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticCentralConnectorCoherence
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourCommonGaugeGeometry
public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorNormalClosureTypes
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourRelatorComparison

/-!
# Connector coherence for the actual order-four elliptic chart

The order-four overlap marking and the constructed cusp marking differ by one common inner
conjugation after transport to the actual core.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open SphereSixComplex.LatticeData

variable (A : AnalyticData)

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






end SphereSixComplex.Geometry.AnalyticData

end

end
