module
public import SphereSixComplex.Paper.Topology.AffinePeripheralAbelianization
public import SphereSixComplex.Paper.Topology.PaperEllipticActualStraightPeriod

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology SphereSixComplex.LatticeData
open PaperVanKampenFourPieceCover
variable (A : AnalyticData)

public theorem actualCore_subset_ellipticInterior :
    A.actualVanKampenFourPieceCover.core ⊆
      A.starCover.stage (2 : Fin 4) := by
  intro x hx
  rw [A.ellipticInterior_eq_threePieceUnion]
  exact Or.inl (Or.inl hx)

public def actualCoreToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.core, A.ellipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.actualCore_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualThreeToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.ellipticThree, A.ellipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.orderThreePiece_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualFourToEllipticInterior :
    C(A.actualVanKampenFourPieceCover.ellipticFour, A.ellipticInterior) :=
  ⟨fun x ↦ ⟨x.1, A.orderFourPiece_subset_ellipticInterior x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

public def actualCoreToEllipticInteriorPiOne :=
  FundamentalGroup.map A.actualCoreToEllipticInterior
    ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩

public theorem actualThreeRelator_ellipticInterior_killed :
    A.actualCoreToEllipticInteriorPiOne
      (A.ellipticThreeOverlapToCore
        A.ellipticThreeCanonicalRelator) = 1 := by
  let D := A.actualVanKampenFourPieceCover
  let c := D.connectorInCore D.ellipticThreeConnector
    D.ellipticThreeConnector_mem D.ellipticThreePoint_mem.1
  change FundamentalGroup.map A.actualCoreToEllipticInterior _
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)
      (FundamentalGroup.map (D.overlapToCore D.ellipticThree) _
        A.ellipticThreeCanonicalRelator)) = 1
  erw [CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath _).map_eq_one_iff.mpr
  erw [CoveringSpace.map_map]
  change FundamentalGroup.map
    (A.actualThreeToEllipticInterior.comp D.ellipticThreeOverlapToPiece) _
      A.ellipticThreeCanonicalRelator = 1
  erw [← CoveringSpace.map_map]
  change FundamentalGroup.map A.actualThreeToEllipticInterior _
    (D.ellipticThreeOverlapFundamentalGroupMap
      A.ellipticThreeCanonicalRelator) = 1
  rw [A.ellipticThreeCanonicalRelator_killed, map_one]

public theorem actualFourRelator_ellipticInterior_killed :
    A.actualCoreToEllipticInteriorPiOne
      (A.ellipticFourOverlapToCore
        A.ellipticFourCanonicalRelator) = 1 := by
  let D := A.actualVanKampenFourPieceCover
  let c := D.connectorInCore D.ellipticFourConnector
    D.ellipticFourConnector_mem D.ellipticFourPoint_mem.1
  change FundamentalGroup.map A.actualCoreToEllipticInterior _
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath c.symm)
      (FundamentalGroup.map (D.overlapToCore D.ellipticFour) _
        A.ellipticFourCanonicalRelator)) = 1
  erw [CoveringSpace.map_fundamentalGroupMulEquivOfPath]
  apply (FundamentalGroup.fundamentalGroupMulEquivOfPath _).map_eq_one_iff.mpr
  erw [CoveringSpace.map_map]
  change FundamentalGroup.map
    (A.actualFourToEllipticInterior.comp D.ellipticFourOverlapToPiece) _
      A.ellipticFourCanonicalRelator = 1
  erw [← CoveringSpace.map_map]
  change FundamentalGroup.map A.actualFourToEllipticInterior _
    (D.ellipticFourOverlapFundamentalGroupMap
      A.ellipticFourCanonicalRelator) = 1
  rw [A.ellipticFourCanonicalRelator_killed, map_one]

end SphereSixComplex.Geometry.AnalyticData
end
