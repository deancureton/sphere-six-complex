module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveCellIncidence
public import SphereSixComplex.Paper.Topology.ConstructedA2PhaseCellIncidence
public import SphereSixComplex.Paper.Topology.ToricCellularCoordinateIncidence

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2TwoCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 4) (j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 1 i j = 0 := by
  fin_cases i
  · exact constructedA2PositiveTwoCell_attachingDegree_zero W T j
  · exact constructedCentralPhaseTwoCell_attachingDegree_zero W T 0 j
  · exact constructedCentralPhaseTwoCell_attachingDegree_zero W T 1 j
  · exact constructedCentralPhaseTwoCell_attachingDegree_zero W T 2 j

public theorem constructedA2TwoCell_coordinateBoundary_single_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 4) (j : Fin 3) :
    standardA2ToricCellularCoordinateBoundary (constructedCentralCellAtlas W).toCWDecomposition
      1 (Pi.single i 1 : Fin 4 → ℤ) j = 0 := by
  let : DecidableEq (cuspWCellIndex (1 + 1)) := inferInstanceAs (DecidableEq (Fin 4))
  exact ((constructedCentralCellAtlas W).coordinateBoundary_single_eq_attachingDegree
    1 i j).trans (constructedA2TwoCell_attachingDegree_zero W _ i j)

end SphereSixComplex.Geometry.InfiniteA2Toric
