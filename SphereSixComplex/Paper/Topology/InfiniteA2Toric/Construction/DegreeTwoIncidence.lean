module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveCellIncidence
public import SphereSixComplex.Paper.Topology.ConstructedA2PhaseCellIncidence
public import SphereSixComplex.Paper.Topology.ToricCellularCoordinateIncidence

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem twoCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 4) (j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 1 i j = 0 := by
  fin_cases i
  · exact positiveTwoCell_attachingDegree_zero W T j
  · exact constructedCentralPhaseTwoCell_attachingDegree_zero W T 0 j
  · exact constructedCentralPhaseTwoCell_attachingDegree_zero W T 1 j
  · exact constructedCentralPhaseTwoCell_attachingDegree_zero W T 2 j

public theorem twoCell_coordinateBoundary_single_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 4) (j : Fin 3) :
    standardA2ToricCellularCoordinateBoundary (constructedCentralCellAtlas W).toCWDecomposition
      1 (Pi.single i 1 : Fin 4 → ℤ) j = 0 := by
  let : DecidableEq (CuspWCellIndex (1 + 1)) := inferInstanceAs (DecidableEq (Fin 4))
  exact ((constructedCentralCellAtlas W).coordinateBoundary_single_eq_attachingDegree
    1 i j).trans (twoCell_attachingDegree_zero W _ i j)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
