module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepCells
public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas
public import SphereSixComplex.Paper.Topology.ToricCellAtlasRechart

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction
open CuspFilling CuspPeriodExpansion
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepCellMap (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (n : ℕ) → CentralFiber.Cell n → PartialEquiv (Fin n → ℝ) (ActualLocalCuspCentralOrbitQuotient W)
  | 0 => constructedCentralCellMap W 0
  | 1 => constructedCentralCellMap W 1
  | 2 => ![correctedPositiveTwoCell W, phaseSweepCell W 0,
      phaseSweepCell W 1, phaseSweepCell W 2]
  | n + 3 => constructedCentralCellMap W (n + 3)

public theorem phaseSweepCellMap_source (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (i : CentralFiber.Cell n) : (phaseSweepCellMap W n i).source = Metric.ball 0 1 := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_source_eq W 0 i
  · exact constructedCentralCellMap_source_eq W 1 i
  · change Fin 4 at i
    fin_cases i
    · exact correctedPositiveTwoCell_source_eq W
    all_goals rfl
  · exact constructedCentralCellMap_source_eq W (n + 3) i

public theorem phaseSweepCellMap_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : CentralFiber.Cell n) :
    ContinuousOn (phaseSweepCellMap W n i) (Metric.closedBall 0 1) := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_continuousOn W 0 i
  · exact constructedCentralCellMap_continuousOn W 1 i
  · change Fin 4 at i
    fin_cases i
    · exact continuousOn_correctedPositiveTwoCell W
    · exact (phaseSweepOrbit_continuous W 0).continuousOn
    · exact (phaseSweepOrbit_continuous W 1).continuousOn
    · exact (phaseSweepOrbit_continuous W 2).continuousOn
  · exact constructedCentralCellMap_continuousOn W (n + 3) i

public theorem phaseSweepCellMap_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : CentralFiber.Cell n) :
    ContinuousOn (phaseSweepCellMap W n i).symm (phaseSweepCellMap W n i).target := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_continuousOn_symm W 0 i
  · exact constructedCentralCellMap_continuousOn_symm W 1 i
  · change Fin 4 at i
    fin_cases i
    · exact continuousOn_correctedPositiveTwoCell_symm W
    · exact phaseSweepCell_continuousOn_symm W 0
    · exact phaseSweepCell_continuousOn_symm W 1
    · exact phaseSweepCell_continuousOn_symm W 2
  · exact constructedCentralCellMap_continuousOn_symm W (n + 3) i

public theorem phaseSweepCellMap_openImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : CentralFiber.Cell n) :
    phaseSweepCellMap W n i '' Metric.ball 0 1 =
      constructedCentralCellMap W n i '' Metric.ball 0 1 := by
  rcases n with (_ | _ | _ | n)
  · rfl
  · rfl
  · change Fin 4 at i
    fin_cases i
    · rfl
    · exact phaseSweepOrbit_image W 0
    · exact phaseSweepOrbit_image W 1
    · exact phaseSweepOrbit_image W 2
  · rfl

public theorem phaseSweepCellMap_closedImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : CentralFiber.Cell n) :
    phaseSweepCellMap W n i '' Metric.closedBall 0 1 =
      constructedCentralCellMap W n i '' Metric.closedBall 0 1 := by
  rcases n with (_ | _ | _ | n)
  · rfl
  · rfl
  · change Fin 4 at i
    fin_cases i
    · rfl
    · exact phaseSweepOrbit_closedImage W 0
    · exact phaseSweepOrbit_closedImage W 1
    · exact phaseSweepOrbit_closedImage W 2
  · rfl

public theorem phaseSweepCellMap_boundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : CentralFiber.Cell n) :
    MapsTo (phaseSweepCellMap W n i) (Metric.sphere 0 1) (constructedCentralCellSkeleton W n) := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_mapsTo W 0 i
  · exact constructedCentralCellMap_mapsTo W 1 i
  · apply Set.MapsTo.mono_right _ (constructedCentralOneSkeleton_subset_cellSkeleton W (by decide))
    change Fin 4 at i
    fin_cases i
    · exact correctedPositiveTwoCell_mapsTo_oneSkeleton W
    · exact phaseSweepOrbit_boundary_oneSkeleton W 0
    · exact phaseSweepOrbit_boundary_oneSkeleton W 1
    · exact phaseSweepOrbit_boundary_oneSkeleton W 2
  · exact constructedCentralCellMap_mapsTo W (n + 3) i

public def phaseSweepCellAtlas (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    CentralFiber.CellAtlas (ActualLocalCuspCentralOrbitQuotient W) :=
  (constructedCentralCellAtlas W).rechart (phaseSweepCellMap W)
    (phaseSweepCellMap_source W) (phaseSweepCellMap_continuousOn W)
    (phaseSweepCellMap_continuousOn_symm W) (phaseSweepCellMap_openImage W)
    (phaseSweepCellMap_closedImage W) (phaseSweepCellMap_boundary W)

end SphereSixComplex.Geometry.CuspCollar
