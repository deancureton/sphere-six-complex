module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepCells
public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas
public import SphereSixComplex.Paper.Topology.ToricCellAtlasRechart

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricModel.Established
open StandardInfiniteA2ToricModel.Construction
open CuspFilling CuspPeriodExpansion
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def phaseSweepCellMap (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (n : ℕ) → cuspWCellIndex n → PartialEquiv (Fin n → ℝ) (ActualLocalCuspCentralOrbitQuotient W)
  | 0 => constructedCentralCellMap W 0
  | 1 => constructedCentralCellMap W 1
  | 2 => ![constructedA2CorrectedPositiveTwoCell W, phaseSweepCell W 0,
      phaseSweepCell W 1, phaseSweepCell W 2]
  | n + 3 => constructedCentralCellMap W (n + 3)

public theorem phaseSweepCellMap_source (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (i : cuspWCellIndex n) : (phaseSweepCellMap W n i).source = Metric.ball 0 1 := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_source_eq W 0 i
  · exact constructedCentralCellMap_source_eq W 1 i
  · change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_source_eq W
    all_goals rfl
  · exact constructedCentralCellMap_source_eq W (n + 3) i

public theorem phaseSweepCellMap_continuousOn
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : cuspWCellIndex n) :
    ContinuousOn (phaseSweepCellMap W n i) (Metric.closedBall 0 1) := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_continuousOn W 0 i
  · exact constructedCentralCellMap_continuousOn W 1 i
  · change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_continuousOn W
    · exact (phaseSweepOrbit_continuous W 0).continuousOn
    · exact (phaseSweepOrbit_continuous W 1).continuousOn
    · exact (phaseSweepOrbit_continuous W 2).continuousOn
  · exact constructedCentralCellMap_continuousOn W (n + 3) i

public theorem phaseSweepCellMap_continuousOn_symm
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : cuspWCellIndex n) :
    ContinuousOn (phaseSweepCellMap W n i).symm (phaseSweepCellMap W n i).target := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_continuousOn_symm W 0 i
  · exact constructedCentralCellMap_continuousOn_symm W 1 i
  · change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_continuousOn_symm W
    · exact phaseSweepCell_continuousOn_symm W 0
    · exact phaseSweepCell_continuousOn_symm W 1
    · exact phaseSweepCell_continuousOn_symm W 2
  · exact constructedCentralCellMap_continuousOn_symm W (n + 3) i

public theorem phaseSweepCellMap_openImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : cuspWCellIndex n) :
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
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : cuspWCellIndex n) :
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
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (n : ℕ) (i : cuspWCellIndex n) :
    MapsTo (phaseSweepCellMap W n i) (Metric.sphere 0 1) (constructedCentralCellSkeleton W n) := by
  rcases n with (_ | _ | _ | n)
  · exact constructedCentralCellMap_mapsTo W 0 i
  · exact constructedCentralCellMap_mapsTo W 1 i
  · apply Set.MapsTo.mono_right _ (constructedCentralOneSkeleton_subset_cellSkeleton W (by decide))
    change Fin 4 at i
    fin_cases i
    · exact constructedA2CorrectedPositiveTwoCell_mapsTo_oneSkeleton W
    · exact phaseSweepOrbit_boundary_oneSkeleton W 0
    · exact phaseSweepOrbit_boundary_oneSkeleton W 1
    · exact phaseSweepOrbit_boundary_oneSkeleton W 2
  · exact constructedCentralCellMap_mapsTo W (n + 3) i

public def phaseSweepCellAtlas (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    StandardA2ToricCentralFiberCellAtlas (ActualLocalCuspCentralOrbitQuotient W) :=
  (constructedCentralCellAtlas W).rechart (phaseSweepCellMap W)
    (phaseSweepCellMap_source W) (phaseSweepCellMap_continuousOn W)
    (phaseSweepCellMap_continuousOn_symm W) (phaseSweepCellMap_openImage W)
    (phaseSweepCellMap_closedImage W) (phaseSweepCellMap_boundary W)

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
