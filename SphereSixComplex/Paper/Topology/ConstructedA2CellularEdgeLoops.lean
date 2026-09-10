module

public import SphereSixComplex.Prerequisites.Topology.CellularLoopComparison
public import SphereSixComplex.Paper.Topology.ConstructedA2EdgeIncidence

@[expose] public section
noncomputable section
open CategoryTheory
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex StandardCircleHomologyLiftDegree
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCentralCellAtlas_edges_same_left
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 j).boundaryMap
        cwBoundaryOneLeft =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 k).boundaryMap
        cwBoundaryOneLeft := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact Subtype.ext ((constructedCentralCellAtlas_edge_left W j).trans
    (constructedCentralCellAtlas_edge_left W k).symm)

public theorem constructedCentralCellAtlas_edges_same_right
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 j).boundaryMap
        cwBoundaryOneRight =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 k).boundaryMap
        cwBoundaryOneRight := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact Subtype.ext ((constructedCentralCellAtlas_edge_right W j).trans
    (constructedCentralCellAtlas_edge_right W k).symm)

public def constructedCentralCellularEdgePath
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    Path (cwCellularEdgePath (ActualLocalCuspCentralOrbitQuotient W) (0 : Fin 3) 0)
      (cwCellularEdgePath (ActualLocalCuspCentralOrbitQuotient W) (0 : Fin 3) 1) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  let X := ActualLocalCuspCentralOrbitQuotient W
  exact ⟨⟨fun t ↦ cwCellularEdgePath X j ⟨t⟩,
    (cwCellularEdgePath X j).hom.continuous.comp continuous_uliftUp⟩,
    (cwCellularEdgePath_left X j).trans
      ((congrArg (integralCWSkeletonInclusion X 1)
        (constructedCentralCellAtlas_edges_same_left W j 0)).trans
        (cwCellularEdgePath_left X (0 : Fin 3)).symm),
    (cwCellularEdgePath_right X j).trans
      ((congrArg (integralCWSkeletonInclusion X 1)
        (constructedCentralCellAtlas_edges_same_right W j 0)).trans
        (cwCellularEdgePath_right X (0 : Fin 3)).symm)⟩

public theorem constructedCentralCellularEdgeLoop_relative_class
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (j k : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1).symm
      ((HomologicalComplex.homologyMap (cwRelativeIntegralSingularChainProjection
        (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1)) 1).hom
        (loopHomologyClass ((constructedCentralCellularEdgePath W j).trans
          (constructedCentralCellularEdgePath W k).symm))) =
      Finsupp.single j 1 - Finsupp.single k 1 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact normalized_cellBasis_loop_edges T (ActualLocalCuspCentralOrbitQuotient W) j k
    (constructedCentralCellAtlas_edges_same_left W j k)
    (constructedCentralCellAtlas_edges_same_right W j k)
    (constructedCentralCellularEdgePath W j) (constructedCentralCellularEdgePath W k) rfl rfl

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
