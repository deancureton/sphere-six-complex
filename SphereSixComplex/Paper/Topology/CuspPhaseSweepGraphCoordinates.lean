module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepAbsoluteComparison
public import SphereSixComplex.Paper.Topology.ConstructedA2CellularEdgeLoops

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open CategoryTheory HomologicalComplex
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex SphereSixComplex.Periods StandardCircleHomologyLiftDegree
open CuspPeriodExpansion InfiniteA2Toric
open InfiniteA2Toric InfiniteA2Toric.Construction
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem phaseSweepCellAtlas_edges_same_left
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 j).boundaryMap
        cwBoundaryOneLeft =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 k).boundaryMap
        cwBoundaryOneLeft := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  apply Subtype.ext
  exact (constructedCentralCellAtlas_edge_left W j).trans
    (constructedCentralCellAtlas_edge_left W k).symm

public theorem phaseSweepCellAtlas_edges_same_right
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 j).boundaryMap
        cwBoundaryOneRight =
      (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W) 1 k).boundaryMap
        cwBoundaryOneRight := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  apply Subtype.ext
  exact (constructedCentralCellAtlas_edge_right W j).trans
    (constructedCentralCellAtlas_edge_right W k).symm

public def phaseSweepCellularEdgePath
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    Path (cwCellularEdgePath (ActualLocalCuspCentralOrbitQuotient W) (0 : Fin 3) 0)
      (cwCellularEdgePath (ActualLocalCuspCentralOrbitQuotient W) (0 : Fin 3) 1) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  let X := ActualLocalCuspCentralOrbitQuotient W
  exact ⟨⟨fun t ↦ cwCellularEdgePath X j ⟨t⟩,
    (cwCellularEdgePath X j).hom.continuous.comp continuous_uliftUp⟩,
    (cwCellularEdgePath_left X j).trans
      ((congrArg (integralCWSkeletonInclusion X 1)
        (phaseSweepCellAtlas_edges_same_left W j 0)).trans
        (cwCellularEdgePath_left X (0 : Fin 3)).symm),
    (cwCellularEdgePath_right X j).trans
      ((congrArg (integralCWSkeletonInclusion X 1)
        (phaseSweepCellAtlas_edges_same_right W j 0)).trans
        (cwCellularEdgePath_right X (0 : Fin 3)).symm)⟩

public theorem phaseSweepCellularEdgeLoop_relative_class
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (j k : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1).symm
      ((homologyMap (cwRelativeIntegralSingularChainProjection
        (integralCWSkeletonInclusion (ActualLocalCuspCentralOrbitQuotient W) 1)) 1).hom
        (loopHomologyClass ((phaseSweepCellularEdgePath W j).trans
          (phaseSweepCellularEdgePath W k).symm))) =
      Finsupp.single j 1 - Finsupp.single k 1 := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  exact normalized_cellBasis_loop_edges T (ActualLocalCuspCentralOrbitQuotient W) j k
    (phaseSweepCellAtlas_edges_same_left W j k)
    (phaseSweepCellAtlas_edges_same_right W j k)
    (phaseSweepCellularEdgePath W j) (phaseSweepCellularEdgePath W k) rfl rfl

public theorem phaseSweepCellularEdgePath_central
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j : Fin 3) (t : unitInterval) :
    (phaseSweepCellularEdgePath W j t).1 = (constructedCentralCellularEdgePath W j t).1 := by
  change phaseSweepCellMap W 1 j (fun _ ↦ 2 * (t : ℝ) - 1) =
    constructedCentralCellMap W 1 j (fun _ ↦ 2 * (t : ℝ) - 1)
  rfl

private theorem loopHomologyClass_eq_of_pointwise
    {X : Type} [TopologicalSpace X] {a b : X} (p : Path a a) (q : Path b b)
    (h : ∀ t, p t = q t) : loopHomologyClass p = loopHomologyClass q := by
  have hab : a = b := by simpa using h 0
  subst b
  congr 1
  ext t
  exact h t

public theorem phaseSweepCellularEdgeLoop_central_homology
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    loopHomologyClass (((phaseSweepCellularEdgePath W j).trans
      (phaseSweepCellularEdgePath W k).symm).map continuous_subtype_val) =
    loopHomologyClass (((constructedCentralCellularEdgePath W j).trans
      (constructedCentralCellularEdgePath W k).symm).map continuous_subtype_val) := by
  apply loopHomologyClass_eq_of_pointwise
  intro t
  change (((phaseSweepCellularEdgePath W j).trans
    (phaseSweepCellularEdgePath W k).symm) t).1 =
    (((constructedCentralCellularEdgePath W j).trans
      (constructedCentralCellularEdgePath W k).symm) t).1
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact phaseSweepCellularEdgePath_central W j _
  · exact phaseSweepCellularEdgePath_central W k _


public theorem phaseSweepCellularEdgeLoop_homologyToCentral
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    homologyMap (cwIntegralSingularChainMapObj
      (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1
        (loopHomologyClass ((phaseSweepCellularEdgePath W j).trans
          (phaseSweepCellularEdgePath W k).symm)) =
    loopHomologyClass (((constructedCentralCellularEdgePath W j).trans
      (constructedCentralCellularEdgePath W k).symm).map continuous_subtype_val) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  change integralSingularHomologyMap 1
    (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2).hom _ = _
  rw [integralSingularHomologyMap_loopHomologyClass]
  exact phaseSweepCellularEdgeLoop_central_homology W j k

public theorem phaseSweepGraphPrism_relativeCoordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 2) (j k : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    phaseSweepHomologyTwoToRelativeEquiv W T
      (topologicalClosedPrismHomology (circleSweepHomotopy W i) 0
        (homologyMap (cwIntegralSingularChainMapObj
          (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1
          (loopHomologyClass ((phaseSweepCellularEdgePath W j).trans
            (phaseSweepCellularEdgePath W k).symm)))) =
      closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0
        (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1
          (Finsupp.single j 1 - Finsupp.single k 1)) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  have h := phaseSweepCentralPrism_relativeCoordinates W T i
    (loopHomologyClass ((phaseSweepCellularEdgePath W j).trans
      (phaseSweepCellularEdgePath W k).symm))
  have he := phaseSweepCellularEdgeLoop_relative_class W T j k
  have he' := congrArg (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1) he
  rw [AddEquiv.apply_symm_apply] at he'
  exact h.trans (congrArg (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0) he')

public theorem phaseSweepGraphPrism_cellCoordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (i : Fin 2) (j k : Fin 3) :
    let _ := (phaseSweepCellAtlas W).cwComplex
    phaseSweepHomologyTwoCellEquiv W T
      (topologicalClosedPrismHomology (circleSweepHomotopy W i) 0
        (homologyMap (cwIntegralSingularChainMapObj
          (integralCWSkeletonToSpace (ActualLocalCuspCentralOrbitQuotient W) 2)) 1
          (loopHomologyClass ((phaseSweepCellularEdgePath W j).trans
            (phaseSweepCellularEdgePath W k).symm)))) =
      (fun l : Fin 4 ↦ ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm
          (closedPrismHomology (phaseSweepSkeletalRelativeHomotopy W i) 0
            (T.normalized.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 1
              (Finsupp.single j 1 - Finsupp.single k 1)))) l) := by
  let _ := (phaseSweepCellAtlas W).cwComplex
  dsimp only
  funext l
  exact congrArg (fun x ↦
    ((T.cellBasis (ActualLocalCuspCentralOrbitQuotient W) 2).symm x) l)
    (phaseSweepGraphPrism_relativeCoordinates W T i j k)

end SphereSixComplex.Geometry.CuspCollar
