module

public import SphereSixComplex.Paper.Topology.SquareRadialCircleComparison

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

namespace Construction

public theorem positiveCell_boundary_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : CWCharacteristicBoundarySphere 2) :
    constructedCentralCellMap W 2 (0 : Fin 4) x.1 =
      correctedPlaneCellOrbit W
        ⟨correctedHexagonHomeomorph 0 x.1,
          (correctedHexagonHomeomorph_mem_closed_iff 0 x.1).mpr
            (Metric.sphere_subset_closedBall x.2)⟩ := by
  change correctedPositiveTwoOrbit W x.1 = _
  rw [correctedPositiveTwoOrbit_closedBall W
    ⟨x.1, Metric.sphere_subset_closedBall x.2⟩]
  rfl

public theorem positiveCell_boundary_side
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    constructedCentralCellMap W 2 (0 : Fin 4)
      (squareBoundaryHexagonHomeomorph.symm
        (hexagonBoundarySidePath i t)).1 =
      actualHexagonSidePath W i t := by
  rw [positiveCell_boundary_formula]
  change correctedPlaneCellOrbit W _ =
    correctedPlaneCellOrbit W (hexagonSide i t)
  apply congrArg (correctedPlaneCellOrbit W)
  apply Subtype.ext
  exact congrArg (fun z : HexagonBoundary ↦ z.1) (squareBoundaryHexagonHomeomorph.apply_symm_apply
    (hexagonBoundarySidePath i t))

public def positiveCellBoundaryMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    ContinuousMap (CWCharacteristicBoundarySphere 2)
      (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W)
    2 (0 : Fin 4)).boundaryMap.hom

public theorem positiveCell_positiveLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    loopHomologyClass (cwSquareBoundaryPositiveLoop.map
      (positiveCellBoundaryMap W).continuous) = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  let f : ContinuousMap HexagonBoundary
      (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) :=
    (positiveCellBoundaryMap W).comp
      ⟨squareBoundaryHexagonHomeomorph.symm,
        squareBoundaryHexagonHomeomorph.symm.continuous⟩
  let g : ContinuousMap (constructedCentralOneSkeleton W)
      (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) :=
    ⟨oneSkeletonCWHomeomorph W, (oneSkeletonCWHomeomorph W).continuous⟩
  have hi (i : Fin 6) (t : unitInterval) :
      f (hexagonBoundarySidePath i t) =
        g (oneSkeletonHexagonSidePath W i t) := by
    apply Subtype.ext
    exact positiveCell_boundary_side W i t
  have hl (t : unitInterval) : f (hexagonBoundaryLoop t) =
      g (oneSkeletonHexagonLoop W t) := by
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 5) t
    intro u
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 4) u
    intro v
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 3) v
    intro w
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 2) w
    exact path_trans_pointwise f g _ _ _ _ (hi 0) (hi 1)
  have hb : f (hexagonBoundaryVertex 0) =
      g (oneSkeletonOrigin W false) := by
    exact (congrArg f (hexagonBoundarySidePath 0).source).symm.trans
      ((hi 0 0).trans (congrArg g (oneSkeletonHexagonSidePath W 0).source))
  have hp : hexagonBoundaryLoop.map f.continuous =
      ((oneSkeletonHexagonLoop W).map g.continuous).cast hb hb := by
    apply Path.ext
    funext t
    exact hl t
  have hz : loopHomologyClass (hexagonBoundaryLoop.map f.continuous) = 0 := by
    rw [hp, loopHomologyClass_cast]
    exact cellularHexagonLoop_homology_zero W
  have h := congrArg (integralSingularHomologyMap 1 (positiveCellBoundaryMap W))
    hexagonBoundaryLoop_square_homology_eq_positive
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass] at h
  exact h.symm.trans hz

public theorem positiveTwoCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : CellularHomology.IntegralComparison) (j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 1 (0 : Fin 4) j = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  apply T.attachingDegree_zero_of_positiveLoop
  exact positiveCell_positiveLoop_homology_zero W

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
