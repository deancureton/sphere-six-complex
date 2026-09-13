module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryLoop
public import SphereSixComplex.Paper.Topology.SquareRadialCircleComparison

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion
open StandardCircleHomologyLiftDegree

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def correctedBallBoundaryMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(CWCharacteristicBoundarySphere 2, centralBoundary W) where
  toFun x := ⟨boundaryCorrectedBallOrbit W ⟨x.1, Metric.sphere_subset_closedBall x.2⟩,
    constructedCentralOneSkeleton_subset_centralBoundary W
      (boundaryCorrectedBallOrbit_boundary_mem_oneSkeleton W _ x.2)⟩
  continuous_toFun := ((continuous_boundaryCorrectedBallOrbit W).comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

public theorem correctedBallBoundaryMap_side
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    (correctedBallBoundaryMap W
      (squareBoundaryHexagonHomeomorph.symm (hexagonBoundarySidePath i t))).1 =
      actualHexagonSidePath W i t := by
  let x := squareBoundaryHexagonHomeomorph.symm (hexagonBoundarySidePath i t)
  have he : boundaryCorrectedBallOrbit W ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ =
      correctedPlaneCellOrbit W
        ⟨correctedHexagonHomeomorph 0 x.1,
          (correctedHexagonHomeomorph_mem_closed_iff 0 x.1).mpr
            (Metric.sphere_subset_closedBall x.2)⟩ := rfl
  change boundaryCorrectedBallOrbit W ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = _
  rw [he]
  apply congrArg (correctedPlaneCellOrbit W)
  apply Subtype.ext
  exact congrArg (fun z : HexagonBoundary ↦ z.1)
    (squareBoundaryHexagonHomeomorph.apply_symm_apply (hexagonBoundarySidePath i t))

public theorem correctedBallBoundaryMap_positiveLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    loopHomologyClass (cwSquareBoundaryPositiveLoop.map
      (correctedBallBoundaryMap W).continuous) = 0 := by
  let f := (correctedBallBoundaryMap W).comp
    ⟨squareBoundaryHexagonHomeomorph.symm, squareBoundaryHexagonHomeomorph.symm.continuous⟩
  let g := oneSkeletonToCentralBoundary W
  have hi (i : Fin 6) (t : unitInterval) :
      f (hexagonBoundarySidePath i t) = g (oneSkeletonHexagonSidePath W i t) := by
    apply Subtype.ext
    exact correctedBallBoundaryMap_side W i t
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
  have hb : f (hexagonBoundaryVertex 0) = g (oneSkeletonOrigin W false) := by
    exact (congrArg f (hexagonBoundarySidePath 0).source).symm.trans
      ((hi 0 0).trans (congrArg g (oneSkeletonHexagonSidePath W 0).source))
  have hp : hexagonBoundaryLoop.map f.continuous =
      ((oneSkeletonHexagonLoop W).map g.continuous).cast hb hb := by
    apply Path.ext
    funext t
    exact hl t
  have hz : loopHomologyClass (hexagonBoundaryLoop.map f.continuous) = 0 := by
    rw [hp, loopHomologyClass_cast]
    exact centralBoundaryHexagonLoop_homology_zero W
  have h := congrArg (integralSingularHomologyMap 1 (correctedBallBoundaryMap W))
    hexagonBoundaryLoop_square_homology_eq_positive
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass] at h
  exact h.symm.trans hz

public theorem correctedBallBoundaryMap_homologyOne_eq_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    integralSingularHomologyMap 1 (correctedBallBoundaryMap W) = 0 :=
  cwSquareBoundaryHomologyMap_eq_zero_of_positiveLoop _
    (correctedBallBoundaryMap_positiveLoop_homology_zero W)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
