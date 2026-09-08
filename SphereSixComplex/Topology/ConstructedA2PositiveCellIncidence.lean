module

public import SphereSixComplex.Topology.SquareRadialCircleComparison

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2PositiveCell_boundary_formula
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : CWCharacteristicBoundarySphere 2) :
    constructedCentralCellMap W 2 (0 : Fin 4) x.1 =
      constructedA2CorrectedPlaneCellOrbit W
        ⟨constructedA2CorrectedHexagonHomeomorph 0 x.1,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff 0 x.1).mpr
            (Metric.sphere_subset_closedBall x.2)⟩ := by
  change constructedA2CorrectedPositiveTwoOrbit W x.1 = _
  rw [constructedA2CorrectedPositiveTwoOrbit_closedBall W
    ⟨x.1, Metric.sphere_subset_closedBall x.2⟩]
  rfl

public theorem constructedA2PositiveCell_boundary_side
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    constructedCentralCellMap W 2 (0 : Fin 4)
      (constructedA2SquareBoundaryHexagonHomeomorph.symm
        (constructedA2HexagonBoundarySidePath i t)).1 =
      constructedA2ActualHexagonSidePath W i t := by
  rw [constructedA2PositiveCell_boundary_formula]
  change constructedA2CorrectedPlaneCellOrbit W _ =
    constructedA2CorrectedPlaneCellOrbit W (constructedA2HexagonSide i t)
  apply congrArg (constructedA2CorrectedPlaneCellOrbit W)
  apply Subtype.ext
  exact congrArg (fun z : ConstructedA2HexagonBoundary ↦ z.1) (constructedA2SquareBoundaryHexagonHomeomorph.apply_symm_apply
    (constructedA2HexagonBoundarySidePath i t))

public def constructedA2PositiveCellBoundaryMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    ContinuousMap (CWCharacteristicBoundarySphere 2)
      (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact (integralCWCharacteristicPairMap (ActualLocalCuspCentralOrbitQuotient W)
    2 (0 : Fin 4)).boundaryMap.hom

public theorem constructedA2PositiveCell_positiveLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    loopHomologyClass (cwSquareBoundaryPositiveLoop.map
      (constructedA2PositiveCellBoundaryMap W).continuous) = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  let f : ContinuousMap ConstructedA2HexagonBoundary
      (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) :=
    (constructedA2PositiveCellBoundaryMap W).comp
      ⟨constructedA2SquareBoundaryHexagonHomeomorph.symm,
        constructedA2SquareBoundaryHexagonHomeomorph.symm.continuous⟩
  let g : ContinuousMap (constructedCentralOneSkeleton W)
      (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2) :=
    ⟨constructedA2OneSkeletonCWHomeomorph W, (constructedA2OneSkeletonCWHomeomorph W).continuous⟩
  have hi (i : Fin 6) (t : unitInterval) :
      f (constructedA2HexagonBoundarySidePath i t) =
        g (constructedA2OneSkeletonHexagonSidePath W i t) := by
    apply Subtype.ext
    exact constructedA2PositiveCell_boundary_side W i t
  have hl (t : unitInterval) : f (constructedA2HexagonBoundaryLoop t) =
      g (constructedA2OneSkeletonHexagonLoop W t) := by
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 5) t
    intro u
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 4) u
    intro v
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 3) v
    intro w
    apply path_trans_pointwise f g _ _ _ _ ?_ (hi 2) w
    exact path_trans_pointwise f g _ _ _ _ (hi 0) (hi 1)
  have hb : f (constructedA2HexagonBoundaryVertex 0) =
      g (constructedA2OneSkeletonOrigin W false) := by
    exact (congrArg f (constructedA2HexagonBoundarySidePath 0).source).symm.trans
      ((hi 0 0).trans (congrArg g (constructedA2OneSkeletonHexagonSidePath W 0).source))
  have hp : constructedA2HexagonBoundaryLoop.map f.continuous =
      ((constructedA2OneSkeletonHexagonLoop W).map g.continuous).cast hb hb := by
    apply Path.ext
    funext t
    exact hl t
  have hz : loopHomologyClass (constructedA2HexagonBoundaryLoop.map f.continuous) = 0 := by
    rw [hp, loopHomologyClass_cast]
    exact constructedA2CellularHexagonLoop_homology_zero W
  have h := congrArg (integralSingularHomologyMap 1 (constructedA2PositiveCellBoundaryMap W))
    hexagonBoundaryLoop_square_homology_eq_positive
  rw [integralSingularHomologyMap_loopHomologyClass,
    integralSingularHomologyMap_loopHomologyClass] at h
  exact h.symm.trans hz

public theorem constructedA2PositiveTwoCell_attachingDegree_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (T : IntegralCWCellularHomologyFoundation) (j : Fin 3) :
    let _ := (constructedCentralCellAtlas W).cwComplex
    T.attachingDegree (ActualLocalCuspCentralOrbitQuotient W) 1 (0 : Fin 4) j = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  apply T.attachingDegree_zero_of_positiveLoop
  exact constructedA2PositiveCell_positiveLoop_homology_zero W

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
