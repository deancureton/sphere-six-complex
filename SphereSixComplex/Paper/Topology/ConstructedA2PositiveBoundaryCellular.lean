module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveBoundaryLoop
public import SphereSixComplex.Paper.Topology.ConstructedA2EdgeIncidence

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2OneSkeleton_eq_cwSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    constructedCentralOneSkeleton W =
      (Topology.RelCWComplex.skeletonLT
        (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W)) (2 : ℕ∞) : Set _) := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  dsimp only
  have h₁ := Topology.CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
    (C := (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W))) 1
  have h₀ := Topology.CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
    (C := (Set.univ : Set (ActualLocalCuspCentralOrbitQuotient W))) 0
  norm_num only [Nat.cast_one, Nat.cast_zero, zero_add, one_add_one_eq_two] at h₁ h₀
  rw [← h₁, ← h₀, Topology.CWComplex.skeletonLT_zero_eq_empty, Set.empty_union]
  rfl

public def constructedA2OneSkeletonCWHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    constructedCentralOneSkeleton W ≃ₜ
      IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact Homeomorph.setCongr (constructedA2OneSkeleton_eq_cwSkeleton W)

public theorem constructedA2CellularHexagonLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
      ((constructedA2OneSkeletonHexagonLoop W).map
        (constructedA2OneSkeletonCWHomeomorph W).continuous) = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  have h := SphereSixComplex.StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass
    (⟨constructedA2OneSkeletonCWHomeomorph W,
      (constructedA2OneSkeletonCWHomeomorph W).continuous⟩ :
      ContinuousMap (constructedCentralOneSkeleton W)
        (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2))
    (constructedA2OneSkeletonHexagonLoop W)
  rw [constructedA2OneSkeletonHexagonLoop_homology_zero, map_zero] at h
  exact h.symm

end SphereSixComplex.Geometry.InfiniteA2Toric
