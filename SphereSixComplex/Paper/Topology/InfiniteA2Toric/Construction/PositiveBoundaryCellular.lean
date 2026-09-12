module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryLoop
public import SphereSixComplex.Paper.Topology.ConstructedA2EdgeIncidence

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem oneSkeleton_eq_cwSkeleton
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

public def oneSkeletonCWHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    let _ := (constructedCentralCellAtlas W).cwComplex
    constructedCentralOneSkeleton W ≃ₜ
      IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  exact Homeomorph.setCongr (oneSkeleton_eq_cwSkeleton W)

public theorem cellularHexagonLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
      ((oneSkeletonHexagonLoop W).map
        (oneSkeletonCWHomeomorph W).continuous) = 0 := by
  let _ := (constructedCentralCellAtlas W).cwComplex
  have h := SphereSixComplex.StandardCircleHomologyLiftDegree.integralSingularHomologyMap_loopHomologyClass
    (⟨oneSkeletonCWHomeomorph W,
      (oneSkeletonCWHomeomorph W).continuous⟩ :
      ContinuousMap (constructedCentralOneSkeleton W)
        (IntegralCWSkeletonLT (ActualLocalCuspCentralOrbitQuotient W) 2))
    (oneSkeletonHexagonLoop W)
  rw [oneSkeletonHexagonLoop_homology_zero, map_zero] at h
  exact h.symm

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
