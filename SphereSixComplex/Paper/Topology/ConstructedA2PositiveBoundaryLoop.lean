module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveBoundaryPaths

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedA2OneSkeletonOrigin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (b : Bool) :
    constructedCentralOneSkeleton W :=
  ⟨constructedCentralOriginOrbit W b, by
    apply Or.inl
    cases b
    · exact Set.mem_iUnion.mpr ⟨0, 0, by simp, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨1, 0, by simp, rfl⟩⟩

public theorem constructedA2ActualHexagonSidePath_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    constructedA2ActualHexagonSidePath W i t ∈ constructedCentralOneSkeleton W :=
  Or.inr (Set.mem_iUnion.mpr ⟨constructedA2BoundaryZeroOneEdge i,
    constructedA2CorrectedPlaneCellOrbit_side_mem_edge W i t⟩)

public def constructedA2OneSkeletonHexagonSidePath
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    Path (constructedA2OneSkeletonOrigin W (constructedA2CellChart 0 i).1)
      (constructedA2OneSkeletonOrigin W
        (constructedA2CellChart 0 (constructedA2CellNextIndex i)).1) where
  toFun t := ⟨constructedA2ActualHexagonSidePath W i t,
    constructedA2ActualHexagonSidePath_mem_oneSkeleton W i t⟩
  continuous_toFun := (constructedA2ActualHexagonSidePath W i).continuous.subtype_mk _
  source' := Subtype.ext (constructedA2ActualHexagonSidePath W i).source
  target' := Subtype.ext (constructedA2ActualHexagonSidePath W i).target

public theorem constructedCentralOneSkeletonEdgePaths_homotopic
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3)
    {x y : constructedCentralOneSkeleton W} (p q : Path x y)
    (hp : ∀ t, (p t).1 ∈ constructedCentralOneCell W i '' Metric.closedBall 0 1)
    (hq : ∀ t, (q t).1 ∈ constructedCentralOneCell W i '' Metric.closedBall 0 1) :
    p.Homotopic q := by
  let Z := Metric.closedBall (0 : Fin 1 → ℝ) 1
  let _ : ContractibleSpace Z :=
    (convex_closedBall (0 : Fin 1 → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let f : Z → constructedCentralOneSkeleton W := fun z ↦
    ⟨constructedCentralOneCell W i z.1,
      Or.inr (Set.mem_iUnion.mpr ⟨i, z.1, z.2, rfl⟩)⟩
  have hf : Continuous f := (constructedCentralOneCell_continuousOn W i).domRestrict.subtype_mk _
  apply SphereSixComplex.paths_homotopic_of_range_in_embedded_contractible f
    (hf.isClosedEmbedding (by
      intro x y h
      apply Subtype.ext
      have hxy := congrArg Subtype.val h
      fin_cases i
      · exact constructedCentralEdgeZeroOrbit_injOn_closedBall W x.2 y.2 hxy
      · exact constructedCentralEdgeOneOrbit_injOn_closedBall W x.2 y.2 hxy
      · exact constructedCentralEdgeTwoOrbit_injOn_closedBall W x.2 y.2 hxy)).isEmbedding p q
  · intro t
    obtain ⟨z, hz, he⟩ := hp t
    exact ⟨⟨z, hz⟩, Subtype.ext he⟩
  · intro t
    obtain ⟨z, hz, he⟩ := hq t
    exact ⟨⟨z, hz⟩, Subtype.ext he⟩

public theorem constructedA2OneSkeletonHexagonSidePath_opposite_homotopic
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    (constructedA2OneSkeletonHexagonSidePath W 0).Homotopic
      (constructedA2OneSkeletonHexagonSidePath W 3).symm ∧
    (constructedA2OneSkeletonHexagonSidePath W 1).symm.Homotopic
      (constructedA2OneSkeletonHexagonSidePath W 4) ∧
    (constructedA2OneSkeletonHexagonSidePath W 2).Homotopic
      (constructedA2OneSkeletonHexagonSidePath W 5).symm := by
  refine ⟨?_, ?_, ?_⟩
  · apply constructedCentralOneSkeletonEdgePaths_homotopic W 1
    · exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 0
    · intro t
      exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 3 (unitInterval.symm t)
  · apply constructedCentralOneSkeletonEdgePaths_homotopic W 0
    · intro t
      exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 1 (unitInterval.symm t)
    · exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 4
  · apply constructedCentralOneSkeletonEdgePaths_homotopic W 2
    · exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 2
    · intro t
      exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 5 (unitInterval.symm t)

public def constructedA2OneSkeletonHexagonLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Path (constructedA2OneSkeletonOrigin W false) (constructedA2OneSkeletonOrigin W false) :=
  (((((constructedA2OneSkeletonHexagonSidePath W 0).trans
    (constructedA2OneSkeletonHexagonSidePath W 1)).trans
    (constructedA2OneSkeletonHexagonSidePath W 2)).trans
    (constructedA2OneSkeletonHexagonSidePath W 3)).trans
    (constructedA2OneSkeletonHexagonSidePath W 4)).trans
    (constructedA2OneSkeletonHexagonSidePath W 5)

public theorem constructedA2OneSkeletonHexagonLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
      (constructedA2OneSkeletonHexagonLoop W) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := constructedA2OneSkeletonHexagonSidePath_opposite_homotopic W
  exact SphereSixComplex.alternatingHexagonBoundaryPath_homology_zero
    (constructedA2OneSkeletonHexagonSidePath W 0)
    (constructedA2OneSkeletonHexagonSidePath W 2)
    (constructedA2OneSkeletonHexagonSidePath W 4)
    (constructedA2OneSkeletonHexagonSidePath W 1)
    (constructedA2OneSkeletonHexagonSidePath W 3)
    (constructedA2OneSkeletonHexagonSidePath W 5) h₀ h₁ h₂

end SphereSixComplex.Geometry.InfiniteA2Toric
