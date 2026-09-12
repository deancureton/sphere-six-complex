module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryPaths

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def oneSkeletonOrigin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (b : Bool) :
    constructedCentralOneSkeleton W :=
  ⟨constructedCentralOriginOrbit W b, by
    apply Or.inl
    cases b
    · exact Set.mem_iUnion.mpr ⟨0, 0, by simp, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨1, 0, by simp, rfl⟩⟩

public theorem actualHexagonSidePath_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    actualHexagonSidePath W i t ∈ constructedCentralOneSkeleton W :=
  Or.inr (Set.mem_iUnion.mpr ⟨boundaryZeroOneEdge i,
    correctedPlaneCellOrbit_side_mem_edge W i t⟩)

public def oneSkeletonHexagonSidePath
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    Path (oneSkeletonOrigin W (cellChart 0 i).1)
      (oneSkeletonOrigin W
        (cellChart 0 (cellNextIndex i)).1) where
  toFun t := ⟨actualHexagonSidePath W i t,
    actualHexagonSidePath_mem_oneSkeleton W i t⟩
  continuous_toFun := (actualHexagonSidePath W i).continuous.subtype_mk _
  source' := Subtype.ext (actualHexagonSidePath W i).source
  target' := Subtype.ext (actualHexagonSidePath W i).target

public theorem centralOneSkeletonEdgePaths_homotopic
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

public theorem oneSkeletonHexagonSidePath_opposite_homotopic
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    (oneSkeletonHexagonSidePath W 0).Homotopic
      (oneSkeletonHexagonSidePath W 3).symm ∧
    (oneSkeletonHexagonSidePath W 1).symm.Homotopic
      (oneSkeletonHexagonSidePath W 4) ∧
    (oneSkeletonHexagonSidePath W 2).Homotopic
      (oneSkeletonHexagonSidePath W 5).symm := by
  refine ⟨?_, ?_, ?_⟩
  · apply centralOneSkeletonEdgePaths_homotopic W 1
    · exact correctedPlaneCellOrbit_side_mem_edge W 0
    · intro t
      exact correctedPlaneCellOrbit_side_mem_edge W 3 (unitInterval.symm t)
  · apply centralOneSkeletonEdgePaths_homotopic W 0
    · intro t
      exact correctedPlaneCellOrbit_side_mem_edge W 1 (unitInterval.symm t)
    · exact correctedPlaneCellOrbit_side_mem_edge W 4
  · apply centralOneSkeletonEdgePaths_homotopic W 2
    · exact correctedPlaneCellOrbit_side_mem_edge W 2
    · intro t
      exact correctedPlaneCellOrbit_side_mem_edge W 5 (unitInterval.symm t)

public def oneSkeletonHexagonLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Path (oneSkeletonOrigin W false) (oneSkeletonOrigin W false) :=
  (((((oneSkeletonHexagonSidePath W 0).trans
    (oneSkeletonHexagonSidePath W 1)).trans
    (oneSkeletonHexagonSidePath W 2)).trans
    (oneSkeletonHexagonSidePath W 3)).trans
    (oneSkeletonHexagonSidePath W 4)).trans
    (oneSkeletonHexagonSidePath W 5)

public theorem oneSkeletonHexagonLoop_homology_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    SphereSixComplex.StandardCircleHomologyLiftDegree.loopHomologyClass
      (oneSkeletonHexagonLoop W) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := oneSkeletonHexagonSidePath_opposite_homotopic W
  exact SphereSixComplex.alternatingHexagonBoundaryPath_homology_zero
    (oneSkeletonHexagonSidePath W 0)
    (oneSkeletonHexagonSidePath W 2)
    (oneSkeletonHexagonSidePath W 4)
    (oneSkeletonHexagonSidePath W 1)
    (oneSkeletonHexagonSidePath W 3)
    (oneSkeletonHexagonSidePath W 5) h₀ h₁ h₂

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
