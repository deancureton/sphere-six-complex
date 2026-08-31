module

public import SphereSixComplex.Topology.ConstructedA2PositiveCOneManifoldBoundaryProof

/-!
# The global smooth model of the constructed A₂ moment strip

The exponential log-position map embeds the closed-height moment strip as the open subset
`(0, ∞) × (0, ∞) × [0, r)` of the Euclidean quadrant.  This supplies a single global
quadrant chart, its manifold structure, and its exact zero-height boundary.
-/

@[expose] public section

noncomputable section

open Function Set TopologicalSpace Topology WithLp

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The global exponential log-position chart of the moment strip. -/
public noncomputable def constructedA2MomentQuadrantEmbedding (r : ℝ) :
    constructedPositiveMomentRegion r → EuclideanQuadrant 3 :=
  fun x ↦ (constructedA2MomentQuadrantHomeomorph r x).1

public theorem constructedA2MomentQuadrantEmbedding_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (constructedA2MomentQuadrantEmbedding r) := by
  exact (constructedA2PositiveQuadrantTarget r).isOpen.isOpenEmbedding_subtypeVal.comp
    (constructedA2MomentQuadrantHomeomorph r).isOpenEmbedding

/-- The singleton global chart on the logarithmic moment strip. -/
@[instance_reducible]
public noncomputable def constructedA2MomentRegionChartedSpace
    (r : ℝ) (hr : 0 < r) :
    ChartedSpace (EuclideanQuadrant 3) (constructedPositiveMomentRegion r) := by
  let _ : Nonempty (constructedPositiveMomentRegion r) :=
    ⟨⟨![0, 0, 0], by simp [constructedPositiveMomentRegion, hr]⟩⟩
  exact (constructedA2MomentQuadrantEmbedding_isOpenEmbedding r).singletonChartedSpace

/-- The logarithmic moment strip is a smooth three-manifold with corners. -/
public theorem constructedA2MomentRegion_isManifold {r : ℝ} (hr : 0 < r) :
    let _ := constructedA2MomentRegionChartedSpace r hr
    IsManifold (modelWithCornersEuclideanQuadrant 3) 1
      (constructedPositiveMomentRegion r) := by
  let _ : Nonempty (constructedPositiveMomentRegion r) :=
    ⟨⟨![0, 0, 0], by simp [constructedPositiveMomentRegion, hr]⟩⟩
  let _ := constructedA2MomentRegionChartedSpace r hr
  exact (constructedA2MomentQuadrantEmbedding_isOpenEmbedding r).isManifold_singleton

/-- In the global quadrant atlas, the manifold boundary of the moment strip is exactly its
zero-height locus. -/
public theorem constructedA2MomentRegion_boundary {r : ℝ} (hr : 0 < r) :
    let _ := constructedA2MomentRegionChartedSpace r hr
    (modelWithCornersEuclideanQuadrant 3).boundary
        (constructedPositiveMomentRegion r) =
      {x | x.1 2 = 0} := by
  let _ : Nonempty (constructedPositiveMomentRegion r) :=
    ⟨⟨![0, 0, 0], by simp [constructedPositiveMomentRegion, hr]⟩⟩
  let _ := constructedA2MomentRegionChartedSpace r hr
  ext x
  have hchart : ⇑(@chartAt (EuclideanQuadrant 3) inferInstance
      (constructedPositiveMomentRegion r) inferInstance
      (constructedA2MomentRegionChartedSpace r hr) x) =
        constructedA2MomentQuadrantEmbedding r := by
    unfold constructedA2MomentRegionChartedSpace
    exact Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq
      (constructedA2MomentQuadrantEmbedding_isOpenEmbedding r)
  change (modelWithCornersEuclideanQuadrant 3).IsBoundaryPoint x ↔ x.1 2 = 0
  rw [ModelWithCorners.isBoundaryPoint_iff, extChartAt_coe]
  rw [hchart]
  change (modelWithCornersEuclideanQuadrant 3
      (constructedA2MomentQuadrantEmbedding r x)) ∈
      frontier (range (modelWithCornersEuclideanQuadrant 3)) ↔ x.1 2 = 0
  rw [frontier, (modelWithCornersEuclideanQuadrant 3).isClosed_range.closure_eq]
  rw [show range (modelWithCornersEuclideanQuadrant 3) =
      {y : EuclideanSpace ℝ (Fin 3) | ∀ i, 0 ≤ y i} from range_euclideanQuadrant 3]
  rw [interior_euclideanQuadrant]
  simp only [modelWithCornersEuclideanQuadrant_apply, mem_sdiff, mem_ofPred_eq,
    constructedA2MomentQuadrantEmbedding, constructedA2MomentQuadrantHomeomorph]
  constructor
  · rintro ⟨_, hnot⟩
    by_contra hzero
    apply hnot
    intro i
    fin_cases i
    · exact Real.exp_pos _
    · exact Real.exp_pos _
    · exact lt_of_le_of_ne x.2.1 (Ne.symm hzero)
  · intro hzero
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · exact (Real.exp_pos _).le
      · exact (Real.exp_pos _).le
      · exact x.2.1
    · intro hpos
      exact (ne_of_gt (hpos 2)) hzero

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end

end
