module

public import SphereSixComplex.Paper.Geometry.StandardInfiniteA2PositiveQuadrantAtlas
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveRelativeCW

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public def positiveSublevel (r : ℝ) : TopologicalSpace.Opens carrierPositivePart where
  carrier := {x | constructedModel.t x.1 ∈ Metric.ball 0 r}
  is_open' := Metric.isOpen_ball.preimage
    (constructedModel.t_holomorphic.continuous.comp continuous_subtype_val)

public def positiveSublevelHomeomorph (r : ℝ) :
    positiveSublevel r ≃ₜ constructedLocalPositivePart r where
  toFun x := ⟨⟨x.1.1, x.2⟩, (mem_constructedLocalPositivePart_iff r _).mpr x.1.2⟩
  invFun x := ⟨⟨x.1.1, (mem_constructedLocalPositivePart_iff r _).mp x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

@[instance_reducible]
public def localPositiveQuadrantChartedSpace (r : ℝ) :
    ChartedSpace (EuclideanQuadrant 3) (constructedLocalPositivePart r) := by
  let _ := positiveQuadrantChartedSpace
  exact SphereSixComplex.transportChartedSpace (positiveSublevelHomeomorph r)

public theorem localPositiveQuadrantIsManifold (r : ℝ) :
    letI := localPositiveQuadrantChartedSpace r
    IsManifold (modelWithCornersEuclideanQuadrant 3) 1 (constructedLocalPositivePart r) := by
  let _ := positiveQuadrantChartedSpace
  let _ := positiveQuadrantIsManifold
  exact SphereSixComplex.isManifold_transportChartedSpace (positiveSublevelHomeomorph r)

public theorem localPositiveQuadrant_boundary (r : ℝ) :
    letI := localPositiveQuadrantChartedSpace r
    (modelWithCornersEuclideanQuadrant 3).boundary (constructedLocalPositivePart r) =
      {q | constructedModel.t q.1.1 = 0} := by
  let _ := positiveQuadrantChartedSpace
  let _ := positiveQuadrantIsManifold
  let _ := localPositiveQuadrantChartedSpace r
  let h := SphereSixComplex.transportDiffeomorph
    (I := modelWithCornersEuclideanQuadrant 3) (n := 1) (positiveSublevelHomeomorph r)
  have hb := h.preimage_boundary one_ne_zero
  rw [ModelWithCorners.boundary_open, positiveQuadrant_boundary] at hb
  ext q
  have hq := congrArg (fun s ↦ (positiveSublevelHomeomorph r).symm q ∈ s) hb
  have hq := Iff.of_eq hq
  change (positiveSublevelHomeomorph r) ((positiveSublevelHomeomorph r).symm q) ∈
    (modelWithCornersEuclideanQuadrant 3).boundary (constructedLocalPositivePart r) ↔
      constructedModel.t q.1.1 = 0 at hq
  rw [Homeomorph.apply_symm_apply] at hq
  exact hq

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
