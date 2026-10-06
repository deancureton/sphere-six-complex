module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Analysis.Complex.Basic

/-! # Complex manifolds as real manifolds -/

@[expose] public section

open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A complex manifold is a real manifold on the same chart carrier and with the same selected
atlas. -/
public theorem isManifoldRealOfComplex
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω}
    (h : IsManifold (modelWithCornersSelf ℂ E) n M) :
    IsManifold (modelWithCornersSelf ℝ E) n M := by
  let _ : IsManifold (modelWithCornersSelf ℂ E) n M := h
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ E) n M
  intro e e' he he'
  have hc := (modelWithCornersSelf ℂ E).contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := n) he)
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := n) he')
  simpa [ModelWithCorners.extendCoordChange, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm] using hc.restrict_scalars ℝ

end SphereSixComplex
