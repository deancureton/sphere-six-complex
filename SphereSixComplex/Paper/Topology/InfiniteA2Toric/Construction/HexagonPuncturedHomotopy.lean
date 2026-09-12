module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HexagonQuadrantPaths

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex

public theorem planeCirclePoint_ne_zero (r : ℝ) (hr : r ≠ 0) (t : ℝ) :
    planeCirclePoint r t ≠ 0 := by
  intro h
  have h₀ : r * Real.cos (2 * Real.pi * t) = 0 := congrFun h 0
  have h₁ : r * Real.sin (2 * Real.pi * t) = 0 := congrFun h 1
  have hc := (mul_eq_zero.mp h₀).resolve_left hr
  have hs := (mul_eq_zero.mp h₁).resolve_left hr
  have hsq := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  rw [hc, hs] at hsq
  norm_num at hsq

public abbrev PuncturedRealPlane := {x : Fin 2 → ℝ // x ≠ 0}

public def planeCirclePuncturedPoint (r : ℝ) (hr : r ≠ 0) : ContinuousMap ℝ PuncturedRealPlane :=
  ⟨fun t ↦ ⟨planeCirclePoint r t, planeCirclePoint_ne_zero r hr t⟩,
    (planeCirclePoint_continuous r).subtype_mk _⟩

namespace Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public theorem hexagonBoundary_ne_zero (z : HexagonBoundary) :
    z.1 ≠ 0 := by
  intro hz
  have h := z.2
  rw [hz] at h
  norm_num [hexagonGauge] at h

public def hexagonBoundaryToPunctured :
    ContinuousMap HexagonBoundary PuncturedRealPlane :=
  ⟨fun z ↦ ⟨z.1, hexagonBoundary_ne_zero z⟩,
    continuous_subtype_val.subtype_mk hexagonBoundary_ne_zero⟩

public def circlePuncturedQuarterPath (i : Fin 4) :
    Path (planeCirclePuncturedPoint (2 / 3) (by norm_num) ((i : ℝ) / 4))
      (planeCirclePuncturedPoint (2 / 3) (by norm_num) (((i : ℝ) + 1) / 4)) :=
  (Path.segment ((i : ℝ) / 4) (((i : ℝ) + 1) / 4)).map
    (planeCirclePuncturedPoint (2 / 3) (by norm_num)).continuous

public def hexagonPuncturedQuarterPath (i : Fin 4) :
    Path (planeCirclePuncturedPoint (2 / 3) (by norm_num) ((i : ℝ) / 4))
      (planeCirclePuncturedPoint (2 / 3) (by norm_num) (((i : ℝ) + 1) / 4)) :=
  ((hexagonBoundaryQuarterPath i).map
    hexagonBoundaryToPunctured.continuous).cast
      (Subtype.ext (planeCirclePoint_quarter_start i))
      (Subtype.ext (planeCirclePoint_quarter_end i))

public theorem hexagonPuncturedQuarterPath_homotopic (i : Fin 4) :
    (hexagonPuncturedQuarterPath i).Homotopic
      (circlePuncturedQuarterPath i) := by
  have hx : 0 < quadrantFunctional i (planeCirclePoint (2 / 3) ((i : ℝ) / 4)) := by
    have h := planeCircleQuarterPath_mem_halfspace (2 / 3) (by norm_num) i 0
    simpa only [Path.source] using h
  have hy : 0 < quadrantFunctional i (planeCirclePoint (2 / 3) (((i : ℝ) + 1) / 4)) := by
    have h := planeCircleQuarterPath_mem_halfspace (2 / 3) (by norm_num) i 1
    simpa only [Path.target] using h
  exact convex_paths_homotopic_in_superset (quadrantHalfSpace_convex i)
    (fun _ h ↦ quadrantHalfSpace_ne_zero i h)
    (hexagonPlaneQuarterPath i) (planeCircleQuarterPath (2 / 3) i)
    hx hy (hexagonPlaneQuarterPath_mem_quadrant i)
    (planeCircleQuarterPath_mem_halfspace (2 / 3) (by norm_num) i)

end Construction

end Geometry.InfiniteA2Toric
end SphereSixComplex
