module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CompactPhaseCorrection

@[expose] public section

noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public def hexagonVertexWeights (x : Fin 2 → ℝ) : Fin 6 → ℝ :=
  let a := (3 / 2 : ℝ) * x 0
  let b := (3 / 2 : ℝ) * x 1
  ![max 0 (min a (a - b)), max 0 (min a b), max 0 (min b (b - a)),
    max 0 (min (-a) (b - a)), max 0 (min (-a) (-b)), max 0 (min (-b) (a - b))]

public theorem continuous_hexagonVertexWeights :
    Continuous hexagonVertexWeights := by
  unfold hexagonVertexWeights
  fun_prop

public def hexagonVertexInterpolation (v : Fin 6 → Fin 2 → ℝ)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ∑ i, hexagonVertexWeights x i • v i

public theorem continuous_hexagonVertexInterpolation (v : Fin 6 → Fin 2 → ℝ) :
    Continuous (hexagonVertexInterpolation v) := by
  unfold hexagonVertexInterpolation
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_hexagonVertexWeights).smul
    continuous_const

public def boundaryAngleVertices (a b c d : ℝ) : Fin 6 → Fin 2 → ℝ :=
  ![![0, 0], ![0, a], ![a - b, b], ![c, b], ![c, d - c], ![d, 0]]

public def boundaryAngleGauge (a b c d : ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  hexagonVertexInterpolation (boundaryAngleVertices a b c d)

public theorem continuous_boundaryAngleGauge (a b c d : ℝ) :
    Continuous (boundaryAngleGauge a b c d) :=
  continuous_hexagonVertexInterpolation _

open SphereSixComplex.Geometry.CuspLocalPhaseAction

public def boundaryCompactGauge (u v : CompactTorus)
    (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  fun j ↦ Circle.exp (boundaryAngleGauge
    (-Complex.arg (u 0 * u 1 * (u 2)⁻¹)) (-Complex.arg (u 1))
    (-Complex.arg (v 0)) (-Complex.arg (v 0 * v 1 * (v 2)⁻¹)) x j)

public theorem continuous_boundaryCompactGauge (u v : CompactTorus) :
    Continuous (boundaryCompactGauge u v) := by
  apply continuous_pi
  intro j
  exact Circle.exp.continuous.comp
    ((continuous_apply j).comp (continuous_boundaryAngleGauge _ _ _ _))

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
