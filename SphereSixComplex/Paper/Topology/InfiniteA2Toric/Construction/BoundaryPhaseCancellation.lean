module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HexagonBoundaryPhaseGauge
@[expose] public section

noncomputable section
open Function Set Topology Matrix
open SphereSixComplex.Geometry.CuspLocalPhaseAction
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
namespace Construction

public def cellPreviousIndex : Fin 6 → Fin 6 := ![5, 0, 1, 2, 3, 4]

public theorem correctedPlaneTile_zero_one (i : Fin 6)
    (p : CellSquare) (hp : p.1 1 = 0) :
    correctedPlaneTile 0 i p =
      (1 - p.1 0 / 2) • planeVertexOffset i +
        (p.1 0 / 2) • planeNextVertexOffset i := by
  have hle : p.1 1 ≤ p.1 0 := by rw [hp]; exact (p.2 0).1
  rw [correctedPlaneTile, planeTile_of_ge 0 i p hle]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [correctedPlaneCenter, planeVertexOffset,
      planeNextVertexOffset, planeNextMidpointOffset, hp] <;> ring

public theorem correctedPlaneTile_zero_zero (i : Fin 6)
    (p : CellSquare) (hp : p.1 0 = 0) :
    correctedPlaneTile 0 i p =
      (p.1 1 / 2) • planeVertexOffset (cellPreviousIndex i) +
        (1 - p.1 1 / 2) •
          planeNextVertexOffset (cellPreviousIndex i) := by
  have hle : p.1 0 ≤ p.1 1 := by rw [hp]; exact (p.2 1).1
  rw [correctedPlaneTile, planeTile_of_le 0 i p hle]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [correctedPlaneCenter, planeVertexOffset,
      planeNextVertexOffset, planeMidpointOffset,
      cellPreviousIndex, hp] <;> ring

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end Construction

open SphereSixComplex.Geometry.CuspCombinatorics

namespace Construction

public def boundaryZeroOneTarget : Fin 6 → ChartIndex :=
  ![(false, 0), (true, 0), (false, 0), (true, -e₁), (false, 0), (true, -e₂)]

public def boundaryZeroZeroTarget : Fin 6 → ChartIndex :=
  ![(false, 0), (true, -e₁), (false, 0), (true, -e₂), (false, 0), (true, 0)]

open SphereSixComplex.Geometry.CuspCollar

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
