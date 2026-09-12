module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.HoneycombCorrectedHexagonalCell

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

namespace Construction

public theorem correctedHexagonCenter_mem
    (v : ToricLattice) :
    correctedPlaneCenter v ∈ correctedPlaneCell v := by
  have h := (correctedHexagonHomeomorph_mem_closed_iff v 0).mpr
    (Metric.mem_closedBall_self zero_le_one)
  simpa [correctedHexagonHomeomorph,
    squareToHexagonRadial] using h

public noncomputable def correctedPositiveHexagonMap
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) (x : Fin 2 → ℝ) :
    constructedPositiveCentralFiber r := by
  classical
  exact if hx : correctedHexagonHomeomorph v x ∈
      correctedPlaneCell v then
    (correctedFiniteQuotientCellHomeomorph hr v
      ⟨correctedHexagonHomeomorph v x, hx⟩ :
        constructedPositiveCentralCell r v)
  else correctedFiniteQuotientCellHomeomorph hr v
      ⟨correctedPlaneCenter v,
        correctedHexagonCenter_mem v⟩

public theorem correctedPositiveHexagonMap_of_mem_closedBall
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.closedBall 0 1) :
    correctedPositiveHexagonMap hr v x =
      (correctedFiniteQuotientCellHomeomorph hr v
        ⟨correctedHexagonHomeomorph v x,
          (correctedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩ :
            constructedPositiveCentralCell r v) := by
  classical
  rw [correctedPositiveHexagonMap, dite_eq_left]











end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric

end
