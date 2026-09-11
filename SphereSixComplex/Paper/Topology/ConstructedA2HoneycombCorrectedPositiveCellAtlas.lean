module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCorrectedHexagonalCell

@[expose] public section

noncomputable section

open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public theorem constructedA2CorrectedHexagonCenter_mem
    (v : ToricLattice) :
    constructedA2CorrectedPlaneCenter v ∈ constructedA2CorrectedPlaneCell v := by
  have h := (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v 0).mpr
    (Metric.mem_closedBall_self zero_le_one)
  simpa [constructedA2CorrectedHexagonHomeomorph,
    constructedA2SquareToHexagonRadial] using h

public noncomputable def constructedA2CorrectedPositiveHexagonMap
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) (x : Fin 2 → ℝ) :
    constructedPositiveCentralFiber r := by
  classical
  exact if hx : constructedA2CorrectedHexagonHomeomorph v x ∈
      constructedA2CorrectedPlaneCell v then
    (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
      ⟨constructedA2CorrectedHexagonHomeomorph v x, hx⟩ :
        constructedPositiveCentralCell r v)
  else constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
      ⟨constructedA2CorrectedPlaneCenter v,
        constructedA2CorrectedHexagonCenter_mem v⟩

public theorem constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
    {r : ℝ} (hr : 0 < r) (v : ToricLattice) (x : Fin 2 → ℝ)
    (hx : x ∈ Metric.closedBall 0 1) :
    constructedA2CorrectedPositiveHexagonMap hr v x =
      (constructedA2CorrectedFiniteQuotientCellHomeomorph hr v
        ⟨constructedA2CorrectedHexagonHomeomorph v x,
          (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff v x).mpr hx⟩ :
            constructedPositiveCentralCell r v) := by
  classical
  rw [constructedA2CorrectedPositiveHexagonMap, dite_eq_left]











end SphereSixComplex.Geometry.InfiniteA2Toric

end
