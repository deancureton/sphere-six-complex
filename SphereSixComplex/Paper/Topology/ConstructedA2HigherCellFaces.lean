module

public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2CorrectedPhaseOrbit_append
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (b : Fin 2 → ℝ) (p : Fin n → ℝ) :
    constructedA2CorrectedPhaseOrbit W n phase (Fin.append b p) =
      constructedA2EffectivePhaseCentralOrbit W
        (constructedA2ActualBoundaryGauge (N := N)
          (constructedA2CorrectedHexagonHomeomorph 0 b) * phase p)
        (constructedA2CorrectedPositiveHexagonMap W.localWitness.radius_pos 0 b) := by
  simp [constructedA2CorrectedPhaseOrbit, Fin.appendHomeomorph]











end SphereSixComplex.Geometry.InfiniteA2Toric
