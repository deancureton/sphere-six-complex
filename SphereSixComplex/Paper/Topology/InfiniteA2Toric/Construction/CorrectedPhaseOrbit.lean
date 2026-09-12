module

public import SphereSixComplex.Paper.Topology.ConstructedA2CellAtlas

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem correctedPhaseOrbit_append
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (phase : (Fin n → ℝ) → Fin 2 → Circle)
    (b : Fin 2 → ℝ) (p : Fin n → ℝ) :
    correctedPhaseOrbit W n phase (Fin.append b p) =
      effectivePhaseCentralOrbit W
        (actualBoundaryGauge (N := N)
          (correctedHexagonHomeomorph 0 b) * phase p)
        (correctedPositiveHexagonMap W.localWitness.radius_pos 0 b) := by
  simp [correctedPhaseOrbit, Fin.appendHomeomorph]











end SphereSixComplex.Geometry.InfiniteA2Toric.Construction
