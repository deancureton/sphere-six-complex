module

public import SphereSixComplex.Topology.ConstructedA2CellAtlas

@[expose] public section
noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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

public theorem constructedA2CorrectedThreeOrbit_phase_face
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 2) (b : Fin 2 → ℝ) (s : ℝ) (hs : |s| = 1) :
    constructedA2CorrectedThreeOrbit W i (Fin.append b ![s]) =
      constructedA2CorrectedPositiveTwoOrbit W b := by
  unfold constructedA2CorrectedThreeOrbit
  rw [constructedA2CorrectedPhaseOrbit_append]
  have hp : constructedA2CircleOnePhase i ![s] = 1 := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [constructedA2CircleOnePhase, constructedCircleBallCell,
        constructedCircleCell_eq_one_of_abs_eq hs]
  rw [hp, mul_one]
  rfl

public theorem constructedA2CorrectedFourOrbit_phase_face_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (s t : ℝ) (hs : |s| = 1) :
    constructedA2CorrectedFourOrbit W (Fin.append b ![s, t]) =
      constructedA2CorrectedThreeOrbit W 1 (Fin.append b ![t]) := by
  unfold constructedA2CorrectedFourOrbit constructedA2CorrectedThreeOrbit
  rw [constructedA2CorrectedPhaseOrbit_append, constructedA2CorrectedPhaseOrbit_append]
  congr 2
  ext j
  fin_cases j <;> simp [constructedA2CircleTwoPhase, constructedA2CircleOnePhase,
    constructedCircleBallCell, constructedCircleCell_eq_one_of_abs_eq hs]

public theorem constructedA2CorrectedFourOrbit_phase_face_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (s t : ℝ) (hs : |s| = 1) :
    constructedA2CorrectedFourOrbit W (Fin.append b ![t, s]) =
      constructedA2CorrectedThreeOrbit W 0 (Fin.append b ![t]) := by
  unfold constructedA2CorrectedFourOrbit constructedA2CorrectedThreeOrbit
  rw [constructedA2CorrectedPhaseOrbit_append, constructedA2CorrectedPhaseOrbit_append]
  congr 2
  ext j
  fin_cases j <;> simp [constructedA2CircleTwoPhase, constructedA2CircleOnePhase,
    constructedCircleBallCell, constructedCircleCell_eq_one_of_abs_eq hs]

public theorem constructedCentralThreeCell_phase_face
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 2) (b : Fin 2 → ℝ) (s : ℝ) (hs : |s| = 1) :
    constructedCentralCellMap W 3 i (Fin.append b ![s]) =
      constructedCentralCellMap W 2 (0 : Fin 4) b :=
  constructedA2CorrectedThreeOrbit_phase_face W i b s hs

public theorem constructedCentralFourCell_phase_face_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (s t : ℝ) (hs : |s| = 1) :
    constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b ![s, t]) =
      constructedCentralCellMap W 3 (1 : Fin 2) (Fin.append b ![t]) :=
  constructedA2CorrectedFourOrbit_phase_face_zero W b s t hs

public theorem constructedCentralFourCell_phase_face_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (s t : ℝ) (hs : |s| = 1) :
    constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b ![t, s]) =
      constructedCentralCellMap W 3 (0 : Fin 2) (Fin.append b ![t]) :=
  constructedA2CorrectedFourOrbit_phase_face_one W b s t hs

public theorem constructedCentralFourCell_base_face
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (hb : b ∈ Metric.sphere 0 1) (p : Fin 2 → ℝ) :
    constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b p) ∈
      constructedCentralBoundaryTwoSkeleton W := by
  apply constructedA2CorrectedPhaseOrbit_base_boundary W 2 constructedA2CircleTwoPhase
  change ((Fin.appendHomeomorph (X := ℝ) 2 2).symm
    ((Fin.appendHomeomorph (X := ℝ) 2 2) (b, p))).1 ∈ Metric.sphere 0 1
  simpa only [Homeomorph.symm_apply_apply] using hb

public theorem constructedCentralThreeCell_opposite_phase_faces
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 2) (b : Fin 2 → ℝ) :
    constructedCentralCellMap W 3 i (Fin.append b ![-1]) =
      constructedCentralCellMap W 3 i (Fin.append b ![1]) :=
  (constructedCentralThreeCell_phase_face W i b (-1) (by norm_num)).trans
    (constructedCentralThreeCell_phase_face W i b 1 (by norm_num)).symm

public theorem constructedCentralFourCell_opposite_phase_faces_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (t : ℝ) :
    constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b ![-1, t]) =
      constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b ![1, t]) :=
  (constructedCentralFourCell_phase_face_zero W b (-1) t (by norm_num)).trans
    (constructedCentralFourCell_phase_face_zero W b 1 t (by norm_num)).symm

public theorem constructedCentralFourCell_opposite_phase_faces_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (b : Fin 2 → ℝ) (t : ℝ) :
    constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b ![t, -1]) =
      constructedCentralCellMap W 4 (0 : Fin 1) (Fin.append b ![t, 1]) :=
  (constructedCentralFourCell_phase_face_one W b (-1) t (by norm_num)).trans
    (constructedCentralFourCell_phase_face_one W b 1 t (by norm_num)).symm

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
