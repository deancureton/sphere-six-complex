module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveCellBoundaryEdges
public import SphereSixComplex.Prerequisites.Topology.HexagonBoundaryPathHomology

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedA2BoundaryFirstSquare (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    ConstructedA2CellSquare :=
  ⟨![2 * (t : ℝ), 0], by
    intro j
    fin_cases j
    · change 0 ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1
      constructor <;> linarith [t.property.1]
    · norm_num⟩

public def constructedA2BoundarySecondSquare (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    ConstructedA2CellSquare :=
  ⟨![0, 2 * (1 - (t : ℝ))], by
    intro j
    fin_cases j
    · norm_num
    · change 0 ≤ 2 * (1 - (t : ℝ)) ∧ 2 * (1 - (t : ℝ)) ≤ 1
      constructor <;> linarith [t.property.2]⟩

public def constructedA2HexagonSide (i : Fin 6) (t : unitInterval) :
    constructedA2CorrectedPlaneCell 0 :=
  if ht : (t : ℝ) ≤ 1 / 2 then
    constructedA2CorrectedPlaneSquareProjection 0 ⟨i, constructedA2BoundaryFirstSquare t ht⟩
  else
    constructedA2CorrectedPlaneSquareProjection 0
      ⟨constructedA2CellNextIndex i, constructedA2BoundarySecondSquare t (le_of_not_ge ht)⟩

public theorem constructedA2HexagonSide_val (i : Fin 6) (t : unitInterval) :
    (constructedA2HexagonSide i t).1 =
      (1 - (t : ℝ)) • constructedA2PlaneVertexOffset i +
        (t : ℝ) • constructedA2PlaneNextVertexOffset i := by
  unfold constructedA2HexagonSide
  split_ifs with ht
  · change constructedA2CorrectedPlaneTile 0 i _ = _
    rw [constructedA2CorrectedPlaneTile_zero_one i _ (by rfl)]
    simp only [constructedA2BoundaryFirstSquare, Matrix.cons_val_zero]
    congr 2 <;> ring
  · change constructedA2CorrectedPlaneTile 0 (constructedA2CellNextIndex i) _ = _
    rw [constructedA2CorrectedPlaneTile_zero_zero _ _ (by rfl)]
    have hi : constructedA2CellPreviousIndex (constructedA2CellNextIndex i) = i := by
      fin_cases i <;> rfl
    simp only [hi, constructedA2BoundarySecondSquare, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    congr 2 <;> ring

public theorem constructedA2HexagonSide_continuous (i : Fin 6) :
    Continuous (constructedA2HexagonSide i) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : unitInterval ↦ (constructedA2HexagonSide i t).1)
  simp_rw [constructedA2HexagonSide_val]
  exact (continuous_const.sub continuous_subtype_val).smul continuous_const |>.add
    (continuous_subtype_val.smul continuous_const)

public def constructedA2CorrectedPlaneCellOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (z : constructedA2CorrectedPlaneCell 0) : ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2EffectivePhaseCentralOrbit W (constructedA2ActualBoundaryGauge (N := N) z.1)
    (constructedA2CorrectedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z).1

public theorem constructedA2CorrectedPlaneCellOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedA2CorrectedPlaneCellOrbit W) := by
  let f : constructedA2CorrectedPlaneCell 0 →
      ConstructedA2ClosedPhaseCell W.localWitness.radius := fun z ↦
    (constructedA2CorrectedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z,
      constructedA2ActualBoundaryGauge (N := N) z.1)
  have hg : Continuous (fun z : constructedA2CorrectedPlaneCell 0 ↦
      constructedA2ActualBoundaryGauge (N := N) z.1) :=
    (constructedA2BoundaryCompactGauge_continuous _ _).comp continuous_subtype_val
  have hf : Continuous f :=
    (constructedA2CorrectedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0).continuous.prodMk hg
  have he : constructedA2CorrectedPlaneCellOrbit W = constructedA2ClosedPhaseCellMap W ∘ f := rfl
  rw [he]
  exact (constructedA2ClosedPhaseCellMap_continuous W).comp hf

public theorem constructedA2CorrectedPlaneCellOrbit_square
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : ConstructedA2CellSquare) :
    constructedA2CorrectedPlaneCellOrbit W (constructedA2CorrectedPlaneSquareProjection 0 ⟨i, p⟩) =
      constructedA2EffectivePhaseCentralOrbit W
        (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))
        (constructedA2CellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 := by
  simp only [constructedA2CorrectedPlaneCellOrbit,
    constructedA2CorrectedFiniteQuotientCellHomeomorph_apply]
  rfl

public theorem constructedA2CorrectedPlaneCellOrbit_side_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    constructedA2CorrectedPlaneCellOrbit W (constructedA2HexagonSide i t) ∈
      constructedCentralOneCell W (constructedA2BoundaryZeroOneEdge i) '' Metric.closedBall 0 1 := by
  unfold constructedA2HexagonSide
  split_ifs
  · rw [constructedA2CorrectedPlaneCellOrbit_square]
    exact constructedA2ActualBoundaryGauge_square_zero_one_mem_edge W i _ rfl
  · rw [constructedA2CorrectedPlaneCellOrbit_square]
    have hi : constructedA2BoundaryZeroZeroEdge (constructedA2CellNextIndex i) =
        constructedA2BoundaryZeroOneEdge i := by fin_cases i <;> rfl
    rw [← hi]
    exact constructedA2ActualBoundaryGauge_square_zero_zero_mem_edge W _ _ rfl

public theorem constructedCentralOriginOrbit_eq_of_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W) (a : ChartIndex)
    (hp : (p.1.1 : constructedModel.Carrier) = inclusion a 0) :
    Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p = constructedCentralOriginOrbit W a.1 := by
  let _ := actualLocalCuspQuotientAction W
  obtain ⟨lambda, hlambda⟩ := shearVector_surjective a.2
  apply Quotient.sound
  change MulAction.orbitRel (Multiplicative ParameterLattice)
    (actualLocalCuspCentralSubMulAction W) p (constructedCentralOriginPoint W a.1)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨Multiplicative.ofAdd lambda, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((Multiplicative.ofAdd lambda • constructedCentralOrigin W a.1 :
    localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = p.1.1
  rw [constructedCentralOrigin_smul_coe, hp]
  simp [translateChartIndex, hlambda]
  rfl

public def constructedA2BoundaryZeroSquare : ConstructedA2CellSquare :=
  ⟨0, by intro j; norm_num⟩

public theorem constructedA2EffectivePhaseCentralOrbit_square_origin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (k : Fin 2 → Circle) :
    constructedA2EffectivePhaseCentralOrbit W k
      (constructedA2CellSquareProjection W.localWitness.radius_pos 0
        ⟨i, constructedA2BoundaryZeroSquare⟩).1 =
      constructedCentralOriginOrbit W (constructedA2CellChart 0 i).1 := by
  apply constructedCentralOriginOrbit_eq_of_carrier W _ (constructedA2CellChart 0 i)
  change carrierTorusActionFun _ (inclusion _ (constructedA2CellLiftCoordinates i _)) = _
  have hz : constructedA2CellLiftCoordinates i
      (fun j ↦ ((constructedA2BoundaryZeroSquare.1 j : ℝ) : ℂ)) = 0 := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [constructedA2CellLiftCoordinates, constructedA2BoundaryZeroSquare]
  rw [hz, carrierTorusActionFun_inclusion]
  simp

public theorem constructedA2CorrectedPlaneCellOrbit_side_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    constructedA2CorrectedPlaneCellOrbit W (constructedA2HexagonSide i 0) =
      constructedCentralOriginOrbit W (constructedA2CellChart 0 i).1 := by
  have hzero : constructedA2HexagonSide i 0 =
      constructedA2CorrectedPlaneSquareProjection 0 ⟨i, constructedA2BoundaryZeroSquare⟩ := by
    unfold constructedA2HexagonSide
    rw [dite_eq_left (by norm_num)]
    congr 2
    apply Subtype.ext
    ext j
    fin_cases j <;> norm_num [constructedA2BoundaryFirstSquare, constructedA2BoundaryZeroSquare]
  rw [hzero, constructedA2CorrectedPlaneCellOrbit_square]
  exact constructedA2EffectivePhaseCentralOrbit_square_origin W i _

public theorem constructedA2CorrectedPlaneCellOrbit_side_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    constructedA2CorrectedPlaneCellOrbit W (constructedA2HexagonSide i 1) =
      constructedCentralOriginOrbit W (constructedA2CellChart 0 (constructedA2CellNextIndex i)).1 := by
  have hone : constructedA2HexagonSide i 1 =
      constructedA2CorrectedPlaneSquareProjection 0
        ⟨constructedA2CellNextIndex i, constructedA2BoundaryZeroSquare⟩ := by
    unfold constructedA2HexagonSide
    rw [dite_eq_right (by norm_num)]
    congr 2
    apply Subtype.ext
    ext j
    fin_cases j <;> norm_num [constructedA2BoundarySecondSquare, constructedA2BoundaryZeroSquare]
  rw [hone, constructedA2CorrectedPlaneCellOrbit_square]
  exact constructedA2EffectivePhaseCentralOrbit_square_origin W _ _

public def constructedA2ActualHexagonSidePath
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    Path (constructedCentralOriginOrbit W (constructedA2CellChart 0 i).1)
      (constructedCentralOriginOrbit W
        (constructedA2CellChart 0 (constructedA2CellNextIndex i)).1) where
  toFun t := constructedA2CorrectedPlaneCellOrbit W (constructedA2HexagonSide i t)
  continuous_toFun := (constructedA2CorrectedPlaneCellOrbit_continuous W).comp
    (constructedA2HexagonSide_continuous i)
  source' := constructedA2CorrectedPlaneCellOrbit_side_zero W i
  target' := constructedA2CorrectedPlaneCellOrbit_side_one W i



end SphereSixComplex.Geometry.InfiniteA2Toric
