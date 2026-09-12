module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveBoundaryEdges
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
namespace Construction


public def boundaryFirstSquare (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    CellSquare :=
  ⟨![2 * (t : ℝ), 0], by
    intro j
    fin_cases j
    · change 0 ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1
      constructor <;> linarith [t.property.1]
    · norm_num⟩

public def boundarySecondSquare (t : unitInterval) (ht : 1 / 2 ≤ (t : ℝ)) :
    CellSquare :=
  ⟨![0, 2 * (1 - (t : ℝ))], by
    intro j
    fin_cases j
    · norm_num
    · change 0 ≤ 2 * (1 - (t : ℝ)) ∧ 2 * (1 - (t : ℝ)) ≤ 1
      constructor <;> linarith [t.property.2]⟩

public def hexagonSide (i : Fin 6) (t : unitInterval) :
    correctedPlaneCell 0 :=
  if ht : (t : ℝ) ≤ 1 / 2 then
    correctedPlaneSquareProjection 0 ⟨i, boundaryFirstSquare t ht⟩
  else
    correctedPlaneSquareProjection 0
      ⟨cellNextIndex i, boundarySecondSquare t (le_of_not_ge ht)⟩

public theorem hexagonSide_val (i : Fin 6) (t : unitInterval) :
    (hexagonSide i t).1 =
      (1 - (t : ℝ)) • planeVertexOffset i +
        (t : ℝ) • planeNextVertexOffset i := by
  unfold hexagonSide
  split_ifs with ht
  · change correctedPlaneTile 0 i _ = _
    rw [correctedPlaneTile_zero_one i _ (by rfl)]
    simp only [boundaryFirstSquare, Matrix.cons_val_zero]
    congr 2 <;> ring
  · change correctedPlaneTile 0 (cellNextIndex i) _ = _
    rw [correctedPlaneTile_zero_zero _ _ (by rfl)]
    have hi : cellPreviousIndex (cellNextIndex i) = i := by
      fin_cases i <;> rfl
    simp only [hi, boundarySecondSquare, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    congr 2 <;> ring

public theorem continuous_hexagonSide (i : Fin 6) :
    Continuous (hexagonSide i) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : unitInterval ↦ (hexagonSide i t).1)
  simp_rw [hexagonSide_val]
  exact (continuous_const.sub continuous_subtype_val).smul continuous_const |>.add
    (continuous_subtype_val.smul continuous_const)

public def correctedPlaneCellOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (z : correctedPlaneCell 0) : ActualLocalCuspCentralOrbitQuotient W :=
  effectivePhaseCentralOrbit W (actualBoundaryGauge (N := N) z.1)
    (correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z).1

public theorem continuous_correctedPlaneCellOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (correctedPlaneCellOrbit W) := by
  let f : correctedPlaneCell 0 →
      ClosedPhaseCell W.localWitness.radius := fun z ↦
    (correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z,
      actualBoundaryGauge (N := N) z.1)
  have hg : Continuous (fun z : correctedPlaneCell 0 ↦
      actualBoundaryGauge (N := N) z.1) :=
    (continuous_boundaryCompactGauge _ _).comp continuous_subtype_val
  have hf : Continuous f :=
    (correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0).continuous.prodMk hg
  have he : correctedPlaneCellOrbit W = closedPhaseCellMap W ∘ f := rfl
  rw [he]
  exact (continuous_closedPhaseCellMap W).comp hf

public theorem correctedPlaneCellOrbit_square
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) :
    correctedPlaneCellOrbit W (correctedPlaneSquareProjection 0 ⟨i, p⟩) =
      effectivePhaseCentralOrbit W
        (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
        (cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 := by
  simp only [correctedPlaneCellOrbit,
    correctedFiniteQuotientCellHomeomorph_apply]
  rfl

public theorem correctedPlaneCellOrbit_side_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (t : unitInterval) :
    correctedPlaneCellOrbit W (hexagonSide i t) ∈
      constructedCentralOneCell W (boundaryZeroOneEdge i) '' Metric.closedBall 0 1 := by
  unfold hexagonSide
  split_ifs
  · rw [correctedPlaneCellOrbit_square]
    exact actualBoundaryGauge_square_zero_one_mem_edge W i _ rfl
  · rw [correctedPlaneCellOrbit_square]
    have hi : boundaryZeroZeroEdge (cellNextIndex i) =
        boundaryZeroOneEdge i := by fin_cases i <;> rfl
    rw [← hi]
    exact actualBoundaryGauge_square_zero_zero_mem_edge W _ _ rfl

public theorem centralOriginOrbit_eq_of_carrier
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

public def boundaryZeroSquare : CellSquare :=
  ⟨0, by intro j; norm_num⟩

public theorem effectivePhaseCentralOrbit_square_origin
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) (k : Fin 2 → Circle) :
    effectivePhaseCentralOrbit W k
      (cellSquareProjection W.localWitness.radius_pos 0
        ⟨i, boundaryZeroSquare⟩).1 =
      constructedCentralOriginOrbit W (cellChart 0 i).1 := by
  apply centralOriginOrbit_eq_of_carrier W _ (cellChart 0 i)
  change carrierTorusActionFun _ (inclusion _ (cellLiftCoordinates i _)) = _
  have hz : cellLiftCoordinates i
      (fun j ↦ ((boundaryZeroSquare.1 j : ℝ) : ℂ)) = 0 := by
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [cellLiftCoordinates, boundaryZeroSquare]
  rw [hz, carrierTorusActionFun_inclusion]
  simp

public theorem correctedPlaneCellOrbit_side_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    correctedPlaneCellOrbit W (hexagonSide i 0) =
      constructedCentralOriginOrbit W (cellChart 0 i).1 := by
  have hzero : hexagonSide i 0 =
      correctedPlaneSquareProjection 0 ⟨i, boundaryZeroSquare⟩ := by
    unfold hexagonSide
    rw [dite_eq_left (by norm_num)]
    congr 2
    apply Subtype.ext
    ext j
    fin_cases j <;> norm_num [boundaryFirstSquare, boundaryZeroSquare]
  rw [hzero, correctedPlaneCellOrbit_square]
  exact effectivePhaseCentralOrbit_square_origin W i _

public theorem correctedPlaneCellOrbit_side_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    correctedPlaneCellOrbit W (hexagonSide i 1) =
      constructedCentralOriginOrbit W (cellChart 0 (cellNextIndex i)).1 := by
  have hone : hexagonSide i 1 =
      correctedPlaneSquareProjection 0
        ⟨cellNextIndex i, boundaryZeroSquare⟩ := by
    unfold hexagonSide
    rw [dite_eq_right (by norm_num)]
    congr 2
    apply Subtype.ext
    ext j
    fin_cases j <;> norm_num [boundarySecondSquare, boundaryZeroSquare]
  rw [hone, correctedPlaneCellOrbit_square]
  exact effectivePhaseCentralOrbit_square_origin W _ _

public def actualHexagonSidePath
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 6) :
    Path (constructedCentralOriginOrbit W (cellChart 0 i).1)
      (constructedCentralOriginOrbit W
        (cellChart 0 (cellNextIndex i)).1) where
  toFun t := correctedPlaneCellOrbit W (hexagonSide i t)
  continuous_toFun := (continuous_correctedPlaneCellOrbit W).comp
    (continuous_hexagonSide i)
  source' := correctedPlaneCellOrbit_side_zero W i
  target' := correctedPlaneCellOrbit_side_one W i



end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
