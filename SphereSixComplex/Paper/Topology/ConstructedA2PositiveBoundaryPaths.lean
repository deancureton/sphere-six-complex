module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveCellBoundaryEdges
public import SphereSixComplex.Prerequisites.Topology.HexagonBoundaryPathHomology

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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
    LocalCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = p.1.1
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

public theorem constructedCentralEdgePaths_homotopic
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (i : Fin 3)
    {x y : ActualLocalCuspCentralOrbitQuotient W} (p q : Path x y)
    (hp : ∀ t, p t ∈ constructedCentralOneCell W i '' Metric.closedBall 0 1)
    (hq : ∀ t, q t ∈ constructedCentralOneCell W i '' Metric.closedBall 0 1) :
    p.Homotopic q := by
  let Z := Metric.closedBall (0 : Fin 1 → ℝ) 1
  let _ : ContractibleSpace Z :=
    (convex_closedBall (0 : Fin 1 → ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let f : Z → ActualLocalCuspCentralOrbitQuotient W := fun z ↦ constructedCentralOneCell W i z.1
  have hf : Continuous f := (constructedCentralOneCell_continuousOn W i).domRestrict
  apply SphereSixComplex.paths_homotopic_of_range_in_embedded_contractible f
    (hf.isClosedEmbedding (by
      intro x y h
      apply Subtype.ext
      fin_cases i
      · exact constructedCentralEdgeZeroOrbit_injOn_closedBall W x.2 y.2 h
      · exact constructedCentralEdgeOneOrbit_injOn_closedBall W x.2 y.2 h
      · exact constructedCentralEdgeTwoOrbit_injOn_closedBall W x.2 y.2 h)).isEmbedding p q
  · intro t
    obtain ⟨z, hz, he⟩ := hp t
    exact ⟨⟨z, hz⟩, he⟩
  · intro t
    obtain ⟨z, hz, he⟩ := hq t
    exact ⟨⟨z, hz⟩, he⟩

public theorem constructedA2ActualHexagonSidePath_opposite_homotopic
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] :
    (constructedA2ActualHexagonSidePath W 0).Homotopic
      (constructedA2ActualHexagonSidePath W 3).symm ∧
    (constructedA2ActualHexagonSidePath W 1).symm.Homotopic
      (constructedA2ActualHexagonSidePath W 4) ∧
    (constructedA2ActualHexagonSidePath W 2).Homotopic
      (constructedA2ActualHexagonSidePath W 5).symm := by
  refine ⟨?_, ?_, ?_⟩
  · apply constructedCentralEdgePaths_homotopic W 1
    · exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 0
    · intro t
      exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 3 (unitInterval.symm t)
  · apply constructedCentralEdgePaths_homotopic W 0
    · intro t
      exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 1 (unitInterval.symm t)
    · exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 4
  · apply constructedCentralEdgePaths_homotopic W 2
    · exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 2
    · intro t
      exact constructedA2CorrectedPlaneCellOrbit_side_mem_edge W 5 (unitInterval.symm t)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
