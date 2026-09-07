module
public import SphereSixComplex.Topology.ConstructedA2SingletonPhaseSurjectivity

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Geometry.CuspCombinatorics

public theorem constructedA2CorrectedPlaneTile_mem_open_of_nonzero
    (v : ToricLattice) (i : Fin 6) (p : ConstructedA2CellSquare)
    (hp : ∀ j, p.1 j ≠ 0) :
    constructedA2CorrectedPlaneTile v i p ∈ constructedA2CorrectedOpenHexagon v := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hp0pos : 0 < p.1 0 := lt_of_le_of_ne hp0.1 (Ne.symm (hp 0))
  have hp0le : p.1 0 ≤ 1 := hp0.2
  have hp1le : p.1 1 ≤ 1 := hp1.2
  have hp1pos : 0 < p.1 1 := lt_of_le_of_ne hp1.1 (Ne.symm (hp 1))
  change constructedA2HexagonGauge
    (constructedA2CorrectedPlaneTile v i p - constructedA2CorrectedPlaneCenter v) < 2 / 3
  rcases le_total (p.1 0) (p.1 1) with h | h
  · have heq : constructedA2CorrectedPlaneTile v i p - constructedA2CorrectedPlaneCenter v =
        (1 - p.1 1) • constructedA2PlaneVertexOffset i +
          (p.1 1 - p.1 0) • constructedA2PlaneMidpointOffset i := by
      rw [constructedA2CorrectedPlaneTile, constructedA2PlaneTile_of_le v i p h]
      abel
    rw [heq, constructedA2HexagonGauge, max_lt_iff]
    constructor
    · apply (pi_norm_lt_iff (show (0 : ℝ) < 2 / 3 by norm_num)).mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        norm_num [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset,
          Real.norm_eq_abs, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;> (try constructor) <;> linarith
    · fin_cases i <;>
        norm_num [constructedA2PlaneVertexOffset, constructedA2PlaneMidpointOffset, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;>
        (try constructor) <;> linarith
  · have heq : constructedA2CorrectedPlaneTile v i p - constructedA2CorrectedPlaneCenter v =
        (1 - p.1 0) • constructedA2PlaneVertexOffset i +
          (p.1 0 - p.1 1) • constructedA2PlaneNextMidpointOffset i := by
      rw [constructedA2CorrectedPlaneTile, constructedA2PlaneTile_of_ge v i p h]
      abel
    rw [heq, constructedA2HexagonGauge, max_lt_iff]
    constructor
    · apply (pi_norm_lt_iff (show (0 : ℝ) < 2 / 3 by norm_num)).mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        norm_num [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset,
          Real.norm_eq_abs, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;> (try constructor) <;> linarith
    · fin_cases i <;>
        norm_num [constructedA2PlaneVertexOffset, constructedA2PlaneNextMidpointOffset, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;>
        (try constructor) <;> linarith
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2FiniteCell_support_singleton_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (z : constructedA2CorrectedPlaneCell 0) :
    componentSupport constructedModel
        ((constructedA2CorrectedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z).1.1.1.1 :
          Carrier) = {0} ↔
      z.1 ∈ constructedA2CorrectedOpenHexagon 0 := by
  constructor
  · intro hz
    obtain ⟨⟨i, p⟩, rfl⟩ := constructedA2CorrectedPlaneSquareProjection_surjective 0 z
    rw [constructedA2CorrectedFiniteQuotientCellHomeomorph_apply] at hz
    exact constructedA2CorrectedPlaneTile_mem_open_of_nonzero 0 i p
      (constructedA2CellSquare_nonzero_of_singletonSupport 0 i p hz)
  · intro hz
    let x := (constructedA2CorrectedHexagonHomeomorph 0).symm z.1
    have hx : x ∈ Metric.ball 0 1 :=
      (constructedA2CorrectedHexagonHomeomorph_mem_open_iff 0 x).mp (by
        simpa [x] using hz)
    have heq := constructedA2CorrectedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos 0 x (Metric.ball_subset_closedBall hx)
    have harg : (⟨constructedA2CorrectedHexagonHomeomorph 0 x,
        (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff 0 x).mpr
          (Metric.ball_subset_closedBall hx)⟩ : constructedA2CorrectedPlaneCell 0) = z := by
      apply Subtype.ext
      exact (constructedA2CorrectedHexagonHomeomorph 0).apply_symm_apply z.1
    rw [harg] at heq
    have hs := constructedA2CorrectedPositiveHexagonMap_componentSupport W 0 x hx
    rw [heq] at hs
    exact hs

public def constructedA2ClosedBallPositiveCellHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.closedBall (0 : Fin 2 → ℝ) 1) ≃ₜ
      constructedPositiveCentralCell W.localWitness.radius 0 :=
  ((constructedA2CorrectedHexagonHomeomorph 0).subtype
    (fun x ↦ (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff 0 x).symm)).trans
      (constructedA2CorrectedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0)

public theorem constructedA2ClosedBallPositiveCellHomeomorph_support_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) :
    componentSupport constructedModel
      ((constructedA2ClosedBallPositiveCellHomeomorph W x).1.1.1.1 : Carrier) = {0} ↔
        x.1 ∈ Metric.ball 0 1 :=
  (constructedA2FiniteCell_support_singleton_iff W _).trans
    (constructedA2CorrectedHexagonHomeomorph_mem_open_iff 0 x.1)

public def constructedA2BallPositiveSingletonHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.ball (0 : Fin 2 → ℝ) 1) ≃ₜ
      constructedA2PositiveSingletonStratum W.localWitness.radius where
  toFun x := ⟨constructedA2ClosedBallPositiveCellHomeomorph W
      ⟨x.1, Metric.ball_subset_closedBall x.property⟩,
    (constructedA2ClosedBallPositiveCellHomeomorph_support_iff W _).mpr x.property⟩
  invFun q := ⟨(constructedA2ClosedBallPositiveCellHomeomorph W).symm q.1,
    (constructedA2ClosedBallPositiveCellHomeomorph_support_iff W _).mp (by
      rw [(constructedA2ClosedBallPositiveCellHomeomorph W).apply_symm_apply]
      exact q.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun q : Metric.closedBall (0 : Fin 2 → ℝ) 1 ↦ q.1)
      ((constructedA2ClosedBallPositiveCellHomeomorph W).symm_apply_apply
        ⟨x.1, Metric.ball_subset_closedBall x.property⟩)
  right_inv q := by
    apply Subtype.ext
    exact (constructedA2ClosedBallPositiveCellHomeomorph W).apply_symm_apply q.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (constructedA2ClosedBallPositiveCellHomeomorph W).continuous.comp
      (continuous_subtype_val.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((constructedA2ClosedBallPositiveCellHomeomorph W).symm.continuous.comp continuous_subtype_val)

/-- The full geometric singleton-support stratum is an open two-ball times the compact
effective two-torus. -/
public def constructedA2ActualSingletonBallPhaseHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) ≃ₜ
      constructedA2ActualSingletonStratum W :=
  ((constructedA2BallPositiveSingletonHomeomorph W).prodCongr (Homeomorph.refl _)).trans
    (constructedA2ActualSingletonPhaseHomeomorph W)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
end
