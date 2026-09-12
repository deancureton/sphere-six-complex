module
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.SingletonPhaseSurjectivity

@[expose] public section
noncomputable section
open Function Set Topology Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.CuspCombinatorics
namespace Construction


public theorem correctedPlaneTile_mem_open_of_nonzero
    (v : ToricLattice) (i : Fin 6) (p : CellSquare)
    (hp : ∀ j, p.1 j ≠ 0) :
    correctedPlaneTile v i p ∈ correctedOpenHexagon v := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  have hp0pos : 0 < p.1 0 := lt_of_le_of_ne hp0.1 (Ne.symm (hp 0))
  have hp0le : p.1 0 ≤ 1 := hp0.2
  have hp1le : p.1 1 ≤ 1 := hp1.2
  have hp1pos : 0 < p.1 1 := lt_of_le_of_ne hp1.1 (Ne.symm (hp 1))
  change hexagonGauge
    (correctedPlaneTile v i p - correctedPlaneCenter v) < 2 / 3
  rcases le_total (p.1 0) (p.1 1) with h | h
  · have heq : correctedPlaneTile v i p - correctedPlaneCenter v =
        (1 - p.1 1) • planeVertexOffset i +
          (p.1 1 - p.1 0) • planeMidpointOffset i := by
      rw [correctedPlaneTile, planeTile_of_le v i p h]
      abel
    rw [heq, hexagonGauge, max_lt_iff]
    constructor
    · apply (pi_norm_lt_iff (show (0 : ℝ) < 2 / 3 by norm_num)).mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        norm_num [planeVertexOffset, planeMidpointOffset,
          Real.norm_eq_abs, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;> (try constructor) <;> linarith
    · fin_cases i <;>
        norm_num [planeVertexOffset, planeMidpointOffset, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;>
        (try constructor) <;> linarith
  · have heq : correctedPlaneTile v i p - correctedPlaneCenter v =
        (1 - p.1 0) • planeVertexOffset i +
          (p.1 0 - p.1 1) • planeNextMidpointOffset i := by
      rw [correctedPlaneTile, planeTile_of_ge v i p h]
      abel
    rw [heq, hexagonGauge, max_lt_iff]
    constructor
    · apply (pi_norm_lt_iff (show (0 : ℝ) < 2 / 3 by norm_num)).mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        norm_num [planeVertexOffset, planeNextMidpointOffset,
          Real.norm_eq_abs, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;> (try constructor) <;> linarith
    · fin_cases i <;>
        norm_num [planeVertexOffset, planeNextMidpointOffset, abs_lt, abs_of_nonneg (sub_nonneg.mpr h)] <;>
        (try constructor) <;> linarith
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem finiteCell_support_singleton_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (z : correctedPlaneCell 0) :
    componentSupport constructedModel
        ((correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z).1.1.1.1 :
          Carrier) = {0} ↔
      z.1 ∈ correctedOpenHexagon 0 := by
  constructor
  · intro hz
    obtain ⟨⟨i, p⟩, rfl⟩ := surjective_correctedPlaneSquareProjection 0 z
    rw [correctedFiniteQuotientCellHomeomorph_apply] at hz
    exact correctedPlaneTile_mem_open_of_nonzero 0 i p
      (cellSquare_nonzero_of_singletonSupport 0 i p hz)
  · intro hz
    let x := (correctedHexagonHomeomorph 0).symm z.1
    have hx : x ∈ Metric.ball 0 1 :=
      (correctedHexagonHomeomorph_mem_open_iff 0 x).mp (by
        simpa [x] using hz)
    have heq := correctedPositiveHexagonMap_of_mem_closedBall
      W.localWitness.radius_pos 0 x (Metric.ball_subset_closedBall hx)
    have harg : (⟨correctedHexagonHomeomorph 0 x,
        (correctedHexagonHomeomorph_mem_closed_iff 0 x).mpr
          (Metric.ball_subset_closedBall hx)⟩ : correctedPlaneCell 0) = z := by
      apply Subtype.ext
      exact (correctedHexagonHomeomorph 0).apply_symm_apply z.1
    rw [harg] at heq
    have hs := correctedPositiveHexagonMap_componentSupport W 0 x hx
    rw [heq] at hs
    exact hs

public def closedBallPositiveCellHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.closedBall (0 : Fin 2 → ℝ) 1) ≃ₜ
      constructedPositiveCentralCell W.localWitness.radius 0 :=
  ((correctedHexagonHomeomorph 0).subtype
    (fun x ↦ (correctedHexagonHomeomorph_mem_closed_iff 0 x).symm)).trans
      (correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0)

public theorem closedBallPositiveCellHomeomorph_support_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) :
    componentSupport constructedModel
      ((closedBallPositiveCellHomeomorph W x).1.1.1.1 : Carrier) = {0} ↔
        x.1 ∈ Metric.ball 0 1 :=
  (finiteCell_support_singleton_iff W _).trans
    (correctedHexagonHomeomorph_mem_open_iff 0 x.1)

public def ballPositiveSingletonHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.ball (0 : Fin 2 → ℝ) 1) ≃ₜ
      positiveSingletonStratum W.localWitness.radius where
  toFun x := ⟨closedBallPositiveCellHomeomorph W
      ⟨x.1, Metric.ball_subset_closedBall x.property⟩,
    (closedBallPositiveCellHomeomorph_support_iff W _).mpr x.property⟩
  invFun q := ⟨(closedBallPositiveCellHomeomorph W).symm q.1,
    (closedBallPositiveCellHomeomorph_support_iff W _).mp (by
      rw [(closedBallPositiveCellHomeomorph W).apply_symm_apply]
      exact q.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun q : Metric.closedBall (0 : Fin 2 → ℝ) 1 ↦ q.1)
      ((closedBallPositiveCellHomeomorph W).symm_apply_apply
        ⟨x.1, Metric.ball_subset_closedBall x.property⟩)
  right_inv q := by
    apply Subtype.ext
    exact (closedBallPositiveCellHomeomorph W).apply_symm_apply q.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (closedBallPositiveCellHomeomorph W).continuous.comp
      (continuous_subtype_val.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      ((closedBallPositiveCellHomeomorph W).symm.continuous.comp continuous_subtype_val)

/-- The full geometric singleton-support stratum is an open two-ball times the compact
effective two-torus. -/
public def actualSingletonBallPhaseHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Metric.ball (0 : Fin 2 → ℝ) 1) × (Fin 2 → Circle) ≃ₜ
      actualSingletonStratum W :=
  ((ballPositiveSingletonHomeomorph W).prodCongr (Homeomorph.refl _)).trans
    (actualSingletonPhaseHomeomorph W)

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
end
