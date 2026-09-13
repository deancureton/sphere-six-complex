module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.BoundaryPhaseCancellation
public import SphereSixComplex.Paper.Topology.StandardA2ToricBoundaryFaceCoverage
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveSingletonBall

@[expose] public section

noncomputable section
open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspToricPhaseAction

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem effectivePhase_fanShear_commute
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (p : constructedModel.Carrier) :
    Additive.toMul (constructedModel.fanShear lambda)
      (constructedModel.torusAction (compactTorusEmbedding (effectivePhaseSection k)) p) =
      constructedModel.torusAction (compactTorusEmbedding (effectivePhaseSection k))
        (Additive.toMul (constructedModel.fanShear lambda) p) := by
  rw [fanShear_torusAction]
  apply congrArg (fun g ↦ constructedModel.torusAction g
    (Additive.toMul (constructedModel.fanShear lambda) p))
  ext i
  fin_cases i <;>
    simp [denseTorusShear, compactTorusEmbedding, effectivePhaseSection]

public theorem positiveDeck_effectivePhase_commute
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (p : constructedModel.Carrier) :
    normalizedPositiveDeckCarrierMap N constructedModel lambda
      (constructedModel.torusAction (compactTorusEmbedding (effectivePhaseSection k)) p) =
      constructedModel.torusAction (compactTorusEmbedding (effectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda p) := by
  rw [normalizedPositiveDeckCarrierMap, effectivePhase_fanShear_commute,
    normalizedPositiveDeckCarrierMap]
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_comm, map_mul, Equiv.Perm.mul_apply]

public theorem frozenDeck_effectivePhase_formula
    (r : ℝ) (lambda : ParameterLattice) (k : Fin 2 → Circle)
    (p : localCarrier constructedModel r) :
    (frozenLocalPsiMap N constructedModel r lambda
      (compactPhaseLocalAction constructedModel r (effectivePhaseSection k) p) :
        constructedModel.Carrier) =
      constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * effectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda (p : constructedModel.Carrier)) := by
  rw [frozenLocalPsiMap_eq_compactPhase_positiveDeck]
  change constructedModel.torusAction _
    (normalizedPositiveDeckCarrierMap N constructedModel lambda
      (constructedModel.torusAction _ (p : constructedModel.Carrier))) = _
  rw [positiveDeck_effectivePhase_commute, map_mul, map_mul, Equiv.Perm.mul_apply]

public def boundaryZeroOneParameter : Fin 6 → ParameterLattice :=
  ![0, boundaryShearParameter 0, boundaryShearParameter 0,
    boundaryShearParameter 1, boundaryShearParameter 1, 0]

public def boundaryZeroZeroParameter : Fin 6 → ParameterLattice :=
  ![0, 0, boundaryShearParameter 0, boundaryShearParameter 0,
    boundaryShearParameter 1, boundaryShearParameter 1]

public theorem boundaryZeroOneParameter_chart (i : Fin 6) :
    translateChartIndex (boundaryZeroOneParameter i) (cellChart 0 i) =
      boundaryZeroOneTarget i := by
  have hzero : shearVector 0 = 0 := by simp [shearVector]
  fin_cases i <;>
    simp [translateChartIndex, boundaryZeroOneParameter,
      cellChart, boundaryZeroOneTarget,
      shearVector_boundaryShearParameter, hzero, boundaryDisplacement]

public theorem boundaryZeroZeroParameter_chart (i : Fin 6) :
    translateChartIndex (boundaryZeroZeroParameter i) (cellChart 0 i) =
      boundaryZeroZeroTarget i := by
  have hzero : shearVector 0 = 0 := by simp [shearVector]
  fin_cases i <;>
    simp [translateChartIndex, boundaryZeroZeroParameter,
      cellChart, boundaryZeroZeroTarget,
      shearVector_boundaryShearParameter, hzero, boundaryDisplacement,
      sub_eq_add_neg, add_comm]

public theorem positiveDeck_singleAxis (lambda : ParameterLattice)
    (a : ChartIndex) (j : Fin 3) (z : ℂ) :
    normalizedPositiveDeckCarrierMap N constructedModel lambda (inclusion a (singleAxis j z)) =
      inclusion (translateChartIndex lambda a) (singleAxis j
        (torusChartCoordinates (translateChartIndex lambda a)
          (normalizedCuspPositiveTwist N lambda) j * z)) := by
  change carrierTorusActionFun _ (carrierFanShearFun _ _) = _
  rw [carrierFanShearFun_inclusion, carrierTorusActionFun_inclusion]
  congr 1
  funext i
  by_cases hi : i = j <;> simp [singleAxis, hi]

public theorem cellLiftCoordinates_zero_one (i : Fin 6)
    (p : CellSquare) (hp : p.1 1 = 0) :
    cellLiftCoordinates i (fun j ↦ (p.1 j : ℂ)) =
      singleAxis (cellRemoveIndex i 0) (p.1 0 : ℂ) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [cellLiftCoordinates, cellRemoveIndex, singleAxis, hp]

public theorem cellLiftCoordinates_zero_zero (i : Fin 6)
    (p : CellSquare) (hp : p.1 0 = 0) :
    cellLiftCoordinates i (fun j ↦ (p.1 j : ℂ)) =
      singleAxis (cellRemoveIndex i 1) (p.1 1 : ℂ) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [cellLiftCoordinates, cellRemoveIndex, singleAxis, hp]

public theorem positiveDeck_square_zero_one (i : Fin 6)
    (p : CellSquare) (hp : p.1 1 = 0) :
    ∃ z : ℂ, normalizedPositiveDeckCarrierMap N constructedModel
        (boundaryZeroOneParameter i) (cellSquareCarrierPoint 0 i p) =
      inclusion (boundaryZeroOneTarget i)
        (singleAxis (cellRemoveIndex i 0) z) := by
  change ∃ z, normalizedPositiveDeckCarrierMap N constructedModel _
    (inclusion _ (cellLiftCoordinates i _)) = _
  rw [cellLiftCoordinates_zero_one i p hp,
    positiveDeck_singleAxis, boundaryZeroOneParameter_chart]
  exact ⟨_, rfl⟩

public theorem positiveDeck_square_zero_zero (i : Fin 6)
    (p : CellSquare) (hp : p.1 0 = 0) :
    ∃ z : ℂ, normalizedPositiveDeckCarrierMap N constructedModel
        (boundaryZeroZeroParameter i) (cellSquareCarrierPoint 0 i p) =
      inclusion (boundaryZeroZeroTarget i)
        (singleAxis (cellRemoveIndex i 1) z) := by
  change ∃ z, normalizedPositiveDeckCarrierMap N constructedModel _
    (inclusion _ (cellLiftCoordinates i _)) = _
  rw [cellLiftCoordinates_zero_zero i p hp,
    positiveDeck_singleAxis, boundaryZeroZeroParameter_chart]
  exact ⟨_, rfl⟩

public def actualBoundaryGauge (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  boundaryCompactGauge (frozenCompactPhase N (boundaryShearParameter 0))
    (frozenCompactPhase N (boundaryShearParameter 1)) x

public def boundaryCorrectedBallOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) : ActualLocalCuspCentralOrbitQuotient W :=
  effectivePhaseCentralOrbit W
    (actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 x.1))
    (closedBallPositiveCellHomeomorph W x).1

public theorem continuous_boundaryCorrectedBallOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (boundaryCorrectedBallOrbit W) := by
  have hg : Continuous (fun x : Metric.closedBall (0 : Fin 2 → ℝ) 1 ↦
      actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 x.1)) :=
    (continuous_boundaryCompactGauge _ _).comp
      ((correctedHexagonHomeomorph 0).continuous.comp continuous_subtype_val)
  let f : Metric.closedBall (0 : Fin 2 → ℝ) 1 →
      ClosedPhaseCell W.localWitness.radius := fun x ↦
    (closedBallPositiveCellHomeomorph W x,
      actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 x.1))
  have hf : Continuous f :=
    (closedBallPositiveCellHomeomorph W).continuous.prodMk hg
  have heq : boundaryCorrectedBallOrbit W = closedPhaseCellMap W ∘ f := rfl
  rw [heq]
  exact (continuous_closedPhaseCellMap W).comp hf

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
