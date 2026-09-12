module
public import SphereSixComplex.Paper.Topology.CuspFillingPhaseCircle
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralCompactAction

@[expose] public section
noncomputable section
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods InfiniteA2Toric
open InfiniteA2Toric.Construction InfiniteA2Toric
open CuspCombinatorics CuspPeriodExpansion CuspLocalPhaseAction CuspFilling
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def cuspPeriodCompactCircle (i : Fin 2) (z : UnitAddCircle) : Fin 2 → Circle :=
  fun j ↦ if j = i then AddCircle.toCircle z else 1

public theorem cuspFillingPeriodCircle_centralOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2)
    (z : UnitAddCircle) (q : ActualLocalCuspCentralOrbitQuotient W) :
    cuspFillingPeriodCircle W i (z,actualLocalCuspCentralOrbitMap W q) =
      actualLocalCuspCentralOrbitMap W
        (centralCompactOrbitMap W (cuspPeriodCompactCircle i z) q) := by
  let _ := actualLocalCuspQuotientAction W
  induction q using Quotient.inductionOn with
  | _ p =>
    change Quotient.mk _ (localCuspPeriodCircle W i (z,p.1)) =
      Quotient.mk _ (centralCompactMap W (cuspPeriodCompactCircle i z) p).1
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change constructedModel.torusAction _ p.1.1 = constructedModel.torusAction _ p.1.1
    apply congrArg (fun g : DenseTorus ↦ constructedModel.torusAction g p.1.1)
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [CuspToricPhaseAction.phaseEmbedding, cuspPeriodPhaseCircle,
        cuspPeriodCompactCircle, effectivePhaseSection,
        compactTorusEmbedding, CircleExponential.toUnits]

public theorem lowerChart_phase_weights (c : CuspToricPhaseAction.Phase) :
    torusChartCoordinates (false,0) (CuspToricPhaseAction.phaseEmbedding c) =
      ![((c 0 : ℂ)⁻¹ * (c 1 : ℂ)⁻¹), (c 0 : ℂ), (c 1 : ℂ)] := by
  ext j
  fin_cases j <;>
    simp [torusChartCoordinates, monomial, dualMatrix, a2DualCharacter, denseRawCoordinates,
      CuspToricPhaseAction.phaseEmbedding, Fin.prod_univ_succ]

public theorem lowerAxis_phase_action (c : CuspToricPhaseAction.Phase)
    (j : Fin 3) (w : ℂ) :
    constructedModel.torusAction (CuspToricPhaseAction.phaseEmbedding c)
      (inclusion (false,0) (singleAxis j w)) =
      inclusion (false,0) (singleAxis j
        (![ ((c 0 : ℂ)⁻¹ * (c 1 : ℂ)⁻¹), (c 0 : ℂ), (c 1 : ℂ)] j * w)) := by
  change carrierTorusActionFun _ _ = _
  rw [carrierTorusActionFun_inclusion, lowerChart_phase_weights]
  apply congrArg (inclusion (false,0))
  ext k
  by_cases h : k = j
  · subst k
    simp [singleAxis]
  · simp [singleAxis, h]

public theorem upperChart_phase_weights (c : CuspToricPhaseAction.Phase) (v : ToricLattice) :
    torusChartCoordinates (true,v) (CuspToricPhaseAction.phaseEmbedding c) =
      ![(c 1 : ℂ)⁻¹, (c 0 : ℂ)⁻¹, (c 0 : ℂ) * (c 1 : ℂ)] := by
  ext j
  fin_cases j <;>
    simp [torusChartCoordinates, monomial, dualMatrix, a2DualCharacter, denseRawCoordinates,
      CuspToricPhaseAction.phaseEmbedding, Fin.prod_univ_succ]

public theorem upperAxis_phase_action (c : CuspToricPhaseAction.Phase)
    (v : ToricLattice) (j : Fin 3) (w : ℂ) :
    constructedModel.torusAction (CuspToricPhaseAction.phaseEmbedding c)
      (inclusion (true,v) (singleAxis j w)) =
      inclusion (true,v) (singleAxis j
        (![(c 1 : ℂ)⁻¹, (c 0 : ℂ)⁻¹, (c 0 : ℂ) * (c 1 : ℂ)] j * w)) := by
  change carrierTorusActionFun _ _ = _
  rw [carrierTorusActionFun_inclusion, upperChart_phase_weights]
  apply congrArg (inclusion (true,v))
  ext k
  by_cases h : k = j
  · subst k
    simp [singleAxis]
  · simp [singleAxis, h]

public theorem fourthPhase_edgeOne_fixed (z : UnitAddCircle) (x : Fin 1 → ℝ) :
    constructedModel.torusAction (CuspToricPhaseAction.phaseEmbedding (cuspPeriodPhaseCircle 1 z))
      (constructedCentralEdgeOneCarrier x) = constructedCentralEdgeOneCarrier x := by
  unfold constructedCentralEdgeOneCarrier
  split_ifs
  · rw [lowerAxis_phase_action]
    simp [cuspPeriodPhaseCircle] <;> rfl
  · rw [upperAxis_phase_action]
    simp [cuspPeriodPhaseCircle] <;> rfl

public theorem thirdPhase_edgeTwo_fixed (z : UnitAddCircle) (x : Fin 1 → ℝ) :
    constructedModel.torusAction (CuspToricPhaseAction.phaseEmbedding (cuspPeriodPhaseCircle 0 z))
      (constructedCentralEdgeTwoCarrier x) = constructedCentralEdgeTwoCarrier x := by
  unfold constructedCentralEdgeTwoCarrier
  split_ifs
  · rw [lowerAxis_phase_action]
    simp [cuspPeriodPhaseCircle] <;> rfl
  · rw [upperAxis_phase_action]
    simp [cuspPeriodPhaseCircle] <;> rfl

end SphereSixComplex.Geometry.CuspCollar
