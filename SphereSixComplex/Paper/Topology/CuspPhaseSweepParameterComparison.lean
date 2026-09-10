module

public import SphereSixComplex.Paper.Topology.CuspPhaseSweepAtlas
public import SphereSixComplex.Paper.Topology.ConstructedA2CircleSweepPrism

@[expose] public section

noncomputable section
open Set Topology Matrix
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open StandardInfiniteA2ToricModel StandardInfiniteA2ToricModel.Construction
open StandardInfiniteA2ToricModel.Established CuspToricPhaseAction
open SphereSixComplex.Periods CuspPeriodExpansion CuspFilling CuspLocalPhaseAction

public theorem phase_edgeZero_swap (u : ℂˣ) (x : Fin 1 → ℝ) :
    constructedModel.torusAction (phaseEmbedding ![u, 1]) (constructedCentralEdgeZeroCarrier x) =
      constructedModel.torusAction (phaseEmbedding ![1, u]) (constructedCentralEdgeZeroCarrier x) := by
  have hl (z : ℂ) : lowerAxisZero z = singleAxis 0 z := by ext i; fin_cases i <;> rfl
  have hu (z : ℂ) : upperAxisTwo z = singleAxis 2 z := by ext i; fin_cases i <;> rfl
  unfold constructedCentralEdgeZeroCarrier
  split_ifs
  · rw [constructedCentralEdgeZeroLowerBranch, hl, lowerAxis_phase_action, lowerAxis_phase_action]
    simp
    rfl
  · rw [constructedCentralEdgeZeroUpperBranch, hu, upperAxis_phase_action, upperAxis_phase_action]
    simp
    rfl

public theorem cyclic_fourthPhaseEdgeZeroSweep (c : Circle) (x : Fin 1 → ℝ) :
    a2CyclicCarrier (fourthPhaseEdgeZeroSweep c x) =
      constructedModel.torusAction (phaseEmbedding ![(Circle.toUnits c)⁻¹, 1])
        (constructedCentralEdgeOneCarrier x) := by
  change a2CyclicCarrier (carrierTorusActionFun _ _) = carrierTorusActionFun _ _
  rw [a2CyclicCarrier_carrierTorusActionFun,
    a2CyclicCarrier_constructedCentralEdgeZeroCarrier, a2CyclicDenseTorus_phaseEmbedding]
  congr 1
  ext i
  fin_cases i <;> simp [a2CyclicPhase]

public theorem cyclic_sq_fourthPhaseEdgeZeroSweep (c : Circle) (x : Fin 1 → ℝ) :
    a2CyclicCarrier (a2CyclicCarrier (fourthPhaseEdgeZeroSweep c x)) =
      constructedModel.torusAction (phaseEmbedding ![1, (Circle.toUnits c)⁻¹])
        (constructedCentralEdgeTwoCarrier x) := by
  change a2CyclicCarrier (a2CyclicCarrier (carrierTorusActionFun _ _)) = _
  rw [a2CyclicCarrier_carrierTorusActionFun, a2CyclicCarrier_carrierTorusActionFun,
    a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier,
    a2CyclicDenseTorus_phaseEmbedding, a2CyclicDenseTorus_phaseEmbedding]
  change constructedModel.torusAction _ (constructedCentralEdgeTwoCarrier x) = _
  unfold constructedCentralEdgeTwoCarrier
  split_ifs
  · rw [lowerAxis_phase_action, lowerAxis_phase_action]
    simp [a2CyclicPhase]
    rfl
  · rw [upperAxis_phase_action, upperAxis_phase_action]
    simp [a2CyclicPhase]
    rfl

public theorem phaseSweepCarrier_zero_third (x : Fin 2 → ℝ) :
    phaseSweepCarrier 0 x =
      constructedModel.torusAction (phaseEmbedding ![Circle.toUnits (circleCutParameter (x 1)), 1])
        (constructedCentralEdgeZeroCarrier (fun _ ↦ x 0)) :=
  (phase_edgeZero_swap _ _).symm

public theorem phaseSweepCarrier_one_third (x : Fin 2 → ℝ) :
    phaseSweepCarrier 1 x =
      constructedModel.torusAction (phaseEmbedding ![(Circle.toUnits (circleCutParameter (x 1)))⁻¹, 1])
        (constructedCentralEdgeOneCarrier (fun _ ↦ x 0)) :=
  cyclic_fourthPhaseEdgeZeroSweep _ _

public theorem phaseSweepCarrier_two_fourth (x : Fin 2 → ℝ) :
    phaseSweepCarrier 2 x =
      constructedModel.torusAction (phaseEmbedding ![1, (Circle.toUnits (circleCutParameter (x 1)))⁻¹])
        (constructedCentralEdgeTwoCarrier (fun _ ↦ x 0)) :=
  cyclic_sq_fourthPhaseEdgeZeroSweep _ _

public theorem circleCutParameter_unitAddCircle (t : ℝ) :
    circleCutParameter (2 * t - 1) = AddCircle.toCircle (t : UnitAddCircle) := by
  rw [circleCutParameter_eq_turn, AddCircle.toCircle_apply_mk]
  congr 1
  simp

public theorem phaseSweepCarrier_zero_period (r t : ℝ) :
    phaseSweepCarrier 0 ![r, 2 * t - 1] =
      constructedModel.torusAction (phaseEmbedding (cuspPeriodPhaseCircle 0 (t : UnitAddCircle)))
        (constructedCentralEdgeZeroCarrier (fun _ ↦ r)) := by
  rw [phaseSweepCarrier_zero_third]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, circleCutParameter_unitAddCircle]
  congr 1

public theorem phaseSweepCarrier_one_period (r t : ℝ) :
    phaseSweepCarrier 1 ![r, 2 * t - 1] =
      constructedModel.torusAction (phaseEmbedding (cuspPeriodPhaseCircle 0 (-t : UnitAddCircle)))
        (constructedCentralEdgeOneCarrier (fun _ ↦ r)) := by
  rw [phaseSweepCarrier_one_third]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, circleCutParameter_unitAddCircle]
  apply congrArg (fun c : Phase ↦ constructedModel.torusAction (phaseEmbedding c)
    (constructedCentralEdgeOneCarrier (fun _ ↦ r)))
  ext i
  fin_cases i <;> simp [cuspPeriodPhaseCircle, PaperAnalyticData.unitCircleExponential,
    AddCircle.toCircle_neg]

public theorem phaseSweepCarrier_two_period (r t : ℝ) :
    phaseSweepCarrier 2 ![r, 2 * t - 1] =
      constructedModel.torusAction (phaseEmbedding (cuspPeriodPhaseCircle 1 (-t : UnitAddCircle)))
        (constructedCentralEdgeTwoCarrier (fun _ ↦ r)) := by
  rw [phaseSweepCarrier_two_fourth]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, circleCutParameter_unitAddCircle]
  apply congrArg (fun c : Phase ↦ constructedModel.torusAction (phaseEmbedding c)
    (constructedCentralEdgeTwoCarrier (fun _ ↦ r)))
  ext i
  fin_cases i <;> simp [cuspPeriodPhaseCircle, PaperAnalyticData.unitCircleExponential,
    AddCircle.toCircle_neg]

public theorem compactCircle_embedding (i : Fin 2) (z : UnitAddCircle) :
    compactTorusEmbedding (constructedA2EffectivePhaseSection (cuspPeriodCompactCircle i z)) =
      phaseEmbedding (cuspPeriodPhaseCircle i z) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [compactTorusEmbedding, constructedA2EffectivePhaseSection, cuspPeriodCompactCircle,
      phaseEmbedding, cuspPeriodPhaseCircle, PaperAnalyticData.unitCircleExponential]

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem phaseSweepOrbit_eq_compact_of_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (j : Fin 2) (x : Fin 2 → ℝ) (y : Fin 1 → ℝ) (z : UnitAddCircle)
    (h : phaseSweepCarrier i x = constructedModel.torusAction
      (phaseEmbedding (cuspPeriodPhaseCircle j z)) (constructedCentralEdgeCarrier i y)) :
    phaseSweepOrbit W i x = constructedA2CentralCompactOrbitMap W
      (cuspPeriodCompactCircle j z) (constructedCentralOneCell W i y) := by
  let _ := actualLocalCuspQuotientAction W
  have hp : phaseSweepPoint W i x = constructedA2CentralCompactMap W
      (cuspPeriodCompactCircle j z) (constructedCentralEdgeCellPoint W i y) := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [phaseSweepPoint, constructedA2CentralCompactMap, compactPhaseLocalAction]
    rw [compactCircle_embedding]
    fin_cases i <;> exact h
  change Quotient.mk _ (phaseSweepPoint W i x) = _
  rw [hp]
  fin_cases i <;> rfl

public theorem phaseSweepToFilling_of_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (j : Fin 2) (x : Fin 2 → ℝ) (y : Fin 1 → ℝ) (z : UnitAddCircle)
    (h : phaseSweepCarrier i x = constructedModel.torusAction
      (phaseEmbedding (cuspPeriodPhaseCircle j z)) (constructedCentralEdgeCarrier i y)) :
    actualLocalCuspCentralOrbitMap W (phaseSweepOrbit W i x) =
      cuspFillingPeriodCircle W j (z,
        actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W i y)) := by
  rw [phaseSweepOrbit_eq_compact_of_carrier W i j x y z h,
    cuspFillingPeriodCircle_centralOrbit]

public theorem phaseSweepToFilling_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (r t : ℝ) :
    actualLocalCuspCentralOrbitMap W (phaseSweepOrbit W 0 ![r, 2 * t - 1]) =
      cuspFillingPeriodCircle W 0 ((t : UnitAddCircle),
        actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 0 (fun _ ↦ r))) :=
  phaseSweepToFilling_of_carrier W 0 0 _ _ _ (phaseSweepCarrier_zero_period r t)

public theorem phaseSweepToFilling_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (r t : ℝ) :
    actualLocalCuspCentralOrbitMap W (phaseSweepOrbit W 1 ![r, 2 * t - 1]) =
      cuspFillingPeriodCircle W 0 ((-t : UnitAddCircle),
        actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 1 (fun _ ↦ r))) :=
  phaseSweepToFilling_of_carrier W 1 0 _ _ _ (phaseSweepCarrier_one_period r t)

public theorem phaseSweepToFilling_two
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (r t : ℝ) :
    actualLocalCuspCentralOrbitMap W (phaseSweepOrbit W 2 ![r, 2 * t - 1]) =
      cuspFillingPeriodCircle W 1 ((-t : UnitAddCircle),
        actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 2 (fun _ ↦ r))) :=
  phaseSweepToFilling_of_carrier W 2 1 _ _ _ (phaseSweepCarrier_two_period r t)

public theorem phaseSweepToFilling_zero_fourth
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (r t : ℝ) :
    actualLocalCuspCentralOrbitMap W (phaseSweepOrbit W 0 ![r, 2 * t - 1]) =
      cuspFillingPeriodCircle W 1 ((t : UnitAddCircle),
        actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 0 (fun _ ↦ r))) := by
  apply phaseSweepToFilling_of_carrier W 0 1
  rw [phaseSweepCarrier_zero_third, phase_edgeZero_swap]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, circleCutParameter_unitAddCircle]
  rfl

public theorem compactOrbit_eq_self_of_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (j : Fin 2) (y : Fin 1 → ℝ) (z : UnitAddCircle)
    (h : constructedModel.torusAction (phaseEmbedding (cuspPeriodPhaseCircle j z))
      (constructedCentralEdgeCarrier i y) = constructedCentralEdgeCarrier i y) :
    constructedA2CentralCompactOrbitMap W (cuspPeriodCompactCircle j z)
      (constructedCentralOneCell W i y) = constructedCentralOneCell W i y := by
  let _ := actualLocalCuspQuotientAction W
  have hp : constructedA2CentralCompactMap W (cuspPeriodCompactCircle j z)
      (constructedCentralEdgeCellPoint W i y) = constructedCentralEdgeCellPoint W i y := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [constructedA2CentralCompactMap, compactPhaseLocalAction]
    rw [compactCircle_embedding]
    fin_cases i <;> exact h
  fin_cases i <;> exact congrArg (Quotient.mk _) hp

public theorem fillingPeriodCircle_edgeOne_fixed
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (y : Fin 1 → ℝ) (z : UnitAddCircle) :
    cuspFillingPeriodCircle W 1 (z,
      actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 1 y)) =
      actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 1 y) := by
  rw [cuspFillingPeriodCircle_centralOrbit,
    compactOrbit_eq_self_of_carrier W 1 1 y z (fourthPhase_edgeOne_fixed z y)]

public theorem fillingPeriodCircle_edgeTwo_fixed
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (y : Fin 1 → ℝ) (z : UnitAddCircle) :
    cuspFillingPeriodCircle W 0 (z,
      actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 2 y)) =
      actualLocalCuspCentralOrbitMap W (constructedCentralOneCell W 2 y) := by
  rw [cuspFillingPeriodCircle_centralOrbit,
    compactOrbit_eq_self_of_carrier W 2 0 y z (thirdPhase_edgeTwo_fixed z y)]

public def phaseSweepPeriod : Fin 3 → Fin 2 := ![0, 0, 1]

public def phaseSweepTime (i : Fin 3) (t : ℝ) : UnitAddCircle :=
  if i = 0 then (t : UnitAddCircle) else (-t : UnitAddCircle)

public theorem phaseSweepOrbit_period
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (r t : ℝ) :
    phaseSweepOrbit W i ![r, 2 * t - 1] =
      constructedA2CentralCompactOrbitMap W
        (cuspPeriodCompactCircle (phaseSweepPeriod i) (phaseSweepTime i t))
        (constructedCentralOneCell W i (fun _ ↦ r)) := by
  fin_cases i
  · exact phaseSweepOrbit_eq_compact_of_carrier W 0 0 _ _ _
      (phaseSweepCarrier_zero_period r t)
  · exact phaseSweepOrbit_eq_compact_of_carrier W 1 0 _ _ _
      (phaseSweepCarrier_one_period r t)
  · exact phaseSweepOrbit_eq_compact_of_carrier W 2 1 _ _ _
      (phaseSweepCarrier_two_period r t)

public theorem phaseSweepOrbit_time_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (r : ℝ) :
    phaseSweepOrbit W i ![r, -1] = constructedCentralOneCell W i (fun _ ↦ r) := by
  have h := phaseSweepOrbit_period W i r 0
  have hz : cuspPeriodCompactCircle (phaseSweepPeriod i) (phaseSweepTime i 0) = 1 := by
    ext j
    simp [phaseSweepTime, cuspPeriodCompactCircle]
  simpa only [mul_zero, zero_sub, hz, constructedA2CentralCompactOrbitMap_one] using h

public theorem phaseSweepOrbit_time_one
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (r : ℝ) :
    phaseSweepOrbit W i ![r, 1] = constructedCentralOneCell W i (fun _ ↦ r) := by
  have h := phaseSweepOrbit_period W i r 1
  have hz : cuspPeriodCompactCircle (phaseSweepPeriod i) (phaseSweepTime i 1) = 1 := by
    ext j
    have h1 : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period 1
    simp [phaseSweepTime, cuspPeriodCompactCircle, h1]
  simpa only [mul_one, show (2 : ℝ) - 1 = 1 by norm_num, hz,
    constructedA2CentralCompactOrbitMap_one] using h

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
