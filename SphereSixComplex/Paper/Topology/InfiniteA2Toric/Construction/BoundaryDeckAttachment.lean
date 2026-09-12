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

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
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

public theorem actualDeck_effectivePhase_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle)
    (hfix : constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * effectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier)) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier)) :
    letI := actualLocalCuspQuotientAction W
    (((Multiplicative.ofAdd lambda • effectivePhaseCentralPoint W k q).1 :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        normalizedPositiveDeckCarrierMap N constructedModel lambda
          (q.1.1.1 : constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N constructedModel W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let p := effectivePhaseCentralPoint W k q
  have hactual : C.psiMap lambda p.1 =
      frozenLocalPsiMap N constructedModel W.localWitness.radius lambda p.1 := by
    apply Subtype.ext
    rw [C.psiMap_coe, frozenLocalPsiMap_coe, p.property]
    rfl
  change ((C.toCuspActionData.psiMap lambda p.1).1 :
    constructedModel.Carrier) = _
  rw [← C.psiMap_eq_generic, hactual]
  exact (frozenDeck_effectivePhase_formula W.localWitness.radius lambda k
    (positiveCentralPoint W q).1).trans hfix

public theorem lowerRealAxis_mem_edge (j : Fin 3) (r : ℝ) (hr : 0 ≤ r) :
    inclusion (false, 0) (singleAxis j (r : ℂ)) ∈
      constructedCentralEdgeCarrier j '' Metric.closedBall 0 1 := by
  obtain ⟨x, hx, heq⟩ := lowerAxisZero_mem_edgeZero_of_nonnegReal r hr
  refine ⟨x, hx, ?_⟩
  fin_cases j
  · have haxis : singleAxis 0 (r : ℂ) = lowerAxisZero r := by
      funext i
      fin_cases i <;> simp [singleAxis, lowerAxisZero]
    simpa [constructedCentralEdgeCarrier, haxis] using heq
  · have h := congrArg a2CyclicCarrier heq
    rw [a2CyclicCarrier_constructedCentralEdgeZeroCarrier,
      a2CyclicCarrier_inclusion, a2CyclicChartIndex_lower_zero] at h
    simpa [constructedCentralEdgeCarrier, a2CyclicRaw, a2CyclicRawLower_lowerAxisZero] using h
  · have h := congrArg (a2CyclicCarrier ∘ a2CyclicCarrier) heq
    simp only [Function.comp_apply] at h
    rw [a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier,
      a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
      a2CyclicChartIndex_lower_zero] at h
    simpa [constructedCentralEdgeCarrier, a2CyclicRaw, a2CyclicRawLower_sq_lowerAxisZero] using h

public theorem upperRealAxisTwo_mem_edge (r : ℝ) (hr : 0 ≤ r) :
    inclusion (true, 0) (upperAxisTwo (r : ℂ)) ∈
      constructedCentralEdgeZeroCarrier '' Metric.closedBall 0 1 := by
  by_cases hz : r = 0
  · refine ⟨fun _ ↦ 1, ?_, ?_⟩
    · simp [Metric.mem_closedBall, dist_zero_right, Pi.norm_def]
    · simp [constructedCentralEdgeZeroCarrier, constructedCentralEdgeZeroUpperBranch, hz]
  · have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    have heq := inclusion_lowerAxisZero_eq_upperAxisTwo 0 (r : ℂ)⁻¹ (inv_ne_zero hc)
    rw [inv_inv] at heq
    rw [← heq, ← Complex.ofReal_inv]
    exact lowerAxisZero_mem_edgeZero_of_nonnegReal r⁻¹ (inv_nonneg.mpr hr)

public theorem upperRealAxis_mem_edge (j : Fin 3) (r : ℝ) (hr : 0 ≤ r) :
    inclusion (constructedCentralUpperAxisChart j)
        (singleAxis (constructedCentralUpperAxisIndex j) (r : ℂ)) ∈
      constructedCentralEdgeCarrier j '' Metric.closedBall 0 1 := by
  obtain ⟨x, hx, heq⟩ := upperRealAxisTwo_mem_edge r hr
  refine ⟨x, hx, ?_⟩
  fin_cases j
  · have haxis : singleAxis 2 (r : ℂ) = upperAxisTwo r := by
      funext i
      fin_cases i <;> simp [singleAxis, upperAxisTwo]
    simpa [constructedCentralEdgeCarrier, constructedCentralUpperAxisChart,
      constructedCentralUpperAxisIndex, haxis] using heq
  · have h := congrArg a2CyclicCarrier heq
    rw [a2CyclicCarrier_constructedCentralEdgeZeroCarrier,
      a2CyclicCarrier_inclusion, a2CyclicChartIndex_upper_zero] at h
    simpa [constructedCentralEdgeCarrier, constructedCentralUpperAxisChart,
      constructedCentralUpperAxisIndex, a2CyclicRaw, a2CyclicRawUpper_upperAxisTwo] using h
  · have h := congrArg (a2CyclicCarrier ∘ a2CyclicCarrier) heq
    simp only [Function.comp_apply] at h
    rw [a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier,
      a2CyclicCarrier_inclusion, a2CyclicCarrier_inclusion,
      a2CyclicChartIndex_sq_upper_zero] at h
    simpa [constructedCentralEdgeCarrier, constructedCentralUpperAxisChart,
      constructedCentralUpperAxisIndex, a2CyclicRaw, a2CyclicRawUpper_sq_upperAxisTwo] using h

public theorem positiveSingleAxis_real (a : ChartIndex) (j : Fin 3) (z : ℂ)
    (hz : inclusion a (singleAxis j z) ∈ carrierPositivePart) :
    ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) := by
  rw [inclusion_mem_carrierPositivePart_iff] at hz
  obtain ⟨r, hr, heq⟩ := hz
  refine ⟨r j, hr j, ?_⟩
  have h := congrFun heq j
  simpa [singleAxis] using h

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

public def boundaryZeroOneEdge : Fin 6 → Fin 3 := ![1, 0, 2, 1, 0, 2]
public def boundaryZeroZeroEdge : Fin 6 → Fin 3 := ![2, 1, 0, 2, 1, 0]

public theorem positiveZeroOneAxis_mem_edge (i : Fin 6) (z : ℂ)
    (hz : inclusion (boundaryZeroOneTarget i)
      (singleAxis (cellRemoveIndex i 0) z) ∈ carrierPositivePart) :
    inclusion (boundaryZeroOneTarget i)
      (singleAxis (cellRemoveIndex i 0) z) ∈
        constructedCentralEdgeCarrier (boundaryZeroOneEdge i) ''
          Metric.closedBall 0 1 := by
  obtain ⟨r, hr, rfl⟩ := positiveSingleAxis_real _ _ _ hz
  fin_cases i
  · exact lowerRealAxis_mem_edge 1 r hr
  · exact upperRealAxis_mem_edge 0 r hr
  · exact lowerRealAxis_mem_edge 2 r hr
  · exact upperRealAxis_mem_edge 1 r hr
  · exact lowerRealAxis_mem_edge 0 r hr
  · exact upperRealAxis_mem_edge 2 r hr

public theorem positiveZeroZeroAxis_mem_edge (i : Fin 6) (z : ℂ)
    (hz : inclusion (boundaryZeroZeroTarget i)
      (singleAxis (cellRemoveIndex i 1) z) ∈ carrierPositivePart) :
    inclusion (boundaryZeroZeroTarget i)
      (singleAxis (cellRemoveIndex i 1) z) ∈
        constructedCentralEdgeCarrier (boundaryZeroZeroEdge i) ''
          Metric.closedBall 0 1 := by
  obtain ⟨r, hr, rfl⟩ := positiveSingleAxis_real _ _ _ hz
  fin_cases i
  · exact lowerRealAxis_mem_edge 2 r hr
  · exact upperRealAxis_mem_edge 1 r hr
  · exact lowerRealAxis_mem_edge 0 r hr
  · exact upperRealAxis_mem_edge 2 r hr
  · exact lowerRealAxis_mem_edge 1 r hr
  · exact upperRealAxis_mem_edge 0 r hr

public def actualBoundaryGauge (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  boundaryCompactGauge (frozenCompactPhase N (boundaryShearParameter 0))
    (frozenCompactPhase N (boundaryShearParameter 1)) x

public theorem boundaryZeroOneParameter_phase (i : Fin 6) :
    frozenCompactPhase N (boundaryZeroOneParameter i) =
      boundaryZeroOnePhase
        (frozenCompactPhase N (boundaryShearParameter 0))
        (frozenCompactPhase N (boundaryShearParameter 1)) i := by
  fin_cases i <;>
    simp [boundaryZeroOneParameter, boundaryZeroOnePhase]

public theorem boundaryZeroZeroParameter_phase (i : Fin 6) :
    frozenCompactPhase N (boundaryZeroZeroParameter i) =
      boundaryZeroZeroPhase
        (frozenCompactPhase N (boundaryShearParameter 0))
        (frozenCompactPhase N (boundaryShearParameter 1)) i := by
  fin_cases i <;>
    simp [boundaryZeroZeroParameter, boundaryZeroZeroPhase]

public theorem actualBoundaryGauge_zero_one_fixes_positiveDeck
    (i : Fin 6) (p : CellSquare) (hp : p.1 1 = 0) :
    constructedModel.torusAction (compactTorusEmbedding
      (frozenCompactPhase N (boundaryZeroOneParameter i) *
        effectivePhaseSection
          (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))))
      (normalizedPositiveDeckCarrierMap N constructedModel (boundaryZeroOneParameter i)
        (cellSquareCarrierPoint 0 i p)) =
      normalizedPositiveDeckCarrierMap N constructedModel (boundaryZeroOneParameter i)
        (cellSquareCarrierPoint 0 i p) := by
  obtain ⟨z, hz⟩ := positiveDeck_square_zero_one (N := N) i p hp
  have h := boundaryGauge_zero_one_fixes_axis
    (frozenCompactPhase N (boundaryShearParameter 0))
    (frozenCompactPhase N (boundaryShearParameter 1)) i p hp z
  rw [← boundaryZeroOneParameter_phase] at h
  exact (congrArg (fun q ↦ constructedModel.torusAction _ q) hz).trans (h.trans hz.symm)

public theorem actualBoundaryGauge_zero_zero_fixes_positiveDeck
    (i : Fin 6) (p : CellSquare) (hp : p.1 0 = 0) :
    constructedModel.torusAction (compactTorusEmbedding
      (frozenCompactPhase N (boundaryZeroZeroParameter i) *
        effectivePhaseSection
          (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))))
      (normalizedPositiveDeckCarrierMap N constructedModel (boundaryZeroZeroParameter i)
        (cellSquareCarrierPoint 0 i p)) =
      normalizedPositiveDeckCarrierMap N constructedModel (boundaryZeroZeroParameter i)
        (cellSquareCarrierPoint 0 i p) := by
  obtain ⟨z, hz⟩ := positiveDeck_square_zero_zero (N := N) i p hp
  have h := boundaryGauge_zero_zero_fixes_axis
    (frozenCompactPhase N (boundaryShearParameter 0))
    (frozenCompactPhase N (boundaryShearParameter 1)) i p hp z
  rw [← boundaryZeroZeroParameter_phase] at h
  exact (congrArg (fun q ↦ constructedModel.torusAction _ q) hz).trans (h.trans hz.symm)

public theorem actualPhaseOrbit_mem_oneSkeleton_of_deck_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (i : Fin 3)
    (hfix : constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * effectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier)) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier))
    (hedge : normalizedPositiveDeckCarrierMap N constructedModel lambda
      (q.1.1.1 : constructedModel.Carrier) ∈
        constructedCentralEdgeCarrier i '' Metric.closedBall 0 1) :
    effectivePhaseCentralOrbit W k q ∈ constructedCentralOneSkeleton W := by
  let _ := actualLocalCuspQuotientAction W
  let p := effectivePhaseCentralPoint W k q
  let g := Multiplicative.ofAdd lambda
  let p' : actualLocalCuspCentralSubMulAction W := g • p
  have hcarrier : (p'.1.1 : constructedModel.Carrier) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier) :=
    actualDeck_effectivePhase_carrier W q lambda k hfix
  obtain ⟨x, hx, heq⟩ := hedge
  have hmem : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' ∈ constructedCentralOneSkeleton W := by
    apply mem_centralOneSkeleton_of_carrier_eq_oneCell W p' i x hx
    have h := hcarrier.trans heq.symm
    fin_cases i <;> exact h
  have horbit : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' = effectivePhaseCentralOrbit W k q := by
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p' p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  rwa [horbit] at hmem

public theorem actualBoundaryGauge_square_zero_one_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) (hp : p.1 1 = 0) :
    effectivePhaseCentralOrbit W
      (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
      (cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneSkeleton W := by
  apply actualPhaseOrbit_mem_oneSkeleton_of_deck_edge W _
    (boundaryZeroOneParameter i) _ (boundaryZeroOneEdge i)
  · exact actualBoundaryGauge_zero_one_fixes_positiveDeck i p hp
  · obtain ⟨z, hz⟩ := positiveDeck_square_zero_one (N := N) i p hp
    have hpos : normalizedPositiveDeckCarrierMap N constructedModel
        (boundaryZeroOneParameter i) (cellSquareCarrierPoint 0 i p) ∈
        carrierPositivePart :=
      carrierPositivePart_torusAction_fanShear _ (normalizedCuspPositiveTwist_real N _) _
        (cellSquareCarrierPoint_mem_positive 0 i p)
    rw [hz] at hpos
    change normalizedPositiveDeckCarrierMap N constructedModel _
      (cellSquareCarrierPoint 0 i p) ∈ _
    rw [hz]
    exact positiveZeroOneAxis_mem_edge i z hpos

public theorem actualBoundaryGauge_square_zero_zero_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) (hp : p.1 0 = 0) :
    effectivePhaseCentralOrbit W
      (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
      (cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneSkeleton W := by
  apply actualPhaseOrbit_mem_oneSkeleton_of_deck_edge W _
    (boundaryZeroZeroParameter i) _ (boundaryZeroZeroEdge i)
  · exact actualBoundaryGauge_zero_zero_fixes_positiveDeck i p hp
  · obtain ⟨z, hz⟩ := positiveDeck_square_zero_zero (N := N) i p hp
    have hpos : normalizedPositiveDeckCarrierMap N constructedModel
        (boundaryZeroZeroParameter i) (cellSquareCarrierPoint 0 i p) ∈
        carrierPositivePart :=
      carrierPositivePart_torusAction_fanShear _ (normalizedCuspPositiveTwist_real N _) _
        (cellSquareCarrierPoint_mem_positive 0 i p)
    rw [hz] at hpos
    change normalizedPositiveDeckCarrierMap N constructedModel _
      (cellSquareCarrierPoint 0 i p) ∈ _
    rw [hz]
    exact positiveZeroZeroAxis_mem_edge i z hpos

public def boundaryCorrectedBallOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) : ActualLocalCuspCentralOrbitQuotient W :=
  effectivePhaseCentralOrbit W
    (actualBoundaryGauge (N := N) (correctedHexagonHomeomorph 0 x.1))
    (closedBallPositiveCellHomeomorph W x).1

public theorem boundaryCorrectedBallOrbit_boundary_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1) :
    boundaryCorrectedBallOrbit W x ∈ constructedCentralOneSkeleton W := by
  let z : correctedPlaneCell 0 :=
    ⟨correctedHexagonHomeomorph 0 x.1,
      (correctedHexagonHomeomorph_mem_closed_iff 0 x.1).mpr x.property⟩
  obtain ⟨⟨i, p⟩, hproj⟩ := surjective_correctedPlaneSquareProjection 0 z
  have htile : correctedPlaneTile 0 i p =
      correctedHexagonHomeomorph 0 x.1 := congrArg Subtype.val hproj
  have hcell : closedBallPositiveCellHomeomorph W x =
      cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩ := by
    change correctedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z = _
    rw [← hproj, correctedFiniteQuotientCellHomeomorph_apply]
  have hp : p.1 0 = 0 ∨ p.1 1 = 0 := by
    by_contra hp
    push Not at hp
    have hopen := correctedPlaneTile_mem_open_of_nonzero 0 i p (by
      intro j
      fin_cases j
      · exact hp.1
      · exact hp.2)
    rw [htile] at hopen
    have hball := (correctedHexagonHomeomorph_mem_open_iff 0 x.1).mp hopen
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx hball
  unfold boundaryCorrectedBallOrbit
  rw [← htile, hcell]
  rcases hp with hp | hp
  · exact actualBoundaryGauge_square_zero_zero_mem_oneSkeleton W i p hp
  · exact actualBoundaryGauge_square_zero_one_mem_oneSkeleton W i p hp

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
