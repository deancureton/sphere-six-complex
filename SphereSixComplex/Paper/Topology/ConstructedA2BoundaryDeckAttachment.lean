module

public import SphereSixComplex.Paper.Topology.ConstructedA2BoundaryPhaseCancellation
public import SphereSixComplex.Paper.Topology.StandardA2ToricBoundaryFaceCoverage
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveSingletonBall

@[expose] public section

noncomputable section
open Function Set Topology Matrix

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2EffectivePhase_fanShear_commute
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (p : constructedModel.Carrier) :
    Additive.toMul (constructedModel.fanShear lambda)
      (constructedModel.torusAction (compactTorusEmbedding (constructedA2EffectivePhaseSection k)) p) =
      constructedModel.torusAction (compactTorusEmbedding (constructedA2EffectivePhaseSection k))
        (Additive.toMul (constructedModel.fanShear lambda) p) := by
  rw [fanShear_torusAction]
  apply congrArg (fun g ↦ constructedModel.torusAction g
    (Additive.toMul (constructedModel.fanShear lambda) p))
  ext i
  fin_cases i <;>
    simp [denseTorusShear, compactTorusEmbedding, constructedA2EffectivePhaseSection]

public theorem constructedA2PositiveDeck_effectivePhase_commute
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (p : constructedModel.Carrier) :
    normalizedPositiveDeckCarrierMap N constructedModel lambda
      (constructedModel.torusAction (compactTorusEmbedding (constructedA2EffectivePhaseSection k)) p) =
      constructedModel.torusAction (compactTorusEmbedding (constructedA2EffectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda p) := by
  rw [normalizedPositiveDeckCarrierMap, constructedA2EffectivePhase_fanShear_commute,
    normalizedPositiveDeckCarrierMap]
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_comm, map_mul, Equiv.Perm.mul_apply]

public theorem constructedA2FrozenDeck_effectivePhase_formula
    (r : ℝ) (lambda : ParameterLattice) (k : Fin 2 → Circle)
    (p : localCarrier constructedModel r) :
    (frozenLocalPsiMap N constructedModel r lambda
      (compactPhaseLocalAction constructedModel r (constructedA2EffectivePhaseSection k) p) :
        constructedModel.Carrier) =
      constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * constructedA2EffectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda (p : constructedModel.Carrier)) := by
  rw [frozenLocalPsiMap_eq_compactPhase_positiveDeck]
  change constructedModel.torusAction _
    (normalizedPositiveDeckCarrierMap N constructedModel lambda
      (constructedModel.torusAction _ (p : constructedModel.Carrier))) = _
  rw [constructedA2PositiveDeck_effectivePhase_commute, map_mul, map_mul, Equiv.Perm.mul_apply]

public theorem constructedA2ActualDeck_effectivePhase_carrier
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle)
    (hfix : constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * constructedA2EffectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier)) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier)) :
    letI := actualLocalCuspQuotientAction W
    (((Multiplicative.ofAdd lambda • constructedA2EffectivePhaseCentralPoint W k q).1 :
      localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) =
        normalizedPositiveDeckCarrierMap N constructedModel lambda
          (q.1.1.1 : constructedModel.Carrier) := by
  let _ := actualLocalCuspQuotientAction W
  let C := NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
    N constructedModel W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let p := constructedA2EffectivePhaseCentralPoint W k q
  have hactual : C.psiMap lambda p.1 =
      frozenLocalPsiMap N constructedModel W.localWitness.radius lambda p.1 := by
    apply Subtype.ext
    rw [C.psiMap_coe, frozenLocalPsiMap_coe, p.property]
    rfl
  change ((C.toCuspActionData.psiMap lambda p.1).1 :
    constructedModel.Carrier) = _
  rw [← C.psiMap_eq_generic, hactual]
  exact (constructedA2FrozenDeck_effectivePhase_formula W.localWitness.radius lambda k
    (constructedA2PositiveCentralPoint W q).1).trans hfix

public theorem constructedA2LowerRealAxis_mem_edge (j : Fin 3) (r : ℝ) (hr : 0 ≤ r) :
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

public theorem constructedA2UpperRealAxisTwo_mem_edge (r : ℝ) (hr : 0 ≤ r) :
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

public theorem constructedA2UpperRealAxis_mem_edge (j : Fin 3) (r : ℝ) (hr : 0 ≤ r) :
    inclusion (constructedCentralUpperAxisChart j)
        (singleAxis (constructedCentralUpperAxisIndex j) (r : ℂ)) ∈
      constructedCentralEdgeCarrier j '' Metric.closedBall 0 1 := by
  obtain ⟨x, hx, heq⟩ := constructedA2UpperRealAxisTwo_mem_edge r hr
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

public theorem constructedA2PositiveSingleAxis_real (a : ChartIndex) (j : Fin 3) (z : ℂ)
    (hz : inclusion a (singleAxis j z) ∈ carrierPositivePart) :
    ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ) := by
  rw [inclusion_mem_carrierPositivePart_iff] at hz
  obtain ⟨r, hr, heq⟩ := hz
  refine ⟨r j, hr j, ?_⟩
  have h := congrFun heq j
  simpa [singleAxis] using h

public def constructedA2BoundaryZeroOneParameter : Fin 6 → ParameterLattice :=
  ![0, constructedA2BoundaryShearParameter 0, constructedA2BoundaryShearParameter 0,
    constructedA2BoundaryShearParameter 1, constructedA2BoundaryShearParameter 1, 0]

public def constructedA2BoundaryZeroZeroParameter : Fin 6 → ParameterLattice :=
  ![0, 0, constructedA2BoundaryShearParameter 0, constructedA2BoundaryShearParameter 0,
    constructedA2BoundaryShearParameter 1, constructedA2BoundaryShearParameter 1]

public theorem constructedA2BoundaryZeroOneParameter_chart (i : Fin 6) :
    translateChartIndex (constructedA2BoundaryZeroOneParameter i) (constructedA2CellChart 0 i) =
      constructedA2BoundaryZeroOneTarget i := by
  have hzero : shearVector 0 = 0 := by simp [shearVector]
  fin_cases i <;>
    simp [translateChartIndex, constructedA2BoundaryZeroOneParameter,
      constructedA2CellChart, constructedA2BoundaryZeroOneTarget,
      shearVector_constructedA2BoundaryShearParameter, hzero, constructedA2BoundaryDisplacement]

public theorem constructedA2BoundaryZeroZeroParameter_chart (i : Fin 6) :
    translateChartIndex (constructedA2BoundaryZeroZeroParameter i) (constructedA2CellChart 0 i) =
      constructedA2BoundaryZeroZeroTarget i := by
  have hzero : shearVector 0 = 0 := by simp [shearVector]
  fin_cases i <;>
    simp [translateChartIndex, constructedA2BoundaryZeroZeroParameter,
      constructedA2CellChart, constructedA2BoundaryZeroZeroTarget,
      shearVector_constructedA2BoundaryShearParameter, hzero, constructedA2BoundaryDisplacement,
      sub_eq_add_neg, add_comm]

public theorem constructedA2PositiveDeck_singleAxis (lambda : ParameterLattice)
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

public theorem constructedA2CellLiftCoordinates_zero_one (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    constructedA2CellLiftCoordinates i (fun j ↦ (p.1 j : ℂ)) =
      singleAxis (constructedA2CellRemoveIndex i 0) (p.1 0 : ℂ) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [constructedA2CellLiftCoordinates, constructedA2CellRemoveIndex, singleAxis, hp]

public theorem constructedA2CellLiftCoordinates_zero_zero (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    constructedA2CellLiftCoordinates i (fun j ↦ (p.1 j : ℂ)) =
      singleAxis (constructedA2CellRemoveIndex i 1) (p.1 1 : ℂ) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [constructedA2CellLiftCoordinates, constructedA2CellRemoveIndex, singleAxis, hp]

public theorem constructedA2PositiveDeck_square_zero_one (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    ∃ z : ℂ, normalizedPositiveDeckCarrierMap N constructedModel
        (constructedA2BoundaryZeroOneParameter i) (constructedA2CellSquareCarrierPoint 0 i p) =
      inclusion (constructedA2BoundaryZeroOneTarget i)
        (singleAxis (constructedA2CellRemoveIndex i 0) z) := by
  change ∃ z, normalizedPositiveDeckCarrierMap N constructedModel _
    (inclusion _ (constructedA2CellLiftCoordinates i _)) = _
  rw [constructedA2CellLiftCoordinates_zero_one i p hp,
    constructedA2PositiveDeck_singleAxis, constructedA2BoundaryZeroOneParameter_chart]
  exact ⟨_, rfl⟩

public theorem constructedA2PositiveDeck_square_zero_zero (i : Fin 6)
    (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    ∃ z : ℂ, normalizedPositiveDeckCarrierMap N constructedModel
        (constructedA2BoundaryZeroZeroParameter i) (constructedA2CellSquareCarrierPoint 0 i p) =
      inclusion (constructedA2BoundaryZeroZeroTarget i)
        (singleAxis (constructedA2CellRemoveIndex i 1) z) := by
  change ∃ z, normalizedPositiveDeckCarrierMap N constructedModel _
    (inclusion _ (constructedA2CellLiftCoordinates i _)) = _
  rw [constructedA2CellLiftCoordinates_zero_zero i p hp,
    constructedA2PositiveDeck_singleAxis, constructedA2BoundaryZeroZeroParameter_chart]
  exact ⟨_, rfl⟩

public def constructedA2BoundaryZeroOneEdge : Fin 6 → Fin 3 := ![1, 0, 2, 1, 0, 2]
public def constructedA2BoundaryZeroZeroEdge : Fin 6 → Fin 3 := ![2, 1, 0, 2, 1, 0]

public theorem constructedA2PositiveZeroOneAxis_mem_edge (i : Fin 6) (z : ℂ)
    (hz : inclusion (constructedA2BoundaryZeroOneTarget i)
      (singleAxis (constructedA2CellRemoveIndex i 0) z) ∈ carrierPositivePart) :
    inclusion (constructedA2BoundaryZeroOneTarget i)
      (singleAxis (constructedA2CellRemoveIndex i 0) z) ∈
        constructedCentralEdgeCarrier (constructedA2BoundaryZeroOneEdge i) ''
          Metric.closedBall 0 1 := by
  obtain ⟨r, hr, rfl⟩ := constructedA2PositiveSingleAxis_real _ _ _ hz
  fin_cases i
  · exact constructedA2LowerRealAxis_mem_edge 1 r hr
  · exact constructedA2UpperRealAxis_mem_edge 0 r hr
  · exact constructedA2LowerRealAxis_mem_edge 2 r hr
  · exact constructedA2UpperRealAxis_mem_edge 1 r hr
  · exact constructedA2LowerRealAxis_mem_edge 0 r hr
  · exact constructedA2UpperRealAxis_mem_edge 2 r hr

public theorem constructedA2PositiveZeroZeroAxis_mem_edge (i : Fin 6) (z : ℂ)
    (hz : inclusion (constructedA2BoundaryZeroZeroTarget i)
      (singleAxis (constructedA2CellRemoveIndex i 1) z) ∈ carrierPositivePart) :
    inclusion (constructedA2BoundaryZeroZeroTarget i)
      (singleAxis (constructedA2CellRemoveIndex i 1) z) ∈
        constructedCentralEdgeCarrier (constructedA2BoundaryZeroZeroEdge i) ''
          Metric.closedBall 0 1 := by
  obtain ⟨r, hr, rfl⟩ := constructedA2PositiveSingleAxis_real _ _ _ hz
  fin_cases i
  · exact constructedA2LowerRealAxis_mem_edge 2 r hr
  · exact constructedA2UpperRealAxis_mem_edge 1 r hr
  · exact constructedA2LowerRealAxis_mem_edge 0 r hr
  · exact constructedA2UpperRealAxis_mem_edge 2 r hr
  · exact constructedA2LowerRealAxis_mem_edge 1 r hr
  · exact constructedA2UpperRealAxis_mem_edge 0 r hr

public def constructedA2ActualBoundaryGauge (x : Fin 2 → ℝ) : Fin 2 → Circle :=
  constructedA2BoundaryCompactGauge (frozenCompactPhase N (constructedA2BoundaryShearParameter 0))
    (frozenCompactPhase N (constructedA2BoundaryShearParameter 1)) x

public theorem constructedA2BoundaryZeroOneParameter_phase (i : Fin 6) :
    frozenCompactPhase N (constructedA2BoundaryZeroOneParameter i) =
      constructedA2BoundaryZeroOnePhase
        (frozenCompactPhase N (constructedA2BoundaryShearParameter 0))
        (frozenCompactPhase N (constructedA2BoundaryShearParameter 1)) i := by
  fin_cases i <;>
    simp [constructedA2BoundaryZeroOneParameter, constructedA2BoundaryZeroOnePhase]

public theorem constructedA2BoundaryZeroZeroParameter_phase (i : Fin 6) :
    frozenCompactPhase N (constructedA2BoundaryZeroZeroParameter i) =
      constructedA2BoundaryZeroZeroPhase
        (frozenCompactPhase N (constructedA2BoundaryShearParameter 0))
        (frozenCompactPhase N (constructedA2BoundaryShearParameter 1)) i := by
  fin_cases i <;>
    simp [constructedA2BoundaryZeroZeroParameter, constructedA2BoundaryZeroZeroPhase]

public theorem constructedA2ActualBoundaryGauge_zero_one_fixes_positiveDeck
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    constructedModel.torusAction (compactTorusEmbedding
      (frozenCompactPhase N (constructedA2BoundaryZeroOneParameter i) *
        constructedA2EffectivePhaseSection
          (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))))
      (normalizedPositiveDeckCarrierMap N constructedModel (constructedA2BoundaryZeroOneParameter i)
        (constructedA2CellSquareCarrierPoint 0 i p)) =
      normalizedPositiveDeckCarrierMap N constructedModel (constructedA2BoundaryZeroOneParameter i)
        (constructedA2CellSquareCarrierPoint 0 i p) := by
  obtain ⟨z, hz⟩ := constructedA2PositiveDeck_square_zero_one (N := N) i p hp
  have h := constructedA2BoundaryGauge_zero_one_fixes_axis
    (frozenCompactPhase N (constructedA2BoundaryShearParameter 0))
    (frozenCompactPhase N (constructedA2BoundaryShearParameter 1)) i p hp z
  rw [← constructedA2BoundaryZeroOneParameter_phase] at h
  exact (congrArg (fun q ↦ constructedModel.torusAction _ q) hz).trans (h.trans hz.symm)

public theorem constructedA2ActualBoundaryGauge_zero_zero_fixes_positiveDeck
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    constructedModel.torusAction (compactTorusEmbedding
      (frozenCompactPhase N (constructedA2BoundaryZeroZeroParameter i) *
        constructedA2EffectivePhaseSection
          (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))))
      (normalizedPositiveDeckCarrierMap N constructedModel (constructedA2BoundaryZeroZeroParameter i)
        (constructedA2CellSquareCarrierPoint 0 i p)) =
      normalizedPositiveDeckCarrierMap N constructedModel (constructedA2BoundaryZeroZeroParameter i)
        (constructedA2CellSquareCarrierPoint 0 i p) := by
  obtain ⟨z, hz⟩ := constructedA2PositiveDeck_square_zero_zero (N := N) i p hp
  have h := constructedA2BoundaryGauge_zero_zero_fixes_axis
    (frozenCompactPhase N (constructedA2BoundaryShearParameter 0))
    (frozenCompactPhase N (constructedA2BoundaryShearParameter 1)) i p hp z
  rw [← constructedA2BoundaryZeroZeroParameter_phase] at h
  exact (congrArg (fun q ↦ constructedModel.torusAction _ q) hz).trans (h.trans hz.symm)

public theorem constructedA2ActualPhaseOrbit_mem_oneSkeleton_of_deck_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (q : constructedPositiveCentralFiber W.localWitness.radius)
    (lambda : ParameterLattice) (k : Fin 2 → Circle) (i : Fin 3)
    (hfix : constructedModel.torusAction
        (compactTorusEmbedding (frozenCompactPhase N lambda * constructedA2EffectivePhaseSection k))
        (normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier)) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier))
    (hedge : normalizedPositiveDeckCarrierMap N constructedModel lambda
      (q.1.1.1 : constructedModel.Carrier) ∈
        constructedCentralEdgeCarrier i '' Metric.closedBall 0 1) :
    constructedA2EffectivePhaseCentralOrbit W k q ∈ constructedCentralOneSkeleton W := by
  let _ := actualLocalCuspQuotientAction W
  let p := constructedA2EffectivePhaseCentralPoint W k q
  let g := Multiplicative.ofAdd lambda
  let p' : actualLocalCuspCentralSubMulAction W := g • p
  have hcarrier : (p'.1.1 : constructedModel.Carrier) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier) :=
    constructedA2ActualDeck_effectivePhase_carrier W q lambda k hfix
  obtain ⟨x, hx, heq⟩ := hedge
  have hmem : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' ∈ constructedCentralOneSkeleton W := by
    apply constructedCentralCarrier_eq_oneCell_implies_mem_oneSkeleton W p' i x hx
    have h := hcarrier.trans heq.symm
    fin_cases i <;> exact h
  have horbit : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' = constructedA2EffectivePhaseCentralOrbit W k q := by
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p' p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  rwa [horbit] at hmem

public theorem constructedA2ActualBoundaryGauge_square_zero_one_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    constructedA2EffectivePhaseCentralOrbit W
      (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))
      (constructedA2CellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneSkeleton W := by
  apply constructedA2ActualPhaseOrbit_mem_oneSkeleton_of_deck_edge W _
    (constructedA2BoundaryZeroOneParameter i) _ (constructedA2BoundaryZeroOneEdge i)
  · exact constructedA2ActualBoundaryGauge_zero_one_fixes_positiveDeck i p hp
  · obtain ⟨z, hz⟩ := constructedA2PositiveDeck_square_zero_one (N := N) i p hp
    have hpos : normalizedPositiveDeckCarrierMap N constructedModel
        (constructedA2BoundaryZeroOneParameter i) (constructedA2CellSquareCarrierPoint 0 i p) ∈
        carrierPositivePart :=
      carrierPositivePart_torusAction_fanShear _ (normalizedCuspPositiveTwist_real N _) _
        (constructedA2CellSquareCarrierPoint_mem_positive 0 i p)
    rw [hz] at hpos
    change normalizedPositiveDeckCarrierMap N constructedModel _
      (constructedA2CellSquareCarrierPoint 0 i p) ∈ _
    rw [hz]
    exact constructedA2PositiveZeroOneAxis_mem_edge i z hpos

public theorem constructedA2ActualBoundaryGauge_square_zero_zero_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    constructedA2EffectivePhaseCentralOrbit W
      (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))
      (constructedA2CellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneSkeleton W := by
  apply constructedA2ActualPhaseOrbit_mem_oneSkeleton_of_deck_edge W _
    (constructedA2BoundaryZeroZeroParameter i) _ (constructedA2BoundaryZeroZeroEdge i)
  · exact constructedA2ActualBoundaryGauge_zero_zero_fixes_positiveDeck i p hp
  · obtain ⟨z, hz⟩ := constructedA2PositiveDeck_square_zero_zero (N := N) i p hp
    have hpos : normalizedPositiveDeckCarrierMap N constructedModel
        (constructedA2BoundaryZeroZeroParameter i) (constructedA2CellSquareCarrierPoint 0 i p) ∈
        carrierPositivePart :=
      carrierPositivePart_torusAction_fanShear _ (normalizedCuspPositiveTwist_real N _) _
        (constructedA2CellSquareCarrierPoint_mem_positive 0 i p)
    rw [hz] at hpos
    change normalizedPositiveDeckCarrierMap N constructedModel _
      (constructedA2CellSquareCarrierPoint 0 i p) ∈ _
    rw [hz]
    exact constructedA2PositiveZeroZeroAxis_mem_edge i z hpos

public def constructedA2BoundaryCorrectedBallOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) : ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2EffectivePhaseCentralOrbit W
    (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 x.1))
    (constructedA2ClosedBallPositiveCellHomeomorph W x).1

public theorem constructedA2BoundaryCorrectedBallOrbit_boundary_mem_oneSkeleton
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Metric.closedBall (0 : Fin 2 → ℝ) 1) (hx : x.1 ∈ Metric.sphere 0 1) :
    constructedA2BoundaryCorrectedBallOrbit W x ∈ constructedCentralOneSkeleton W := by
  let z : constructedA2CorrectedPlaneCell 0 :=
    ⟨constructedA2CorrectedHexagonHomeomorph 0 x.1,
      (constructedA2CorrectedHexagonHomeomorph_mem_closed_iff 0 x.1).mpr x.property⟩
  obtain ⟨⟨i, p⟩, hproj⟩ := constructedA2CorrectedPlaneSquareProjection_surjective 0 z
  have htile : constructedA2CorrectedPlaneTile 0 i p =
      constructedA2CorrectedHexagonHomeomorph 0 x.1 := congrArg Subtype.val hproj
  have hcell : constructedA2ClosedBallPositiveCellHomeomorph W x =
      constructedA2CellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩ := by
    change constructedA2CorrectedFiniteQuotientCellHomeomorph W.localWitness.radius_pos 0 z = _
    rw [← hproj, constructedA2CorrectedFiniteQuotientCellHomeomorph_apply]
  have hp : p.1 0 = 0 ∨ p.1 1 = 0 := by
    by_contra hp
    push Not at hp
    have hopen := constructedA2CorrectedPlaneTile_mem_open_of_nonzero 0 i p (by
      intro j
      fin_cases j
      · exact hp.1
      · exact hp.2)
    rw [htile] at hopen
    have hball := (constructedA2CorrectedHexagonHomeomorph_mem_open_iff 0 x.1).mp hopen
    exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hx hball
  unfold constructedA2BoundaryCorrectedBallOrbit
  rw [← htile, hcell]
  rcases hp with hp | hp
  · exact constructedA2ActualBoundaryGauge_square_zero_zero_mem_oneSkeleton W i p hp
  · exact constructedA2ActualBoundaryGauge_square_zero_one_mem_oneSkeleton W i p hp

public theorem constructedA2BoundaryCorrectedBallOrbit_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedA2BoundaryCorrectedBallOrbit W) := by
  have hg : Continuous (fun x : Metric.closedBall (0 : Fin 2 → ℝ) 1 ↦
      constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 x.1)) :=
    (constructedA2BoundaryCompactGauge_continuous _ _).comp
      ((constructedA2CorrectedHexagonHomeomorph 0).continuous.comp continuous_subtype_val)
  let f : Metric.closedBall (0 : Fin 2 → ℝ) 1 →
      ConstructedA2ClosedPhaseCell W.localWitness.radius := fun x ↦
    (constructedA2ClosedBallPositiveCellHomeomorph W x,
      constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedHexagonHomeomorph 0 x.1))
  have hf : Continuous f :=
    (constructedA2ClosedBallPositiveCellHomeomorph W).continuous.prodMk hg
  have heq : constructedA2BoundaryCorrectedBallOrbit W = constructedA2ClosedPhaseCellMap W ∘ f := rfl
  rw [heq]
  exact (constructedA2ClosedPhaseCellMap_continuous W).comp hf

end SphereSixComplex.Geometry.InfiniteA2Toric

end
