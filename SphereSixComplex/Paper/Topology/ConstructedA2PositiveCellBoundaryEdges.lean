module

public import SphereSixComplex.Paper.Topology.ConstructedA2BoundaryDeckAttachment

@[expose] public section
noncomputable section
open Function Set Topology
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedA2ActualPhaseOrbit_mem_edge_of_deck_edge
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
    constructedA2EffectivePhaseCentralOrbit W k q ∈
      constructedCentralOneCell W i '' Metric.closedBall 0 1 := by
  let _ := actualLocalCuspQuotientAction W
  let p := constructedA2EffectivePhaseCentralPoint W k q
  let g := Multiplicative.ofAdd lambda
  let p' : actualLocalCuspCentralSubMulAction W := g • p
  have hcarrier : (p'.1.1 : constructedModel.Carrier) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier) :=
    constructedA2ActualDeck_effectivePhase_carrier W q lambda k hfix
  obtain ⟨x, hx, heq⟩ := hedge
  have he : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' = constructedCentralOneCell W i x := by
    rw [← constructedCentralOneCellRepresentativePoint_orbit W i x]
    apply congrArg (Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)))
    apply Subtype.ext
    apply Subtype.ext
    have h := hcarrier.trans heq.symm
    fin_cases i <;> exact h
  have horbit : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' = constructedA2EffectivePhaseCentralOrbit W k q := by
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p' p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  exact ⟨x, hx, he.symm.trans horbit⟩

public theorem constructedA2ActualBoundaryGauge_square_zero_one_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 1 = 0) :
    constructedA2EffectivePhaseCentralOrbit W
      (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))
      (constructedA2CellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneCell W (constructedA2BoundaryZeroOneEdge i) '' Metric.closedBall 0 1 := by
  apply constructedA2ActualPhaseOrbit_mem_edge_of_deck_edge W _
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

public theorem constructedA2ActualBoundaryGauge_square_zero_zero_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : ConstructedA2CellSquare) (hp : p.1 0 = 0) :
    constructedA2EffectivePhaseCentralOrbit W
      (constructedA2ActualBoundaryGauge (N := N) (constructedA2CorrectedPlaneTile 0 i p))
      (constructedA2CellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneCell W (constructedA2BoundaryZeroZeroEdge i) '' Metric.closedBall 0 1 := by
  apply constructedA2ActualPhaseOrbit_mem_edge_of_deck_edge W _
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

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
