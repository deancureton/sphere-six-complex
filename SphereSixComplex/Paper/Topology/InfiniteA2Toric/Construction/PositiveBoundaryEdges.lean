module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.BoundaryDeckAttachment

@[expose] public section
noncomputable section
open Function Set Topology
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


public theorem actualPhaseOrbit_mem_edge_of_deck_edge
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
    effectivePhaseCentralOrbit W k q ∈
      constructedCentralOneCell W i '' Metric.closedBall 0 1 := by
  let _ := actualLocalCuspQuotientAction W
  let p := effectivePhaseCentralPoint W k q
  let g := Multiplicative.ofAdd lambda
  let p' : actualLocalCuspCentralSubMulAction W := g • p
  have hcarrier : (p'.1.1 : constructedModel.Carrier) =
      normalizedPositiveDeckCarrierMap N constructedModel lambda (q.1.1.1 : constructedModel.Carrier) :=
    actualDeck_effectivePhase_carrier W q lambda k hfix
  obtain ⟨x, hx, heq⟩ := hedge
  have he : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' = constructedCentralOneCell W i x := by
    rw [← centralOneCellRepresentativePoint_orbit W i x]
    apply congrArg (Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)))
    apply Subtype.ext
    apply Subtype.ext
    have h := hcarrier.trans heq.symm
    fin_cases i <;> exact h
  have horbit : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W)) p' = effectivePhaseCentralOrbit W k q := by
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (actualLocalCuspCentralSubMulAction W) p' p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨g, rfl⟩
  exact ⟨x, hx, he.symm.trans horbit⟩

public theorem actualBoundaryGauge_square_zero_one_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) (hp : p.1 1 = 0) :
    effectivePhaseCentralOrbit W
      (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
      (cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneCell W (boundaryZeroOneEdge i) '' Metric.closedBall 0 1 := by
  apply actualPhaseOrbit_mem_edge_of_deck_edge W _
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

public theorem actualBoundaryGauge_square_zero_zero_mem_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 6) (p : CellSquare) (hp : p.1 0 = 0) :
    effectivePhaseCentralOrbit W
      (actualBoundaryGauge (N := N) (correctedPlaneTile 0 i p))
      (cellSquareProjection W.localWitness.radius_pos 0 ⟨i, p⟩).1 ∈
        constructedCentralOneCell W (boundaryZeroZeroEdge i) '' Metric.closedBall 0 1 := by
  apply actualPhaseOrbit_mem_edge_of_deck_edge W _
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

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
