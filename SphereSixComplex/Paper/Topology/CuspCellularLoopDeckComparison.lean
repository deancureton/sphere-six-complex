module
public import SphereSixComplex.Paper.Topology.CuspCellularEdgeDeckLabels
public import SphereSixComplex.Prerequisites.Topology.QuotientCoverLoopHomology

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedCentralEdgeLoopLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j k : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    Path (constructedCentralOrigin W false)
      ((Additive.toMul (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k) :
        Multiplicative ParameterLattice) • constructedCentralOrigin W false) := by
  let _ := actualLocalCuspQuotientAction W
  let _ := actualLocalPsiContinuousConstSMul W
  let g : Multiplicative ParameterLattice :=
    Additive.toMul (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k)
  let q := ((constructedCentralEdgeLift W k).symm.map (continuous_const_smul g)).cast
    (show (Additive.toMul (centralEdgeEndpointDeck j) : Multiplicative ParameterLattice) •
      constructedCentralOrigin W true =
        g • ((Additive.toMul (centralEdgeEndpointDeck k) : Multiplicative ParameterLattice) •
          constructedCentralOrigin W true) from by
      rw [← mul_smul]
      congr 1
      change centralEdgeEndpointDeck j =
        centralEdgeEndpointDeck j - centralEdgeEndpointDeck k + centralEdgeEndpointDeck k
      abel) rfl
  exact (constructedCentralEdgeLift W j).trans q

public def constructedCellularLoopInFilling
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :=
  let _ := (constructedCentralCellAtlas W).cwComplex
  ((constructedCentralCellularEdgePath W j).trans
    (constructedCentralCellularEdgePath W k).symm).map
      (((actualLocalCuspCentralOrbitMap_isEmbedding W).continuous).comp continuous_subtype_val)

public theorem constructedCentralEdgeLoopLift_projects
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) (t : unitInterval) :
    (Quotient.mk _ (constructedCentralEdgeLoopLift W j k t) : ActualLocalCuspFilling W) =
      constructedCellularLoopInFilling W j k t := by
  let _ := actualLocalCuspQuotientAction W
  change Quotient.mk _ ((constructedCentralEdgeLift W j).trans _ t) =
    actualLocalCuspCentralOrbitMap W
      (((constructedCentralCellularEdgePath W j).trans
        (constructedCentralCellularEdgePath W k).symm t).1)
  simp only [Path.trans_apply]
  split_ifs
  · exact constructedCentralEdgeLift_projects W j _
  · change (Quotient.mk _
      ((Additive.toMul (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k) :
        Multiplicative ParameterLattice) • constructedCentralEdgeLift W k _) :
        ActualLocalCuspFilling W) = _
    have hq (g : Multiplicative ParameterLattice) (x : localCarrier constructedModel W.localWitness.radius) :
        (Quotient.mk _ (g • x) : ActualLocalCuspFilling W) = Quotient.mk _ x := by
      apply Quotient.sound
      change MulAction.orbitRel (Multiplicative ParameterLattice)
        (localCarrier constructedModel W.localWitness.radius) (g • x) x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, rfl⟩
    rw [hq]
    exact constructedCentralEdgeLift_projects W k _

public def constructedLocalFillingProjection
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(localCarrier constructedModel W.localWitness.radius, ActualLocalCuspFilling W) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

public theorem constructedLocalFillingProjection_smul
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (g : Multiplicative ParameterLattice)
    (x : localCarrier constructedModel W.localWitness.radius) :
    let _ := actualLocalCuspQuotientAction W
    constructedLocalFillingProjection W (g • x) = constructedLocalFillingProjection W x := by
  let _ := actualLocalCuspQuotientAction W
  apply Quotient.sound
  change MulAction.orbitRel (Multiplicative ParameterLattice)
    (localCarrier constructedModel W.localWitness.radius) (g • x) x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

public theorem constructedLocalFillingProjection_covering
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    let _ := actualLocalCuspQuotientAction W
    IsQuotientCoveringMap (constructedLocalFillingProjection W) (Multiplicative ParameterLattice) := by
  exact W.localWitness.quotient_isQuotientCoveringMap

public def constructedProjectedGraphLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j k : Fin 3) :
    Path (constructedLocalFillingProjection W (constructedCentralOrigin W false))
      (constructedLocalFillingProjection W (constructedCentralOrigin W false)) :=
  ((constructedCentralEdgeLoopLift W j k).map
    (constructedLocalFillingProjection W).continuous).cast rfl
      (constructedLocalFillingProjection_smul W _ _).symm

public theorem constructedProjectedGraphLoop_deck
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j k : Fin 3) :
    let _ := actualLocalCuspQuotientAction W
    (constructedLocalFillingProjection_covering W).fundamentalGroupToMulOpposite
      ⟨constructedCentralOrigin W false, rfl⟩
      (Path.Homotopic.Quotient.mk (constructedProjectedGraphLoop W j k)) =
    MulOpposite.op (Additive.toMul (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k)) := by
  let _ := actualLocalCuspQuotientAction W
  let hp := constructedLocalFillingProjection_covering W
  let g : Multiplicative ParameterLattice :=
    Additive.toMul (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k)
  let ex : (constructedLocalFillingProjection W) ⁻¹'
      {constructedLocalFillingProjection W (constructedCentralOrigin W false)} :=
    ⟨constructedCentralOrigin W false, rfl⟩
  let ey : (constructedLocalFillingProjection W) ⁻¹'
      {constructedLocalFillingProjection W (constructedCentralOrigin W false)} :=
    ⟨g • constructedCentralOrigin W false, constructedLocalFillingProjection_smul W g _⟩
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := ex) (ey := ey) (Path.Homotopic.Quotient.mk (constructedCentralEdgeLoopLift W j k))
    (γ := Path.Homotopic.Quotient.mk (constructedProjectedGraphLoop W j k))
    (by rfl)
  apply hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  exact (congrArg Subtype.val hm).symm

public def constructedLocalFillingDeckHomology
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ParameterLattice ≃+ IntegralSingularHomology 1 (ActualLocalCuspFilling W) := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (localCarrier constructedModel W.localWitness.radius) :=
    constructedModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let hp := constructedLocalFillingProjection_covering W
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  exact Topology.abelianCoverHomologyEquiv hp (constructedCentralOrigin W false)

public theorem constructedLocalFillingDeckHomology_graphLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (j k : Fin 3) :
    constructedLocalFillingDeckHomology W
      (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k) =
      StandardCircleHomologyLiftDegree.loopHomologyClass (constructedProjectedGraphLoop W j k) := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (localCarrier constructedModel W.localWitness.radius) :=
    constructedModel.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let hp := constructedLocalFillingProjection_covering W
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  have h := Topology.abelianCoverHomologyEquiv_hurewicz hp (constructedCentralOrigin W false)
    (Path.Homotopic.Quotient.mk (constructedProjectedGraphLoop W j k))
  rw [constructedProjectedGraphLoop_deck] at h
  exact h

public theorem constructedLocalFillingDeckHomology_cellularLoop
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)] (j k : Fin 3) :
    constructedLocalFillingDeckHomology W
      (centralEdgeEndpointDeck j - centralEdgeEndpointDeck k) =
      StandardCircleHomologyLiftDegree.loopHomologyClass (constructedCellularLoopInFilling W j k) := by
  rw [constructedLocalFillingDeckHomology_graphLoop]
  let p := constructedProjectedGraphLoop W j k
  let q := constructedCellularLoopInFilling W j k
  have h : ∀ t, p t = q t := constructedCentralEdgeLoopLift_projects W j k
  have hxy := p.source.symm.trans ((h 0).trans q.source)
  erw [← StandardCircleHomologyLiftDegree.loopHomologyClass_cast q hxy]
  congr 1
  ext t
  exact h t

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
