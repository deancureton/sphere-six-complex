module
public import SphereSixComplex.Topology.QuotientCoverLoopHomology
public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods SphereSixComplex.Topology
open CuspPeriodExpansion CuspFilling CuspLocalPhaseAction StandardInfiniteA2ToricModel
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public def actualCuspDeckHomologyOneEquiv (W : ActualPuncturedCuspCollarWitness N M) :
    IntegralSingularHomology 1 (actualLocalCuspFilling W) ≃+ ParameterLattice := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (LocalCarrier M W.localWitness.radius) :=
    M.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let p : C(LocalCarrier M W.localWitness.radius, actualLocalCuspFilling W) :=
    ⟨Quotient.mk _, continuous_quot_mk⟩
  have hp : IsQuotientCoveringMap p (Multiplicative ParameterLattice) :=
    W.localWitness.quotient_isQuotientCoveringMap
  let _ : PathConnectedSpace (actualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  exact (abelianCoverHomologyEquiv hp (Classical.arbitrary _)).symm

public theorem actualCuspDeckHomologyOneEquiv_eq (W : ActualPuncturedCuspCollarWitness N M)
    (e : LocalCarrier M W.localWitness.radius) :
    let _ := actualLocalCuspQuotientAction W
    let _ : SimplyConnectedSpace (LocalCarrier M W.localWitness.radius) :=
      M.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
    let p : C(LocalCarrier M W.localWitness.radius, actualLocalCuspFilling W) :=
      ⟨Quotient.mk _, continuous_quot_mk⟩
    let hp : IsQuotientCoveringMap p (Multiplicative ParameterLattice) :=
      W.localWitness.quotient_isQuotientCoveringMap
    let _ : PathConnectedSpace (actualLocalCuspFilling W) :=
      hp.surjective.pathConnectedSpace hp.continuous
    actualCuspDeckHomologyOneEquiv W = (abelianCoverHomologyEquiv hp e).symm := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (LocalCarrier M W.localWitness.radius) :=
    M.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let p : C(LocalCarrier M W.localWitness.radius, actualLocalCuspFilling W) :=
    ⟨Quotient.mk _, continuous_quot_mk⟩
  have hp : IsQuotientCoveringMap p (Multiplicative ParameterLattice) :=
    W.localWitness.quotient_isQuotientCoveringMap
  let _ : PathConnectedSpace (actualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  dsimp only [actualCuspDeckHomologyOneEquiv]
  congr 1
  exact abelianCoverHomologyEquiv_basepoint _ _ _

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
