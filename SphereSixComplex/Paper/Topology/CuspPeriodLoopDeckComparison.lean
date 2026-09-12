module

public import SphereSixComplex.Paper.Topology.ActualCuspCentralFiberRetraction
public import SphereSixComplex.Prerequisites.Topology.QuotientCoverLoopHomology
public import SphereSixComplex.Paper.Topology.PaperCuspActualAffineFillingCoverSquare

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.InfiniteA2Toric
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public def localCuspPeriodLift
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (lambda : ParameterLattice) :
    let _ := actualLocalCuspQuotientAction W
    Path (localCuspExponentialPoint M W.localWitness.radius 0 s hsr)
      ((Additive.toMul lambda : Multiplicative ParameterLattice) •
        localCuspExponentialPoint M W.localWitness.radius 0 s hsr) := by
  let _ := actualLocalCuspQuotientAction W
  let F := assembledFuchsianPeriodFunctions E D
  let x := periodValues F.tau F.mu F.beta (N.lift s)
  let v := periodVector x (firstPeriodCoefficients lambda)
  refine ⟨⟨fun t ↦ additiveCuspFillingLift W ⟨((t : ℝ) • v,s), ?_⟩, ?_⟩, ?_, ?_⟩
  · change ‖cuspQ s‖ < W.localWitness.radius
    simpa only [Metric.mem_ball, dist_zero_right] using hsr
  · apply (additiveCuspFillingLift W).continuous.comp
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.smul continuous_const).prodMk continuous_const
  · change localCuspExponentialPoint M W.localWitness.radius ((0 : ℝ) • v) s hsr = _
    rw [zero_smul]
  · change localCuspExponentialPoint M W.localWitness.radius ((1 : ℝ) • v) s hsr = _
    rw [one_smul]
    change localCuspExponentialPoint M W.localWitness.radius
      (periodVector x (firstPeriodCoefficients lambda)) s hsr = _
    rw [periodVector_firstPeriodCoefficients]
    have h := localCuspExponentialPoint_period_equivariant N M W.localWitness.radius
      W.localWitness.radius_pos W.localWitness.radius_le s hs hsr 0 lambda
    dsimp only at h
    rw [add_zero] at h
    erw [CuspLocalPhaseAction.LocalHolomorphicPhaseCoefficients.psiMap_eq_generic
      _] at h
    exact h.symm

public def localCuspPeriodLoop
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (lambda : ParameterLattice) :
    Path (actualCuspFillingProjection W (localCuspExponentialPoint M W.localWitness.radius 0 s hsr))
      (actualCuspFillingProjection W (localCuspExponentialPoint M W.localWitness.radius 0 s hsr)) := by
  let _ := actualLocalCuspQuotientAction W
  exact ((localCuspPeriodLift W s hs hsr lambda).map
    (actualCuspFillingProjection W).continuous).cast rfl
      ((actualCuspFillingProjection_isQuotientCoveringMap W).map_smul
        (Additive.toMul lambda : Multiplicative ParameterLattice)).symm

public theorem localCuspPeriodLoop_homology
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (e : localCarrier M W.localWitness.radius) (lambda : ParameterLattice) :
    let _ := actualLocalCuspQuotientAction W
    let _ : SimplyConnectedSpace (localCarrier M W.localWitness.radius) :=
      M.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
    let hp := actualCuspFillingProjection_isQuotientCoveringMap W
    let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
      hp.surjective.pathConnectedSpace hp.continuous
    Topology.abelianCoverHomologyEquiv hp e lambda =
      StandardCircleHomologyLiftDegree.loopHomologyClass (localCuspPeriodLoop W s hs hsr lambda) := by
  let _ := actualLocalCuspQuotientAction W
  let _ : SimplyConnectedSpace (localCarrier M W.localWitness.radius) :=
    M.localCarrierSimplyConnected W.localWitness.radius W.localWitness.radius_pos
  let hp := actualCuspFillingProjection_isQuotientCoveringMap W
  let _ : PathConnectedSpace (ActualLocalCuspFilling W) :=
    hp.surjective.pathConnectedSpace hp.continuous
  exact Topology.abelianCoverHomologyEquiv_of_lift hp e _
    (Additive.toMul lambda) (localCuspPeriodLoop W s hs hsr lambda)
    (localCuspPeriodLift W s hs hsr lambda) (fun _ ↦ rfl)

end SphereSixComplex.Geometry.CuspCollar
