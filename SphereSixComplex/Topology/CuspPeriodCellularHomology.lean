module
public import SphereSixComplex.Topology.CuspCellularLoopDeckComparison
public import SphereSixComplex.Topology.CuspPeriodLoopDeckComparison

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open StandardCircleHomologyLiftDegree
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem localCuspPeriodLoop_cellularHomology
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius)
    (lambda : ParameterLattice) :
    loopHomologyClass (localCuspPeriodLoop W s hs hsr lambda) =
      (-lambda 0 + lambda 1) • loopHomologyClass (constructedCellularLoopInFilling W 0 2) +
      (-lambda 1) • loopHomologyClass (constructedCellularLoopInFilling W 1 2) := by
  have hp : constructedLocalFillingDeckHomology W lambda =
      loopHomologyClass (localCuspPeriodLoop W s hs hsr lambda) :=
    localCuspPeriodLoop_homology W s hs hsr (constructedCentralOrigin W false) lambda
  rw [← hp, ← constructedLocalFillingDeckHomology_cellularLoop W 0 2,
    ← constructedLocalFillingDeckHomology_cellularLoop W 1 2,
    ← map_zsmul, ← map_zsmul, ← map_add]
  apply congrArg (constructedLocalFillingDeckHomology W)
  rw [show centralEdgeEndpointDeck 0 - centralEdgeEndpointDeck 2 = ![-1,0] from
    centralCellularBasisDeck 0,
    show centralEdgeEndpointDeck 1 - centralEdgeEndpointDeck 2 = ![-1,-1] from
      centralCellularBasisDeck 1]
  ext i
  fin_cases i <;> simp

public theorem localCuspFirstPeriodLoop_cellularHomology
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius) :
    loopHomologyClass (localCuspPeriodLoop W s hs hsr ![1,0]) =
      -loopHomologyClass (constructedCellularLoopInFilling W 0 2) := by
  rw [localCuspPeriodLoop_cellularHomology]
  simp

public theorem localCuspSecondPeriodLoop_cellularHomology
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    [T2Space (ActualLocalCuspCentralOrbitQuotient W)]
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) W.localWitness.radius) :
    loopHomologyClass (localCuspPeriodLoop W s hs hsr ![0,1]) =
      loopHomologyClass (constructedCellularLoopInFilling W 0 2) -
      loopHomologyClass (constructedCellularLoopInFilling W 1 2) := by
  rw [localCuspPeriodLoop_cellularHomology]
  simp [sub_eq_add_neg]

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
