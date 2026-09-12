module
public import SphereSixComplex.Paper.Topology.CuspCellularLoopDeckComparison
public import SphereSixComplex.Paper.Topology.CuspPeriodLoopDeckComparison

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open StandardCircleHomologyLiftDegree
variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
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



end SphereSixComplex.Geometry.CuspCollar
