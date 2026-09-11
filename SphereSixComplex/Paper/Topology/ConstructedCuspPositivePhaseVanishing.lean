module
public import SphereSixComplex.Paper.Topology.ConstructedCuspPositiveProjection
public import SphereSixComplex.Paper.Topology.ConstructedA2CentralCompactAction
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Periods SphereSixComplex.Topology
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge CuspPeriodExpansion
open InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction CircleProductIdentityMappingTorus
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedCuspPositiveProjection_central_action
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (q : ActualLocalCuspCentralOrbitQuotient W) :
    let _ := (constructedCuspPolarData W).positiveDeckAction
    constructedCuspPositiveProjection W
      (actualLocalCuspCentralOrbitMap W (constructedA2CentralCompactOrbitMap W k q)) =
      constructedCuspPositiveProjection W (actualLocalCuspCentralOrbitMap W q) := by
  let _ := (constructedCuspPolarData W).positiveDeckAction
  induction q using Quotient.inductionOn with | h x =>
    exact actualPositiveModulusProjection_central_compact W _ _ _
      (constructedA2EffectivePhaseSection k) x.1 x.2



end SphereSixComplex.Geometry.CuspStraighteningRetraction
