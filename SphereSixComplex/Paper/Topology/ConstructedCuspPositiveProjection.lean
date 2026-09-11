module
public import SphereSixComplex.Paper.Topology.CuspPositiveModulusProjection
public import SphereSixComplex.Paper.Topology.ConstructedA2PhaseSpreadingCompletion

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Periods CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPeriodExpansion InfiniteA2Toric InfiniteA2Toric
open InfiniteA2Toric.Construction
variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public def constructedCuspPolarData
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PolarHoneycombData constructedModel W.localWitness.radius :=
  (constructedPolarHoneycombResidualData W).toTopologicalData.toConstructionData.toPolarHoneycombData

public def constructedCuspPolarDeckLift
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    PolarPhaseDeckLift N constructedModel W.localWitness.radius (constructedCuspPolarData W) :=
  PolarPhaseRadialCompatibility.toDeckLift
    ⟨fun lambda i ↦ norm_normalizedCuspPositiveTwist N lambda i⟩

public theorem constructedCuspPolar_modulus_phase
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (k : CompactTorus)
    (p : (constructedCuspPolarData W).positivePart) :
    (constructedCuspPolarData W).modulus
      (compactPhaseOrbit constructedModel W.localWitness.radius
        (constructedCuspPolarData W).positivePart (k, p)) = p := by
  exact compactPhaseOrbit_modulus
    (constructedPolarHoneycombResidualData W).toTopologicalData.toConstructionData
    (constructedPolarHoneycombResidualData W).toTopologicalData.toConstructionData_invariantModulus k p

public def constructedCuspPositiveProjection
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    let P := constructedCuspPolarData W
    let _ := P.positiveDeckAction
    C(ActualLocalCuspFilling W, PolarHoneycombData.OrbitQuotient P.positivePart) :=
  actualPositiveModulusProjection W (constructedCuspPolarData W)
    (constructedCuspPolarDeckLift W) (constructedCuspPolar_modulus_phase W)


end SphereSixComplex.Geometry.CuspStraighteningRetraction
