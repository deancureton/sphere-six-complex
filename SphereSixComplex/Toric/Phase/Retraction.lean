module

public import SphereSixComplex.Toric.Positive.QuotientRetraction
public import SphereSixComplex.Toric.Honeycomb.CorrectedCover
public import SphereSixComplex.Cusp.Retraction.PhaseCompatibility

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

public def constructedPolarHoneycombConstruction
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    NormalizedPolarHoneycombConstructionData N constructedModel W.localWitness.radius :=
  constructedPolarHoneycombConstructionData W
    (correctedHoneycombHomeomorph W.localWitness.radius_pos)
    (constructedPositiveQuotientRetraction W)

public instance constructedHasCuspPhaseSpreading
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) : HasCuspPhaseSpreading W := by
  let Q := constructedPolarHoneycombConstruction W
  let P := Q.toPolarHoneycombData
  let := P.positiveDeckAction
  let R := P.positiveEquivariantStrongDeformationRetraction
  exact ⟨⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    (compactPhaseOrbit_prod_isQuotientMap constructedModel W.localWitness.radius P)
    (PolarPhaseDeckLift.ofNormEq
      (fun lambda i ↦ norm_normalizedCuspPositiveTwist N lambda i)) R
    (compactPhaseOrbit_homotopy_eq_of_invariantModulus Q
      (constructedLocalModulus_compactPhase W.localWitness.radius) R)⟩⟩⟩

end SphereSixComplex.Geometry.InfiniteA2Toric
