module

public import SphereSixComplex.Paper.Topology.ConstructedA2PositivePartContractibilityProof
public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCorrectedCover

/-!
# Exact coordinate residue for the constructed A₂ polar honeycomb

The explicit carrier already supplies the positive-deck covering and Hausdorff quotient.  The
remaining coordinate package consists of a global moment-coordinate homeomorphism and a
relative CW structure on the orbit quotient. The central honeycomb cell charts are proved.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction


/-- The relative CW structure still required on the constructed positive-deck quotient. -/
public abbrev ConstructedA2PositiveQuotientRelativeCW
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  letI := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  RelCWComplex
    (Set.univ : Set (PolarHoneycombData.OrbitQuotient
      (constructedLocalPositivePart W.localWitness.radius)))
    (PolarHoneycombData.orbitCore
      {q : constructedLocalPositivePart W.localWitness.radius |
        constructedModel.t
          (q : localCarrier constructedModel W.localWitness.radius) = 0})



end SphereSixComplex.Geometry.InfiniteA2Toric

end
