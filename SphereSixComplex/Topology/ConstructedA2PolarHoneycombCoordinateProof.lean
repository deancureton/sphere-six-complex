module

public import SphereSixComplex.Topology.ConstructedA2PolarHoneycombPhaseGeometryCompletion

/-!
# Exact coordinate residue for the constructed A₂ polar honeycomb

The explicit carrier already supplies the positive-deck covering and Hausdorff quotient.  The
remaining coordinate package is exactly the product of three independent constructions: a
global moment-coordinate homeomorphism, compatible planar-to-toric honeycomb cell charts, and a
relative CW structure on the orbit quotient.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The global moment-coordinate homeomorphism still required for the constructed carrier. -/
public abbrev ConstructedA2MomentCoordinateHomeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  constructedLocalPositivePart W.localWitness.radius ≃ₜ
    constructedPositiveMomentRegion W.localWitness.radius

/-- The relative CW structure still required on the constructed positive-deck quotient. -/
public abbrev ConstructedA2PositiveQuotientRelativeCW
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
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
          (q : LocalCarrier constructedModel W.localWitness.radius) = 0})

/-- The proposed constructed-model coordinate package exists exactly when its three genuinely
missing components exist.  In particular, none of the already proved covering, properness,
Hausdorffness, or convexity results supplies one of these components implicitly. -/
public theorem constructedPolarHoneycombCoordinateData_nonempty_iff
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Nonempty (ConstructedPolarHoneycombCoordinateData W) ↔
      Nonempty (ConstructedA2MomentCoordinateHomeomorph W) ∧
      Nonempty (ConstructedHoneycombCellData W.localWitness.radius) ∧
      Nonempty (ConstructedA2PositiveQuotientRelativeCW W) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨⟨C.momentHomeomorph⟩, ⟨C.honeycombCells⟩, ⟨C.quotientRelativeCW⟩⟩
  · rintro ⟨⟨e⟩, ⟨H⟩, ⟨hCW⟩⟩
    exact ⟨{
      momentHomeomorph := e
      honeycombCells := H
      quotientRelativeCW := hCW
    }⟩

/-- The three exact coordinate components give the specialized phase geometry used by the
paper, without invoking the universal phase-geometry axiom. -/
public theorem constructedNormalizedPolarHoneycombPhaseGeometry_of_coordinateComponents
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (hMoment : Nonempty (ConstructedA2MomentCoordinateHomeomorph W))
    (hCells : Nonempty (ConstructedHoneycombCellData W.localWitness.radius))
    (hCW : Nonempty (ConstructedA2PositiveQuotientRelativeCW W)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N constructedModel
        W.localWitness.radius //
      PolarPhaseGeometricCore constructedModel W.localWitness.radius
        Q.toPolarHoneycombData} :=
  constructedNormalizedPolarHoneycombPhaseGeometry W
    ((constructedPolarHoneycombCoordinateData_nonempty_iff W).mpr
      ⟨hMoment, hCells, hCW⟩)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
