/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Topology.ConstructedA2PositivePartContractibilityProof

/-!
# Specialized phase geometry for the constructed infinite A₂ carrier

At the actual cusp radius, the positive-part contractibility field follows from the global
moment-coordinate homeomorphism.  The central honeycomb follows from compatible cell charts.
Thus the broad abstract-model phase assumption reduces, for the model used by the paper, to
these two explicit coordinate constructions and the cellular quotient theorem.
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
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion
open
  SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The exact coordinate and cellular inputs still needed for the constructed model at the
actual cusp radius.  Unlike the former phase-geometry assumption, every field refers to the
single explicit carrier used in the paper. -/
public structure ConstructedPolarHoneycombCoordinateData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) where
  momentHomeomorph :
    constructedLocalPositivePart W.localWitness.radius ≃ₜ
      constructedPositiveMomentRegion W.localWitness.radius
  honeycombCells : ConstructedHoneycombCellData W.localWitness.radius
  quotientRelativeCW :
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

namespace ConstructedPolarHoneycombCoordinateData

/-- Coordinate data provide all three fields of the constructed-model residual package. -/
public noncomputable def toResidualData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (C : ConstructedPolarHoneycombCoordinateData W) :
    ConstructedPolarHoneycombResidualData W where
  honeycomb := C.honeycombCells.honeycomb
  positive_contractible :=
    constructedLocalPositivePart_contractible_of_momentHomeomorph
      W.localWitness.radius_pos C.momentHomeomorph
  quotient_relativeCW := C.quotientRelativeCW

/-- The explicit coordinate package gives the specialized normalized phase geometry. -/
public noncomputable def toPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    {W : ActualPuncturedCuspCollarWitness N constructedModel}
    (C : ConstructedPolarHoneycombCoordinateData W) :
    {Q : NormalizedPolarHoneycombConstructionData N constructedModel
        W.localWitness.radius //
      PolarPhaseGeometricCore constructedModel W.localWitness.radius
        Q.toPolarHoneycombData} :=
  C.toResidualData.toPhaseGeometry

end ConstructedPolarHoneycombCoordinateData

/-- Specialized replacement for the abstract-model phase assumption: it is enough to construct
the moment coordinates, compatible honeycomb cells, and the quotient relative CW structure for
the actual constructed carrier. -/
public theorem constructedNormalizedPolarHoneycombPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (h : Nonempty (ConstructedPolarHoneycombCoordinateData W)) :
    Nonempty {Q : NormalizedPolarHoneycombConstructionData N constructedModel
        W.localWitness.radius //
      PolarPhaseGeometricCore constructedModel W.localWitness.radius
        Q.toPolarHoneycombData} :=
  h.map ConstructedPolarHoneycombCoordinateData.toPhaseGeometry

/-- The same specialized inputs give precisely the phase-spreading package consumed by the
paper's cusp retraction. -/
public theorem constructedPolarHoneycombPhaseSpreadingPackage
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (h : Nonempty (ConstructedPolarHoneycombCoordinateData W)) :
    Nonempty (Σ P : PolarHoneycombData constructedModel W.localWitness.radius,
      FrozenLocalCuspPhaseSpreadingData N constructedModel W.localWitness.radius P) := by
  obtain ⟨C⟩ := h
  let Q := C.toResidualData.toTopologicalData.toConstructionData
  let P := Q.toPolarHoneycombData
  have H : PolarPhaseRadialCompatibility N constructedModel W.localWitness.radius P :=
    ⟨fun lambda i ↦ norm_normalizedCuspPositiveTwist N lambda i⟩
  have G : PolarPhaseGeometricCore constructedModel W.localWitness.radius P :=
    polarPhaseGeometricCore_of_invariantModulus_only Q
      C.toResidualData.toTopologicalData.toConstructionData_invariantModulus
  exact ⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    (compactPhaseOrbit_prod_isQuotientMap constructedModel W.localWitness.radius P)
    H.toDeckLift G⟩⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
