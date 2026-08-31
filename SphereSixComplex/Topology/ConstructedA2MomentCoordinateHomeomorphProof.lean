/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Topology.ConstructedA2PositivePartContractibilityProof
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Moment coordinates for the constructed A₂ positive carrier

This file isolates the exact point-set-topological certificate needed for the global moment
coordinate.  Properness packages continuity and closedness, so a proper bijective coordinate map
is already the required homeomorphism.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The minimal global coordinate certificate for the positive part of the constructed carrier. -/
public structure ConstructedA2ProperMomentCoordinate (r : ℝ) where
  coordinate :
    constructedLocalPositivePart r → constructedPositiveMomentRegion r
  proper_coordinate : IsProperMap coordinate
  injective_coordinate : Injective coordinate
  surjective_coordinate : Surjective coordinate

namespace ConstructedA2ProperMomentCoordinate

/-- A proper bijective moment coordinate is a homeomorphism. -/
public noncomputable def toHomeomorph {r : ℝ}
    (C : ConstructedA2ProperMomentCoordinate r) :
    constructedLocalPositivePart r ≃ₜ constructedPositiveMomentRegion r :=
  IsHomeomorph.homeomorph C.coordinate
    ((isHomeomorph_iff_continuous_isClosedMap_bijective).2
      ⟨C.proper_coordinate.continuous, C.proper_coordinate.isClosedMap,
        C.injective_coordinate, C.surjective_coordinate⟩)

/-- Every homeomorphism supplies the proper-coordinate certificate, so the reduction loses no
information. -/
public noncomputable def ofHomeomorph {r : ℝ}
    (e : constructedLocalPositivePart r ≃ₜ constructedPositiveMomentRegion r) :
    ConstructedA2ProperMomentCoordinate r where
  coordinate := e
  proper_coordinate := e.isProperMap
  injective_coordinate := e.injective
  surjective_coordinate := e.surjective

end ConstructedA2ProperMomentCoordinate

/-- Exact reduction of the moment-homeomorphism problem to an explicit proper bijective map. -/
public theorem constructedA2MomentCoordinateHomeomorph_nonempty_iff
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Nonempty (constructedLocalPositivePart W.localWitness.radius ≃ₜ
      constructedPositiveMomentRegion W.localWitness.radius) ↔
      Nonempty (ConstructedA2ProperMomentCoordinate W.localWitness.radius) := by
  constructor
  · exact Nonempty.map ConstructedA2ProperMomentCoordinate.ofHomeomorph
  · exact Nonempty.map ConstructedA2ProperMomentCoordinate.toHomeomorph

/-- The specialized proper-coordinate certificate gives component one of the constructed polar
honeycomb coordinate data. -/
public theorem constructedA2MomentCoordinateHomeomorph_of_properCoordinate
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D}
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (C : ConstructedA2ProperMomentCoordinate W.localWitness.radius) :
    Nonempty (constructedLocalPositivePart W.localWitness.radius ≃ₜ
      constructedPositiveMomentRegion W.localWitness.radius) :=
  ⟨C.toHomeomorph⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
