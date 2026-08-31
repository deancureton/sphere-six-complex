/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Topology.ConstructedA2MomentCoordinateHomeomorphProof

/-!
# The punctured-density interface for the constructed A₂ moment coordinate

The noncentral positive stratum is dense in the constructed positive carrier. Consequently, a
continuous extension of the logarithmic moment coordinate is unique, and its value at every
central point is forced by the exact punctured-neighbourhood limit.
-/

@[expose] public section

noncomputable section

open Filter Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The noncentral stratum of the constructed positive carrier. -/
public def constructedA2PositiveOffCentral (r : ℝ) : Set (constructedLocalPositivePart r) :=
  {q | constructedModel.t (q : LocalCarrier constructedModel r) ≠ 0}

/-- The noncentral positive stratum is dense. The polar-modulus retraction preserves
nonvanishing height, so this follows from density of the dense torus in the ambient carrier. -/
public theorem constructedA2PositiveOffCentral_dense (r : ℝ) :
    Dense (constructedA2PositiveOffCentral r) := by
  have htorus : Dense {q : constructedModel.Carrier | constructedModel.t q ≠ 0} := by
    rw [← constructedModel.torus_range]
    exact constructedModel.torus_dense
  have hlocal : Dense {q : LocalCarrier constructedModel r | constructedModel.t q ≠ 0} :=
    htorus.preimage (cuspNeighborhood constructedModel r).isOpen.isOpenMap_subtype_val
  let R := constructedLocalModulusRetraction r
  have hR : Surjective R := fun q ↦ ⟨q, constructedLocalModulusRetraction_fixed r q⟩
  apply (hR.denseRange.dense_image R.continuous hlocal).mono
  rintro q ⟨p, hp, rfl⟩
  change constructedModel.t (constructedLocalModulusRetraction r p) ≠ 0
  rw [constructedLocalModulusRetraction_t]
  exact_mod_cast norm_ne_zero_iff.mpr hp

/-- Every continuous extension of the logarithmic coordinate has the displayed exact limit at a
central point. This is the point-set gluing condition still required of the honeycomb chart. -/
public theorem constructedA2OffCentralMomentCoordinateTarget_tendsto_of_continuousExtension
    {r : ℝ} (F : constructedLocalPositivePart r → constructedPositiveMomentRegion r)
    (hF : Continuous F)
    (hoff : ∀ q ∈ constructedA2PositiveOffCentral r,
      F q = constructedA2OffCentralMomentCoordinateTarget q)
    (q : constructedLocalPositivePart r) :
    Tendsto constructedA2OffCentralMomentCoordinateTarget
      (nhdsWithin q (constructedA2PositiveOffCentral r)) (nhds (F q)) := by
  apply Tendsto.congr' _ (tendsto_nhdsWithin_of_tendsto_nhds hF.continuousAt)
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact hoff p hp

/-- A continuous extension pinned on the noncentral stratum is unique. -/
public theorem constructedA2OffCentralMomentCoordinateTarget_continuousExtension_unique
    {r : ℝ} {F G : constructedLocalPositivePart r → constructedPositiveMomentRegion r}
    (hF : Continuous F) (hG : Continuous G)
    (hFoff : ∀ q ∈ constructedA2PositiveOffCentral r,
      F q = constructedA2OffCentralMomentCoordinateTarget q)
    (hGoff : ∀ q ∈ constructedA2PositiveOffCentral r,
      G q = constructedA2OffCentralMomentCoordinateTarget q) :
    F = G := by
  apply (constructedA2PositiveOffCentral_dense r).denseRange_val.equalizer hF hG
  funext q
  exact (hFoff q q.property).trans (hGoff q q.property).symm

/-- Any two proper pinned moment-coordinate certificates have the same underlying coordinate. -/
public theorem ConstructedA2ProperMomentCoordinate.coordinate_eq
    {r : ℝ} {H K : ConstructedHoneycombCellData r}
    (C : ConstructedA2ProperMomentCoordinate r H)
    (D : ConstructedA2ProperMomentCoordinate r K) :
    C.coordinate = D.coordinate := by
  apply constructedA2OffCentralMomentCoordinateTarget_continuousExtension_unique
    C.proper_coordinate.continuous D.proper_coordinate.continuous
  · intro q hq
    exact C.coordinate_offCentral q hq
  · intro q hq
    exact D.coordinate_offCentral q hq

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

end
