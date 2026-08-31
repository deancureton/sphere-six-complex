/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Topology.ConstructedNormalizedPolarHoneycombReduction
import Mathlib.Analysis.Convex.Contractible

/-!
# Contractibility reduction for the constructed positive part

The expected moment-coordinate target is the open-height part of the closed upper half-space.
This file proves that target contractible and reduces positive-part contractibility to the precise
missing global moment-coordinate homeomorphism.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The convex moment-coordinate model of the local positive part. -/
public def constructedPositiveMomentRegion (r : ℝ) : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 2 ∧ x 2 < r}

public theorem constructedPositiveMomentRegion_convex (r : ℝ) :
    Convex ℝ (constructedPositiveMomentRegion r) := by
  have hlinear : IsLinearMap ℝ (fun x : Fin 3 → ℝ ↦ x 2) :=
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  simpa only [constructedPositiveMomentRegion, Set.ofPred_and] using
    (convex_halfSpace_ge hlinear 0).inter (convex_halfSpace_lt hlinear r)

public theorem constructedPositiveMomentRegion_nonempty {r : ℝ} (hr : 0 < r) :
    (constructedPositiveMomentRegion r).Nonempty := by
  refine ⟨0, ?_⟩
  simp [constructedPositiveMomentRegion, hr]

public theorem constructedPositiveMomentRegion_contractible {r : ℝ} (hr : 0 < r) :
    ContractibleSpace (constructedPositiveMomentRegion r) :=
  (constructedPositiveMomentRegion_convex r).contractibleSpace
    (constructedPositiveMomentRegion_nonempty hr)

/-- A global moment-coordinate homeomorphism supplies the remaining positive-part
contractibility field of the constructed polar-honeycomb package. -/
public theorem constructedLocalPositivePart_contractible_of_momentHomeomorph
    {r : ℝ} (hr : 0 < r)
    (e : constructedLocalPositivePart r ≃ₜ constructedPositiveMomentRegion r) :
    ContractibleSpace (constructedLocalPositivePart r) := by
  let _ : ContractibleSpace (constructedPositiveMomentRegion r) :=
    constructedPositiveMomentRegion_contractible hr
  exact e.contractibleSpace

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
