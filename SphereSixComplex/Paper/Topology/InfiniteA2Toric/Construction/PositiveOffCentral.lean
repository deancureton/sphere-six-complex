/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.MomentCoordinates

/-!
# The punctured-density interface for the constructed A₂ moment coordinate

The noncentral positive stratum is dense in the constructed positive carrier. Consequently, a
continuous extension of the logarithmic moment coordinate is unique, and its value at every
central point is forced by the exact punctured-neighbourhood limit.
-/

@[expose] public section

noncomputable section

open Filter Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction

/-- The noncentral stratum of the constructed positive carrier. -/
public def positiveOffCentral (r : ℝ) : Set (constructedLocalPositivePart r) :=
  {q | constructedModel.t (q : localCarrier constructedModel r) ≠ 0}





end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
