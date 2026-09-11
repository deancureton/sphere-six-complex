/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Paper.Topology.ConstructedNormalizedPolarHoneycombReduction
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

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

/-- The convex moment-coordinate model of the local positive part. -/
public def constructedPositiveMomentRegion (r : ℝ) : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 2 ∧ x 2 < r}





end SphereSixComplex.Geometry.InfiniteA2Toric
