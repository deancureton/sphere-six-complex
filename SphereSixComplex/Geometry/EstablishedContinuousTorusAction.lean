module

public import SphereSixComplex.Geometry.CuspStraighteningHomeomorph

/-!
# Joint continuity of the standard toric action

The action of an algebraic torus on a toric variety is jointly algebraic, hence continuous.
The current toric-model interface exposes continuity of every fixed multiplier and holomorphicity
for smooth parameter families, but not this joint-continuity theorem.  This file isolates that
standard toric fact; it contains no cusp straightening, quotient, or retraction conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspStraighteningExtension
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- Joint continuity of the algebraic torus action on the standard infinite `A₂` toric
model.  This is an API boundary until the explicit chart formulas are exposed in a form from
which Mathlib's continuity lemmas can derive the result directly. -/
public axiom establishedContinuousTorusAction (M : Model) : ContinuousTorusAction M

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
