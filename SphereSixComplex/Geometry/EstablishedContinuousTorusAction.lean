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

/-- Joint continuity of the algebraic torus action on the standard infinite `A₂` toric model.

Read off `Model.torusAction_continuous`.  This does not derive joint continuity from the other
`Model` fields: it is carried by the same toric-geometry boundary that
`StandardInfiniteA2ToricModel.Established.model` asserts, namely that the countable smooth fan of
the `A₂` triangulation has an associated toric variety with its algebraic torus action
[Ful93, Sections 1.4 and 3.1], [Oda88, Sections 1.2--1.3].  An algebraic group action on a variety
is a morphism, hence continuous in both variables at once. -/
public theorem establishedContinuousTorusAction (M : Model) : ContinuousTorusAction M :=
  ⟨M.torusAction_continuous⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
