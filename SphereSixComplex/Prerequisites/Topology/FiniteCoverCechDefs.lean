module

public import SphereSixComplex.Prerequisites.Topology.SingularExcisionOpenCover
public import SphereSixComplex.Prerequisites.Topology.SingularStandardSimplexCone
public import SphereSixComplex.Prerequisites.Topology.FirstQuadrantSingleColumnTotal
public import Mathlib.AlgebraicTopology.CechNerve

/-!
# The finite-cover Cech--singular bicomplex

This file contains the objects and augmentation used by the finite-cover Leray--Cech
comparison.  Its proof is separated from these definitions so that the degreewise row
contractions can use them without creating an import cycle.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

section FiniteCoverCech

variable {iota X : Type} [TopologicalSpace X]

/-- The intersection selected by a finite set of cover indices.  The empty intersection is the
whole space, as usual. -/
public def finiteCoverIntersection (U : iota → Set X) (s : Finset iota) : Set X :=
  ⋂ i ∈ s, U i


















end FiniteCoverCech

end SphereSixComplex
