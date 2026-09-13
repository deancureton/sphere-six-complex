module

public import SphereSixComplex.Prerequisites.Topology.SingularExcisionOpenCover
public import Mathlib.AlgebraicTopology.CechNerve

/-! # Finite intersections of a cover -/

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
