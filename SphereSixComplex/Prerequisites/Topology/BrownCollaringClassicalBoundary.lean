module

public import SphereSixComplex.Prerequisites.Topology.OpenCollarPush
public import Mathlib.Topology.Metrizable.Basic

/-!
# Brown's collaring theorem

Morton Brown, *Locally Flat Imbeddings of Topological Manifolds*, Annals of Mathematics
75 (1962), 331–341, Theorem 1 (p. 337): a locally collared subset of a metric space is
collared. Section II defines a collar as a homeomorphism from `B × [0,1)` onto an open
neighborhood, restricting to the identity at zero. The statement below uses that definition
and makes no dimension, compactness, smoothness, or problem-specific hypothesis.

Source: https://www.maths.gla.ac.uk/~mpowell/Brown%20collars.pdf
-/

@[expose] public section

namespace SphereSixComplex

public def LocallyCollared {X : Type*} [TopologicalSpace X] (B : Set X) : Prop :=
  ∀ x ∈ B, ∃ V : Set X, V ⊆ B ∧ x ∈ V ∧ IsOpen {b : B | b.1 ∈ V} ∧
    Nonempty (OpenTopologicalCollar X V)

public axiom LocallyCollared.nonempty_collar {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (B : Set X) (hB : LocallyCollared B) : Nonempty (OpenTopologicalCollar X B)

end SphereSixComplex
