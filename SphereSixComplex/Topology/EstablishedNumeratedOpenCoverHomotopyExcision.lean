module

public import SphereSixComplex.Topology.NumeratedCoverHomotopyExcisionProof

/-!
# Numerated open covers are homotopy excisive

Dold's theorem for a two-set cover, proved from a partition of unity with closed supports.
The former open-support interface fixed the inverse of the double-mapping-cylinder collapse
pointwise, which forced a discontinuous section; see `NumeratedCoverHomotopyExcisionProof`.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

namespace OpenUnionHomotopy

universe u

variable {X : Type u} [TopologicalSpace X]

/-- For a normal paracompact open union, a homotopy equivalence from the overlap to the right
member makes the literal inclusion of the left member into the union a homotopy equivalence. -/
public theorem leftToUnion_isHomotopyEquivalence_of_normal_paracompact
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [NormalSpace ↥(U ∪ V)] [ParacompactSpace ↥(U ∪ V)]
    (hinter : IsHomotopyEquivalence (interToRight U V).hom) :
    IsHomotopyEquivalence (leftToUnion U V).hom :=
  ClosedCover.leftToUnion_isHomotopyEquivalence_of_normal_paracompact_proved U V hU hV hinter

end OpenUnionHomotopy

end SphereSixComplex
