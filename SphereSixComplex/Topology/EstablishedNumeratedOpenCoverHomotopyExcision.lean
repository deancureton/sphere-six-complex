module

public import SphereSixComplex.Topology.OpenUnionHomotopyEquivalence

/-!
# Numerated open covers are homotopy excisive

This file records the classical Dold theorem for a numerated two-set cover. The constructive
interface fixes the inverse of the double-mapping-cylinder collapse pointwise from the
numeration, so the established boundary contains no paper-specific space or conclusion.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

namespace EstablishedGeneralTopology

open OpenUnionHomotopy

universe u

/-- Dold's numerated-cover theorem: the canonical collapse from the double mapping cylinder of
the two inclusions to their union is a homotopy equivalence. -/
public axiom numeratedTwoSetCoverHomotopyExcisionData
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (N : TwoSetNumeration U V) : N.HomotopyExcisionData

end EstablishedGeneralTopology

namespace OpenUnionHomotopy

universe u

variable {X : Type u} [TopologicalSpace X]

/-- For a normal paracompact open union, a homotopy equivalence from the overlap to the right
member makes the literal inclusion of the left member into the union a homotopy equivalence. -/
public theorem leftToUnion_isHomotopyEquivalence_of_normal_paracompact
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [NormalSpace ↥(U ∪ V)] [ParacompactSpace ↥(U ∪ V)]
    (hinter : IsHomotopyEquivalence (interToRight U V).hom) :
    IsHomotopyEquivalence (leftToUnion U V).hom := by
  let N := Classical.choice (exists_twoSetNumeration U V hU hV)
  let D := EstablishedGeneralTopology.numeratedTwoSetCoverHomotopyExcisionData N
  exact leftToUnion_isHomotopyEquivalence U V hU hV hinter
    (TwoSetNumeration.HomotopyExcisionData.isHomotopyExcisiveSpan N D hU hV)

end OpenUnionHomotopy

end SphereSixComplex
