module

public import SphereSixComplex.Prerequisites.Topology.StandardSimplexSimplicialSingularComparison
public import SphereSixComplex.Prerequisites.Topology.BoundarySevenFaceNeighborhoodDeformation

/-!
# The local simplicial--singular comparison on a boundary face

The canonical adjunction unit on the standard six-simplex, followed by the singular-set map of
the inclusion into its affine face neighbourhood, induces a quasi-isomorphism on integral
chains.  The proof factors this exact canonical map into the standard-simplex comparison and the
singular-chain map of the explicit face-neighbourhood homotopy equivalence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Simplicial

namespace SphereSixComplex

/-- The canonical simplicial map from the standard six-simplex to singular simplices in its
`i`-th affine face neighbourhood. -/
public noncomputable def boundarySevenFaceNeighborhoodLocalComparisonSSetMap
    (i : Fin 8) :
    (Δ[6] : SSet.{0}) ⟶
      TopCat.toSSet.obj (TopCat.of (boundarySevenComparisonFaceNeighborhood i)) :=
  sSetTopAdj.unit.app (Δ[6] : SSet.{0}) ≫
    TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i)




end SphereSixComplex
