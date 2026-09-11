module

public import SphereSixComplex.Prerequisites.Topology.BoundarySevenFaceNeighborhoodIntersections
public import SphereSixComplex.Prerequisites.Topology.ContractibleSingularMapQuasiIso

/-!
# Homology of finite face-neighbourhood intersections

The explicit strong deformation retractions of the affine intersections imply their positive-
degree singular homology vanishes.  More strongly, every specified map from a realized standard
simplex into such an intersection induces a quasi-isomorphism on singular chains.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap Simplicial

namespace SphereSixComplex


/-- Any continuous map from a realized standard simplex to a nonempty proper intersection
induces a singular-chain quasi-isomorphism. -/
public theorem standardSimplexToBoundarySevenFaceNeighborhoodIntersection_quasiIso
    (R : AddCommGrpCat) (n : ℕ) (s : Finset (Fin 8))
    (hsne : s.Nonempty) (hsproper : s ≠ Finset.univ)
    (f : C((SSet.toTop.obj (Δ[n] : SSet.{0}) : Type),
      boundarySevenFaceNeighborhoodIntersection s)) :
    QuasiIso (standardSimplexToContractibleSingularChainMap R n f) := by
  let _ : ContractibleSpace (boundarySevenFaceNeighborhoodIntersection s) :=
    boundarySevenFaceNeighborhoodIntersection_contractibleSpace s hsne hsproper
  exact standardSimplexToContractibleSingularChainMap_quasiIso R n f

end SphereSixComplex
