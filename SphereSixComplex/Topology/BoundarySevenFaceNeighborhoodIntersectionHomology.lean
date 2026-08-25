module

public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodIntersections
public import SphereSixComplex.Topology.ContractibleSingularMapQuasiIso

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

/-- A nonempty proper face-neighbourhood intersection has zero positive-degree singular homology,
with arbitrary coefficients. -/
public theorem boundarySevenFaceNeighborhoodIntersection_singularHomology_isZero
    (R : AddCommGrpCat) (s : Finset (Fin 8)) (hsne : s.Nonempty)
    (hsproper : s ≠ Finset.univ) (k : ℕ) (hk : k ≠ 0) :
    IsZero (((singularHomologyFunctor AddCommGrpCat k).obj R).obj
      (TopCat.of (boundarySevenFaceNeighborhoodIntersection s))) := by
  let _ : ContractibleSpace (boundarySevenFaceNeighborhoodIntersection s) :=
    boundarySevenFaceNeighborhoodIntersection_contractibleSpace s hsne hsproper
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (boundarySevenFaceNeighborhoodIntersection s)
  have hunit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat k R (TopCat.of Unit) hk
  exact hunit.of_iso (singularHomologyIsoOfHomotopyEquiv R k e)

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
