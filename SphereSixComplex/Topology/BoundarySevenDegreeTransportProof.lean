module

public import SphereSixComplex.Topology.BoundarySevenProperFaceDegreeTransportProof
public import SphereSixComplex.Topology.SixSphereAntipodalReflectionDegree

/-!
# Unconditional boundary-seven generator transport

The normalized generator and affine proper-face realization now discharge the former
subdivision-generator transport assumption.  Consequently, once the canonical integral
simplicial-to-singular comparison is available, coordinate reflection acts by negation and the
standard six-sphere has the required degree theory.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Simplicial

namespace SphereSixComplex

/-- The former subdivision-generator transport predicate follows with no additional geometric
input. -/
public theorem boundarySevenSubdivisionGeneratorDegreeTransport_proof
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    BoundarySevenSubdivisionGeneratorDegreeTransport hcomparison e :=
  boundarySevenSubdivisionGeneratorDegreeTransport_of_properFace hcomparison e
    (boundarySevenProperFaceGeneratorDegreeTransport_proof hcomparison e)

/-- Coordinate reflection acts by literal negation on top integral homology as soon as the
canonical boundary comparison is known to be a quasi-isomorphism. -/
public theorem sixSphereCoordinateReflection_homology_negation_of_boundaryComparison
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) :
    sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap =
      -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere) :=
  sixSphereCoordinateReflection_homology_negation_of_subdivisionGeneratorTransport
    hcomparison
    (boundarySevenSubdivisionGeneratorDegreeTransport_proof hcomparison
      boundarySevenReflectionEquivariantHomeomorph)

/-- The canonical integral boundary comparison is now the only remaining input to the complete
degree theory of the standard six-sphere. -/
public theorem sixSphereDegreeTheory_of_boundarySevenComparison
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ)) :
    Nonempty OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory :=
  sixSphereDegreeTheory_of_comparison_coordinateReflection hcomparison
    (sixSphereCoordinateReflection_homology_negation_of_boundaryComparison hcomparison)

end SphereSixComplex
