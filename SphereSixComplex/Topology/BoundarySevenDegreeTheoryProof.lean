module

public import SphereSixComplex.Topology.BoundarySevenCechTotalQuasiIsoProof
public import SphereSixComplex.Topology.BoundarySevenDegreeTransportProof

/-!
# The boundary-seven degree theory

The Cech argument supplies the canonical integral simplicial-to-singular comparison, while the
independent generator-transport argument proves that coordinate reflection acts by negation on
top homology.  This downstream adapter combines the two results without making the pure Cech or
mod-two homology development depend on degree theory.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- The standard six-sphere has the complete degree theory used by the oriented homotopy-sphere
development. -/
public theorem sixSphereDegreeTheory_proof :
    Nonempty OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory :=
  sixSphereDegreeTheory_of_boundarySevenComparison
    boundarySeven_integralComparison_proof

end SphereSixComplex
