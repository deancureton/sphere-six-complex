module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# Cusp Wang boundary

The cusp collar's Wang boundary is obtained from the mapping-torus boundary through the
homology equivalence induced by the radial collar's homotopy equivalence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

namespace Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates
open SphereSixComplex.CircleMappingTorusHomologyBases

variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- The actual cusp Wang connecting homomorphism before taking monodromy-invariant
coordinates. -/
public noncomputable def actualCuspWangBoundaryHom (A : AnalyticData) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      IntegralSingularHomology 1 G.Fiber := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  let P := circleMappingTorusHTwoPresentation G.clutching
  exact P.boundary.comp
    (integralSingularHomologyEquivOfHomotopyEquiv 2 G.totalHomotopyEquiv).toAddMonoidHom


end EllipticTwoDiscCoverData

end Geometry.AnalyticData

end SphereSixComplex
