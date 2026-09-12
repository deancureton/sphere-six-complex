module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# The remaining cusp Wang naturality square

The canonical Mayer--Vietoris boundary is already natural under pullback.  The Wang sequence used
for the radial cusp collar, however, is currently supplied only as four exact homomorphisms.  Its
statement does not identify its boundary with a chain-level connecting morphism, so exactness
alone cannot determine the orientation of that boundary.

This file isolates the smallest general interface needed here: naturality after applying one
marked coordinate to each connecting homomorphism.  Everything from that standard
connecting-morphism square to the Section 7 boundary comparison is proved below.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

namespace Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData
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


/-- The fourth marked coordinate on the actual elliptic band overlap. -/
public noncomputable def ellipticBandFourthCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) →+ ℤ :=
  coordinateAfterAddEquiv N.actualHomologyCoordinates.bandOne 3




end EllipticTwoDiscCoverData

end Geometry.AnalyticData

end SphereSixComplex
