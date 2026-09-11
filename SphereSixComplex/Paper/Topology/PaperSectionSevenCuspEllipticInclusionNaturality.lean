module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# Marked naturality for the cusp-to-elliptic inclusion

The two residual inclusion-coordinate identities can be stated directly for the actual map from
the cusp collar to the cusp-free elliptic interior.  This file proves that formulation equivalent
to the literal-union formulation used by the two-disc Mayer--Vietoris calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticTwoDiscHomologyCoordinates
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- The marked degree-one coordinate on the actual elliptic interior. -/
public noncomputable def ellipticInteriorDegreeOneCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 1 A.ellipticInterior →+ ℤ :=
  coordinateAfterAddEquiv
    N.actualHomologyCoordinates.normalizedEllipticInteriorHomologyOneEquiv 0




/-- Pulling the actual elliptic degree-one coordinate back along the cusp inclusion gives the
literal-union coordinate already used by the Mayer--Vietoris calculation. -/
public theorem ellipticInteriorDegreeOneCoordinateHom_cuspToEllipticInteriorMap
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 1 (A.openEmbeddingStarData.collarSource 0)) :
    D.ellipticInteriorDegreeOneCoordinateHom N
        (integralSingularHomologyMap 1 D.cuspToEllipticInteriorMap.hom x) =
      cuspDegreeOneCoordinateHom N x := by
  rw [D.cuspToEllipticInteriorMap_homology]
  let e := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  change N.actualHomologyCoordinates.normalizedUnionHomologyOneEquiv
      (e.symm (e (cuspToEllipticUnionHomology D 1 x))) 0 = _
  rw [e.symm_apply_apply]
  rfl



end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
