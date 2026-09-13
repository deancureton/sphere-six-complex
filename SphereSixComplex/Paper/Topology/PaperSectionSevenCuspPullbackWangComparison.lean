module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspCoverNaturality

/-!
# Comparing the pulled-back cusp cover with the cusp Wang coordinate

The canonical Mayer--Vietoris boundary of the pulled-back elliptic cover lands in the kernel of
the elliptic side-difference map.  This module packages that boundary as an additive homomorphism
and isolates the remaining geometric comparison with the final invariant Wang coordinate of the
actual cusp collar.  Once that single homomorphism identity is known, all six pulled-back boundary
basis calculations follow.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex.Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.LatticeData SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.CuspMonodromyCoinvariants

variable {A : AnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- The pulled-back boundary as an additive homomorphism before restricting its codomain to
elliptic side-difference invariants. -/
public noncomputable def cuspPulledBackBoundaryHom :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) :=
  ConcreteCategory.hom
    (D.cuspOpenCoverHomologyComparison.boundary 1 ≫
      BinaryOpenCover.openIntersectionPullbackHomologyMap D.cuspToEllipticInteriorMap
        (orderThreeOpen D) (orderFourOpen D) 1 ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (orderThreeOpen D) (orderFourOpen D) 1).inv)

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData
