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
open EllipticInteriorMarkedCycleData
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.LatticeData SphereSixComplex.LatticeWangAlgebra
open SphereSixComplex.Topology.PaperCuspSpecializationAlgebra

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

public theorem cuspPulledBackBoundaryHom_apply (x) :
    D.cuspPulledBackBoundaryHom x = D.cuspPulledBackBoundary x :=
  rfl

/-- The pulled-back cusp-cover boundary, regarded as an invariant of the elliptic side
difference map. -/
public noncomputable def cuspPulledBackBoundaryInvariantHom :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      (presentationTwo (D := D)).invariants where
  toFun x := ⟨D.cuspPulledBackBoundary x, by
    rw [← D.canonicalBoundary_cuspToEllipticUnionHomology x,
      ← presentationTwo_boundary]
    exact (presentationTwo (D := D)).lowDifference_boundary
      (cuspToEllipticUnionHomology D 2 x)⟩
  map_zero' := by
    apply Subtype.ext
    change D.cuspPulledBackBoundaryHom 0 = 0
    exact map_zero D.cuspPulledBackBoundaryHom
  map_add' x y := by
    apply Subtype.ext
    change D.cuspPulledBackBoundaryHom (x + y) =
      D.cuspPulledBackBoundaryHom x + D.cuspPulledBackBoundaryHom y
    exact map_add D.cuspPulledBackBoundaryHom x y


/-- The integer coordinate of the pulled-back boundary after the elliptic intersection has been
oriented by the normalized two-disc computation. -/
public noncomputable def cuspPulledBackBoundaryCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+ ℤ :=
  N.actualHomologyCoordinates.degreeTwoInvariantEquiv.toAddEquiv.toAddMonoidHom.comp
    D.cuspPulledBackBoundaryInvariantHom

public theorem cuspPulledBackBoundaryCoordinateHom_apply
    (N : A.EllipticBandHomologyAlignment D) (x) :
    D.cuspPulledBackBoundaryCoordinateHom N x =
      N.actualHomologyCoordinates.degreeTwoInvariantEquiv
        (D.cuspPulledBackBoundaryInvariantHom x) :=
  rfl

/-- Pullback naturality identifies the new source-cover coordinate homomorphism with the
previously defined elliptic Mayer--Vietoris boundary coordinate. -/
public theorem cuspPulledBackBoundaryCoordinateHom_eq_cuspDegreeTwoBoundaryCoordinateHom
    (N : A.EllipticBandHomologyAlignment D) :
    D.cuspPulledBackBoundaryCoordinateHom N = cuspDegreeTwoBoundaryCoordinateHom N := by
  apply AddMonoidHom.ext
  intro x
  rw [D.cuspPulledBackBoundaryCoordinateHom_apply,
    cuspDegreeTwoBoundaryCoordinateHom_apply]
  congr 1
  apply Subtype.ext
  change D.cuspPulledBackBoundary x =
    (presentationTwo (D := D)).boundary (cuspToEllipticUnionHomology D 2 x)
  change D.cuspPulledBackBoundary x =
    canonicalBoundary D 1 (cuspToEllipticUnionHomology D 2 x)
  exact (D.canonicalBoundary_cuspToEllipticUnionHomology x).symm





/-- The elliptic invariant coordinate is the fourth marked coordinate of the boundary in the
actual band overlap. -/
public theorem cuspPulledBackBoundaryCoordinateHom_apply_eq_bandCoordinate
    (N : A.EllipticBandHomologyAlignment D)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    D.cuspPulledBackBoundaryCoordinateHom N x =
      N.actualHomologyCoordinates.bandOne (D.cuspPulledBackBoundary x) 3 := by
  rfl

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData
