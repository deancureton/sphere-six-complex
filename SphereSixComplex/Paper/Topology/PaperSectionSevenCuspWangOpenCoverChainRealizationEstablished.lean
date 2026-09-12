module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares

/-!
# Oriented chain comparison for the explicit cusp fibre slice

The full-fibre slice constructs the map from the actual cusp fibre into the intersection of the
pulled-back binary cover.  The remaining input is therefore reduced to two equalities for that
specific map: its period-marked identification with the elliptic band and the oriented
connecting-morphism comparison. The band identification here requires explicit crossing-marking
agreement; it is not inferred from the normalized strip marking.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open EllipticTwoDiscHomologyCoordinates
open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily

variable {A : AnalyticData}

namespace EllipticTwoDiscCoverData

/-- Restrict the cusp-to-elliptic map to the intersections of the two open covers. -/
public def cuspCoverIntersectionToEllipticOpensIntersectionMap
    (D : A.EllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (Opens.toTopCat (TopCat.of A.ellipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D)) where
  toFun := BinaryOpenCover.openIntersectionPreimageMap D.cuspToEllipticInteriorMap
    (orderThreeOpen D) (orderFourOpen D)
  continuous_toFun := (BinaryOpenCover.openIntersectionPreimageMap
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)).hom.continuous

/-- Forget the `Opens` presentation of the elliptic intersection. -/
public def ellipticOpensIntersectionToBandMap
    (D : A.EllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of A.ellipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :=
  ⟨(BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm,
    (BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm.continuous⟩

/-- The restriction of the cusp-to-elliptic map from the pulled-back cover intersection to the
elliptic band. -/
public def cuspCoverIntersectionToEllipticBandMap
    (D : A.EllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior)) :=
  D.ellipticOpensIntersectionToBandMap.comp
    D.cuspCoverIntersectionToEllipticOpensIntersectionMap

/-- The selected full-fibre slice, transported as an actual continuous map into the elliptic
band. -/
public noncomputable def actualCuspWangFiberToBandMap
    (R : A.AffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
        Set A.ellipticInterior)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandMap.comp
    (actualCuspWangFiberToCuspCoverIntersectionMap (A := A) R)







end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData
