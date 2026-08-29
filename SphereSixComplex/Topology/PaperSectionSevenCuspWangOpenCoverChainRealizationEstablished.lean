module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSlice

/-!
# Oriented chain comparison for the explicit cusp fibre slice

The full-fibre slice constructs the map from the actual cusp fibre into the intersection of the
pulled-back binary cover.  The remaining input is therefore reduced to two equalities for that
specific map: its period-marked identification with the elliptic band and the oriented
connecting-morphism comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- Restrict the cusp-to-elliptic map to the intersections of the two open covers. -/
public def cuspCoverIntersectionToEllipticOpensIntersectionMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (Opens.toTopCat (TopCat.of A.SectionSevenEllipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D)) where
  toFun := BinaryOpenCover.openIntersectionPreimageMap D.cuspToEllipticInteriorMap
    (orderThreeOpen D) (orderFourOpen D)
  continuous_toFun := (BinaryOpenCover.openIntersectionPreimageMap
    D.cuspToEllipticInteriorMap (orderThreeOpen D) (orderFourOpen D)).hom.continuous

/-- Forget the `Opens` presentation of the elliptic intersection. -/
public def ellipticOpensIntersectionToBandMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of A.SectionSevenEllipticInterior)).obj
        (orderThreeOpen D ⊓ orderFourOpen D),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :=
  ⟨(BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm,
    (BinaryOpenCover.opensIntersectionHomeomorph
      (orderThreeOpen D) (orderFourOpen D)).symm.continuous⟩

/-- The restriction of the cusp-to-elliptic map from the pulled-back cover intersection to the
elliptic band. -/
public def cuspCoverIntersectionToEllipticBandMap
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    C((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen),
      (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior)) :=
  D.ellipticOpensIntersectionToBandMap.comp
    D.cuspCoverIntersectionToEllipticOpensIntersectionMap

/-- The selected full-fibre slice, transported as an actual continuous map into the elliptic
band. -/
public noncomputable def actualCuspWangFibreToBandMap
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
        Set A.SectionSevenEllipticInterior)) := by
  let G := A.actualCuspRadialClutchingData
  letI := G.fiberTopology
  exact R.twoDiscCover.cuspCoverIntersectionToEllipticBandMap.comp
    (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)

/-- The categorical pullback/intersection comparison is induced by the literal restricted map. -/
public theorem cuspCoverIntersectionToEllipticBandHomologyOne_eq_map
    (D : A.SectionSevenEllipticTwoDiscCoverData) :
    D.cuspCoverIntersectionToEllipticBandHomologyOne =
      integralSingularHomologyMap 1 D.cuspCoverIntersectionToEllipticBandMap := by
  rw [cuspCoverIntersectionToEllipticBandHomologyOne,
    cuspCoverIntersectionToEllipticBandMap]
  exact (integralSingularHomologyMap_comp 1 _ _).symm

/-- The previously defined transported homology map is induced by the continuous band map. -/
public theorem actualCuspWangFibreToBandHomologyOne_eq_map
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspWangFibreToBandHomologyOne (A := A) R =
      integralSingularHomologyMap 1 (actualCuspWangFibreToBandMap (A := A) R) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [actualCuspWangFibreToBandMap, actualCuspWangFibreToBandHomologyOne,
    R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne_eq_map]
  exact (integralSingularHomologyMap_comp 1 _ _).symm

/-- The exact residual comparison for the constructed full-fibre slice.  The second equality
fixes the sign of the connecting morphism. -/
public structure ActualCuspWangFullFibreSliceComparison
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  fiberToBand_homology :
    R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
      actualCuspWangFibreToBandHomologyOne (A := A) R
  wangBoundary_eq_chainConnecting :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
        (actualCuspWangBoundaryHom A) =
      R.twoDiscCover.cuspOpenCoverConnectingHom

namespace EstablishedActualCuspWangOpenCoverChainRealization

/-- The period-marked and oriented chain comparison for the explicitly constructed full-fibre
slice. -/
public axiom fullFibreSliceComparison (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspWangFullFibreSliceComparison R

/-- The standard chain-level Wang theorem for the actual radial mapping-torus cut cover.  Its
content is the oriented realization of the established Wang connecting map by the explicit
short exact singular-chain sequence, before transport to the elliptic cover. -/
public noncomputable def realization (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.ActualCuspWangOpenCoverChainRealization :=
  actualCuspWangOpenCoverChainRealization_of_fullFibreSlice (A := A) R
    (fullFibreSliceComparison R).fiberToBand_homology
    (fullFibreSliceComparison R).wangBoundary_eq_chainConnecting

end EstablishedActualCuspWangOpenCoverChainRealization

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
