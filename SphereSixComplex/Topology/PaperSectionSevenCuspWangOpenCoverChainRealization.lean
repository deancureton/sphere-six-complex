module

public import SphereSixComplex.Topology.PaperSectionSevenCuspFiberBandTopologicalSquare

/-!
# Chain realization of the cusp Wang boundary

The Wang presentation currently exposes its connecting morphism only as an opaque homology map.
The canonical pulled-back cusp cover, by contrast, has an explicit short exact sequence of
singular chain complexes.  This file isolates the precise realization statement identifying the
oriented Wang morphism with the connecting morphism of that chain sequence.  The final boundary
square is then derived from the chain realization and homotopy invariance.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} (D : A.SectionSevenEllipticTwoDiscCoverData)

namespace SectionSevenEllipticTwoDiscCoverData

/-- The map on first homology induced by transport from the pulled-back intersection to the
actual elliptic band. -/
public noncomputable def cuspCoverIntersectionToEllipticBandHomologyOne :
    IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
          (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen)) →+
      IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) :=
  ConcreteCategory.hom
    (BinaryOpenCover.openIntersectionPullbackHomologyMap D.cuspToEllipticInteriorMap
        (orderThreeOpen D) (orderFourOpen D) 1 ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (orderThreeOpen D) (orderFourOpen D) 1).inv)

/-- The connecting morphism of the explicit short exact chain sequence of the pulled-back cusp
cover, after the canonical generated-cover comparison. -/
public noncomputable def cuspOpenCoverConnectingHom :
    IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0) →+
      IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
          (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen)) :=
  ConcreteCategory.hom (D.cuspOpenCoverHomologyComparison.boundary 1)

/-- Transporting the chain connecting morphism is definitionally the pulled-back boundary used
in the Section 7 comparison. -/
public theorem cuspPulledBackBoundaryHom_eq_comp :
    D.cuspPulledBackBoundaryHom =
      D.cuspCoverIntersectionToEllipticBandHomologyOne.comp
        D.cuspOpenCoverConnectingHom := by
  ext x
  rfl

/-- A chain-level realization of the oriented Wang boundary in the explicit pulled-back cover.
The first field realizes the mapping-torus fibre inside the cover intersection.  The second says
that this geometric realization is the previously constructed period-marked band map.  The last
field identifies the opaque established Wang boundary with the connecting morphism produced by
`coverChainShortComplex`; it fixes the sign rather than merely asserting exactness. -/
public structure ActualCuspWangOpenCoverChainRealization where
  fiberToCuspCoverIntersectionMap :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    C(G.Fiber,
      (Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
        (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen))
  fiberToBand_homology :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    D.canonicalCuspFiberToBandHomologyOne =
      D.cuspCoverIntersectionToEllipticBandHomologyOne.comp
        (integralSingularHomologyMap 1 fiberToCuspCoverIntersectionMap)
  wangBoundary_eq_chainConnecting :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (integralSingularHomologyMap 1 fiberToCuspCoverIntersectionMap).comp
        (actualCuspWangBoundaryHom A) =
      D.cuspOpenCoverConnectingHom

namespace ActualCuspWangOpenCoverChainRealization

/-- The explicit chain realization implies the formerly axiomatized unmarked boundary square. -/
public theorem canonicalWangBoundaryNaturality
    (R : D.ActualCuspWangOpenCoverChainRealization) :
    D.CanonicalCuspWangBoundaryNaturality := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [CanonicalCuspWangBoundaryNaturality, R.fiberToBand_homology,
    AddMonoidHom.comp_assoc,
    R.wangBoundary_eq_chainConnecting, ← D.cuspPulledBackBoundaryHom_eq_comp]

/-- Naturality of the explicit short exact chain sequence under the cusp-to-elliptic cover map
identifies the elliptic Mayer--Vietoris boundary with the transported Wang boundary. -/
public theorem canonicalBoundary_cuspToElliptic_eq_wangBoundary
    (R : D.ActualCuspWangOpenCoverChainRealization)
    (x : IntegralSingularHomology 2 (A.openEmbeddingStarData.collarSource 0)) :
    canonicalBoundary D 1 (cuspToEllipticUnionHomology D 2 x) =
      D.canonicalCuspFiberToBandHomologyOne (actualCuspWangBoundaryHom A x) := by
  rw [D.canonicalBoundary_cuspToEllipticUnionHomology]
  exact (DFunLike.congr_fun R.canonicalWangBoundaryNaturality x).symm

end ActualCuspWangOpenCoverChainRealization

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
