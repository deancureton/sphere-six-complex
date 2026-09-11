module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspFiberBandTopologicalSquare

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

open EllipticTwoDiscHomologyCoordinates

variable {A : PaperAnalyticData} (D : A.EllipticTwoDiscCoverData)

namespace EllipticTwoDiscCoverData

/-- The map on first homology induced by transport from the pulled-back intersection to the
actual elliptic band. -/
public noncomputable def cuspCoverIntersectionToEllipticBandHomologyOne :
    IntegralSingularHomology 1
        ((Opens.toTopCat (TopCat.of (A.openEmbeddingStarData.collarSource 0))).obj
          (D.cuspOrderThreeOpen ⊓ D.cuspOrderFourOpen)) →+
      IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior) :=
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


end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
