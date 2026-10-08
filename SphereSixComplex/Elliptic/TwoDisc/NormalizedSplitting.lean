module

public import SphereSixComplex.Cusp.Specialization.Coordinates
public import SphereSixComplex.Elliptic.TwoDisc.HomologyCoordinates

/-! # The cusp inclusion into the elliptic Mayer–Vietoris union -/

@[expose] public section

noncomputable section

open AlgebraicTopology Set

namespace SphereSixComplex.Geometry.AnalyticData

variable {A : AnalyticData}

namespace EllipticTwoDiscHomologyCoordinates

/-- Pull the actual cusp-collar inclusion into the literal union used by the elliptic
Mayer--Vietoris presentation. -/
public noncomputable def cuspToEllipticUnionHomology
    (D : A.EllipticTwoDiscCoverData) (k : ℕ)
    (x : IntegralSingularHomology k (A.openEmbeddingStarData.collarSource 0)) :
    IntegralSingularHomology k
        (D.orderThreeSide ∪ D.orderFourSide : Set A.ellipticInterior) :=
  (integralSingularHomologyEquiv k
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.ellipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)).symm
    (integralSingularHomologyMap k
      (IntegralMayerVietoris.interToLeft
        ((A.openEmbeddingStarData.mayerVietorisCover).stage (2 : Fin 4))
        ((A.openEmbeddingStarData.mayerVietorisCover).piece 3))
      (integralSingularHomologyEquiv k
        A.cuspCollarToFinalOverlapHomeomorph x))

end EllipticTwoDiscHomologyCoordinates

end SphereSixComplex.Geometry.AnalyticData
