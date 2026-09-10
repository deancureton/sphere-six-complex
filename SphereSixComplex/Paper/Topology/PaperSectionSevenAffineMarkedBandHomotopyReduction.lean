module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedRetractionGeometry
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOverlapInterleaving

/-!
# Reduction of the marked affine band homotopies

The remaining marked-band assertion follows formally once the inclusion of the common band in
each affine side is homotopic, inside that side, to the marked central-fibre inclusion obtained
from the inverse of the side-to-fibre homotopy equivalence.  This module records that exact
geometric residue and proves the formal cancellation step.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable {A : PaperAnalyticData}

/-- The side-to-reduced-fibre equivalence selected from the proved order-three overlap
equivalence. -/
public noncomputable def affineOrderThreeSideToReducedFiberHomotopyEquiv
    (A : PaperAnalyticData) :
    A.actualAffineHeightSplit.allocation.orderThreeSide ≃ₕ
      OrderThreeReducedCentralFiber A.periods :=
  (orderThreeOverlapIsHomotopyEquivalence_inclusion
      A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv |>.trans
    (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
      A.orderThreeFillingImage
      A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv |>.trans
    A.orderThreeFillingImageHomotopyEquiv

/-- The side-to-reduced-fibre equivalence selected from the proved order-four overlap
equivalence. -/
public noncomputable def affineOrderFourSideToReducedFiberHomotopyEquiv
    (A : PaperAnalyticData) :
    A.actualAffineHeightSplit.allocation.orderFourSide ≃ₕ
      OrderFourReducedCentralFiber A.periods :=
  (orderFourOverlapIsHomotopyEquivalence_inclusion
      A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv |>.trans
    (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
      A.orderFourFillingImage
      A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv |>.trans
    A.orderFourFillingImageHomotopyEquiv

/-- The exact remaining side-level geometry.  Each common-band inclusion is deformed, within
the corresponding affine side, to the inverse image of its explicit marked finite-cover
projection. -/
public structure AffineMarkedBandSideContractions (A : PaperAnalyticData) where
  orderThree :
    (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).Homotopic
    ((affineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp
      (affineBandOrderThreeMarkedProjection A))
  orderFour :
    (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide).Homotopic
    ((affineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp
      (affineBandOrderFourMarkedProjection A))

/-- Cancelling a homotopy equivalence against its inverse turns a side-level marked contraction
into the required band-to-fibre homotopy. -/
private theorem homotopic_to_inverse_comp_implies_forward_comp_homotopic
    {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (j : C(B, X)) (p : C(B, Y))
    (h : j.Homotopic (e.invFun.comp p)) :
    (e.toFun.comp j).Homotopic p := by
  exact (ContinuousMap.Homotopic.comp (.refl e.toFun) h).trans
    (ContinuousMap.Homotopic.comp e.right_inv (.refl p))

/-- Conversely, a band-to-fibre homotopy can be lifted back to the side by the inverse of the
same homotopy equivalence. -/
private theorem forward_comp_homotopic_implies_homotopic_to_inverse_comp
    {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (j : C(B, X)) (p : C(B, Y))
    (h : (e.toFun.comp j).Homotopic p) :
    j.Homotopic (e.invFun.comp p) := by
  exact (ContinuousMap.Homotopic.comp e.left_inv (.refl j)).symm.trans
    (ContinuousMap.Homotopic.comp (.refl e.invFun) h)

/-- The two exact side-level contractions imply the paper's residual marked-band assertion,
with no additional topological assumptions. -/
public theorem markedBandHomotopies_of_sideContractions
    (A : PaperAnalyticData) (H : A.AffineMarkedBandSideContractions) :
    A.AffineOverlapBandCompatibility := by
  refine { orderThree := ?_, orderFour := ?_ }
  · rw [← affineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact homotopic_to_inverse_comp_implies_forward_comp_homotopic
      (affineOrderThreeSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToLeft
        A.actualAffineHeightSplit.allocation.orderThreeSide
        A.actualAffineHeightSplit.allocation.orderFourSide)
      (affineBandOrderThreeMarkedProjection A) H.orderThree
  · rw [← affineBandOrderFourMarkedProjection_eq_coverMap A]
    exact homotopic_to_inverse_comp_implies_forward_comp_homotopic
      (affineOrderFourSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToRight
        A.actualAffineHeightSplit.allocation.orderThreeSide
        A.actualAffineHeightSplit.allocation.orderFourSide)
      (affineBandOrderFourMarkedProjection A) H.orderFour

/-- The reduction is exact: the original residual marked-band package also recovers the two
side-level marked contractions. -/
public theorem sideContractions_of_markedBandHomotopies
    (A : PaperAnalyticData) (H : A.AffineOverlapBandCompatibility) :
    A.AffineMarkedBandSideContractions := by
  refine { orderThree := ?_, orderFour := ?_ }
  · rw [affineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact forward_comp_homotopic_implies_homotopic_to_inverse_comp
      (affineOrderThreeSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToLeft
        A.actualAffineHeightSplit.allocation.orderThreeSide
        A.actualAffineHeightSplit.allocation.orderFourSide)
      (affineBandOrderThreeCoverMap A) H.orderThree
  · rw [affineBandOrderFourMarkedProjection_eq_coverMap A]
    exact forward_comp_homotopic_implies_homotopic_to_inverse_comp
      (affineOrderFourSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToRight
        A.actualAffineHeightSplit.allocation.orderThreeSide
        A.actualAffineHeightSplit.allocation.orderFourSide)
      (affineBandOrderFourCoverMap A) H.orderFour

end SphereSixComplex.Geometry.PaperAnalyticData

end
