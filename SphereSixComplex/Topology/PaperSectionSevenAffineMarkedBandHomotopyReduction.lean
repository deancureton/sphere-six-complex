module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedRetractionGeometry
public import SphereSixComplex.Topology.PaperSectionSevenAffineOverlapInterleaving

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
public noncomputable def sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv
    (A : PaperAnalyticData) :
    A.sectionSevenActualAffineSplit.allocation.orderThreeSide ≃ₕ
      OrderThreeReducedCentralFiber A.periods :=
  (orderThreeOverlapIsHomotopyEquivalence_inclusion
      A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv |>.trans
    (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenOrderThreeFillingImage
      A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv |>.trans
    A.sectionSevenOrderThreeFillingImageHomotopyEquiv

/-- The side-to-reduced-fibre equivalence selected from the proved order-four overlap
equivalence. -/
public noncomputable def sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv
    (A : PaperAnalyticData) :
    A.sectionSevenActualAffineSplit.allocation.orderFourSide ≃ₕ
      OrderFourReducedCentralFiber A.periods :=
  (orderFourOverlapIsHomotopyEquivalence_inclusion
      A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv |>.trans
    (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderFourSide
      A.sectionSevenOrderFourFillingImage
      A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv |>.trans
    A.sectionSevenOrderFourFillingImageHomotopyEquiv

/-- The exact remaining side-level geometry.  Each common-band inclusion is deformed, within
the corresponding affine side, to the inverse image of its explicit marked finite-cover
projection. -/
public structure SectionSevenAffineMarkedBandSideContractions (A : PaperAnalyticData) where
  orderThree :
    (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide).Homotopic
    ((sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp
      (sectionSevenAffineBandOrderThreeMarkedProjection A))
  orderFour :
    (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide).Homotopic
    ((sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp
      (sectionSevenAffineBandOrderFourMarkedProjection A))

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
    (A : PaperAnalyticData) (H : A.SectionSevenAffineMarkedBandSideContractions) :
    A.SectionSevenAffineOverlapBandCompatibility := by
  refine { orderThree := ?_, orderFour := ?_ }
  · rw [← sectionSevenAffineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact homotopic_to_inverse_comp_implies_forward_comp_homotopic
      (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToLeft
        A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenActualAffineSplit.allocation.orderFourSide)
      (sectionSevenAffineBandOrderThreeMarkedProjection A) H.orderThree
  · rw [← sectionSevenAffineBandOrderFourMarkedProjection_eq_coverMap A]
    exact homotopic_to_inverse_comp_implies_forward_comp_homotopic
      (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToRight
        A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenActualAffineSplit.allocation.orderFourSide)
      (sectionSevenAffineBandOrderFourMarkedProjection A) H.orderFour

/-- The reduction is exact: the original residual marked-band package also recovers the two
side-level marked contractions. -/
public theorem sideContractions_of_markedBandHomotopies
    (A : PaperAnalyticData) (H : A.SectionSevenAffineOverlapBandCompatibility) :
    A.SectionSevenAffineMarkedBandSideContractions := by
  refine { orderThree := ?_, orderFour := ?_ }
  · rw [sectionSevenAffineBandOrderThreeMarkedProjection_eq_coverMap A]
    exact forward_comp_homotopic_implies_homotopic_to_inverse_comp
      (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToLeft
        A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenActualAffineSplit.allocation.orderFourSide)
      (sectionSevenAffineBandOrderThreeCoverMap A) H.orderThree
  · rw [sectionSevenAffineBandOrderFourMarkedProjection_eq_coverMap A]
    exact forward_comp_homotopic_implies_homotopic_to_inverse_comp
      (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A)
      (IntegralMayerVietoris.interToRight
        A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenActualAffineSplit.allocation.orderFourSide)
      (sectionSevenAffineBandOrderFourCoverMap A) H.orderFour

end SphereSixComplex.Geometry.PaperAnalyticData

end
