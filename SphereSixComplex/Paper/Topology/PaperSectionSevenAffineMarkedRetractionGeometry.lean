module

public import SphereSixComplex.Prerequisites.Topology.StrongDeformationRetraction
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedProjectionSquaresProof

/-!
# Marked affine side retractions

The affine side inclusions have many homotopy inverses, but any two are homotopic.  This module
separates that formal choice from the paper-specific geometric assertion: it is enough to exhibit
one inverse on each side whose restriction to the named central band gives the corresponding
marked finite-cover projection.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

variable {A : PaperAnalyticData}

/-- The order-three band map associated to a specified inverse of the side inclusion. -/
public noncomputable def affineOrderThreeBandMapOfRetraction
    (E : A.actualAffineHeightSplit.allocation.orderThreeSide ≃ₕ
      A.actualAffineHeightSplit.orderThreeFillingSubspace) :=
  (A.orderThreeFillingImageHomotopyEquiv.toFun.comp
    (E.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
        A.orderThreeFillingImage
        A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The order-four band map associated to a specified inverse of the side inclusion. -/
public noncomputable def affineOrderFourBandMapOfRetraction
    (E : A.actualAffineHeightSplit.allocation.orderFourSide ≃ₕ
      A.actualAffineHeightSplit.orderFourFillingSubspace) :=
  (A.orderFourFillingImageHomotopyEquiv.toFun.comp
    (E.trans
      (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
        A.orderFourFillingImage
        A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide)

/-- The proposition-selected order-three band map is the map of its selected inverse. -/
public theorem affineOrderThreeBandToReducedFiber_eq_bandMapOfRetraction
    (h : IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderThreeFillingSubspace) :
    affineOrderThreeBandToReducedFiber h =
      affineOrderThreeBandMapOfRetraction h.toHomotopyEquiv :=
  rfl

/-- The proposition-selected order-four band map is the map of its selected inverse. -/
public theorem affineOrderFourBandToReducedFiber_eq_bandMapOfRetraction
    (h : IsHomotopyEquivalenceInclusion
      A.actualAffineHeightSplit.orderFourFillingSubspace) :
    affineOrderFourBandToReducedFiber h =
      affineOrderFourBandMapOfRetraction h.toHomotopyEquiv :=
  rfl

/-- Changing the chosen inverse of the order-three side inclusion by a homotopy changes the
induced band map by a homotopy. -/
public theorem affineOrderThreeBandMapOfRetraction_homotopic
    {E F : A.actualAffineHeightSplit.allocation.orderThreeSide ≃ₕ
      A.actualAffineHeightSplit.orderThreeFillingSubspace}
    (h : E.toFun.Homotopic F.toFun) :
    (affineOrderThreeBandMapOfRetraction E).Homotopic
      (affineOrderThreeBandMapOfRetraction F) := by
  exact ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.comp
      (.refl A.orderThreeFillingImageHomotopyEquiv.toFun)
      (ContinuousMap.Homotopic.comp
        (.refl (nestedSubtypeHomeomorph
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.orderThreeFillingImage
          A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv.toFun)
        h))
    (.refl (IntegralMayerVietoris.interToLeft
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide))

/-- Changing the chosen inverse of the order-four side inclusion by a homotopy changes the
induced band map by a homotopy. -/
public theorem affineOrderFourBandMapOfRetraction_homotopic
    {E F : A.actualAffineHeightSplit.allocation.orderFourSide ≃ₕ
      A.actualAffineHeightSplit.orderFourFillingSubspace}
    (h : E.toFun.Homotopic F.toFun) :
    (affineOrderFourBandMapOfRetraction E).Homotopic
      (affineOrderFourBandMapOfRetraction F) := by
  exact ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.comp
      (.refl A.orderFourFillingImageHomotopyEquiv.toFun)
      (ContinuousMap.Homotopic.comp
        (.refl (nestedSubtypeHomeomorph
          A.actualAffineHeightSplit.allocation.orderFourSide
          A.orderFourFillingImage
          A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv.toFun)
        h))
    (.refl (IntegralMayerVietoris.interToRight
      A.actualAffineHeightSplit.allocation.orderThreeSide
      A.actualAffineHeightSplit.allocation.orderFourSide))

/-- One geometrically marked inverse of the order-three side inclusion. -/
public structure AffineOrderThreeMarkedRetractionInput where
  retraction : A.actualAffineHeightSplit.allocation.orderThreeSide ≃ₕ
    A.actualAffineHeightSplit.orderThreeFillingSubspace
  invFun_eq : retraction.invFun =
    topologicalSubsetInclusionMap A.actualAffineHeightSplit.orderThreeFillingSubspace
  markedSquare :
    (affineOrderThreeBandMapOfRetraction retraction).Homotopic
      (affineBandOrderThreeMarkedProjection A)

/-- One geometrically marked inverse of the order-four side inclusion. -/
public structure AffineOrderFourMarkedRetractionInput where
  retraction : A.actualAffineHeightSplit.allocation.orderFourSide ≃ₕ
    A.actualAffineHeightSplit.orderFourFillingSubspace
  invFun_eq : retraction.invFun =
    topologicalSubsetInclusionMap A.actualAffineHeightSplit.orderFourFillingSubspace
  markedSquare :
    (affineOrderFourBandMapOfRetraction retraction).Homotopic
      (affineBandOrderFourMarkedProjection A)

/-- The two paper-specific marked retractions.  All dependence on Lean's selected homotopy
inverses is removed by homotopy-inverse uniqueness. -/
public structure AffineMarkedRetractionInput where
  orderThree : A.AffineOrderThreeMarkedRetractionInput
  orderFour : A.AffineOrderFourMarkedRetractionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
