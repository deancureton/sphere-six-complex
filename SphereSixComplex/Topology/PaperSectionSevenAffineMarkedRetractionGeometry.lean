module

public import SphereSixComplex.Topology.EstablishedStrongDeformationRetracts
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedProjectionSquaresProof

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
public noncomputable def sectionSevenAffineOrderThreeBandMapOfRetraction
    (E : A.sectionSevenActualAffineSplit.allocation.orderThreeSide ≃ₕ
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace) :=
  (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
    (E.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderThreeSide
        A.sectionSevenOrderThreeFillingImage
        A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The order-four band map associated to a specified inverse of the side inclusion. -/
public noncomputable def sectionSevenAffineOrderFourBandMapOfRetraction
    (E : A.sectionSevenActualAffineSplit.allocation.orderFourSide ≃ₕ
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace) :=
  (A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
    (E.trans
      (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderFourSide
        A.sectionSevenOrderFourFillingImage
        A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun)
    |>.comp (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide)

/-- The proposition-selected order-three band map is the map of its selected inverse. -/
public theorem sectionSevenAffineOrderThreeBandToReducedFiber_eq_bandMapOfRetraction
    (h : IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace) :
    sectionSevenAffineOrderThreeBandToReducedFiber h =
      sectionSevenAffineOrderThreeBandMapOfRetraction h.toHomotopyEquiv :=
  rfl

/-- The proposition-selected order-four band map is the map of its selected inverse. -/
public theorem sectionSevenAffineOrderFourBandToReducedFiber_eq_bandMapOfRetraction
    (h : IsHomotopyEquivalenceInclusion
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace) :
    sectionSevenAffineOrderFourBandToReducedFiber h =
      sectionSevenAffineOrderFourBandMapOfRetraction h.toHomotopyEquiv :=
  rfl

/-- Changing the chosen inverse of the order-three side inclusion by a homotopy changes the
induced band map by a homotopy. -/
public theorem sectionSevenAffineOrderThreeBandMapOfRetraction_homotopic
    {E F : A.sectionSevenActualAffineSplit.allocation.orderThreeSide ≃ₕ
      A.sectionSevenActualAffineSplit.orderThreeFillingSubspace}
    (h : E.toFun.Homotopic F.toFun) :
    (sectionSevenAffineOrderThreeBandMapOfRetraction E).Homotopic
      (sectionSevenAffineOrderThreeBandMapOfRetraction F) := by
  exact ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.comp
      (.refl A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun)
      (ContinuousMap.Homotopic.comp
        (.refl (nestedSubtypeHomeomorph
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenOrderThreeFillingImage
          A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv.toFun)
        h))
    (.refl (IntegralMayerVietoris.interToLeft
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide))

/-- Changing the chosen inverse of the order-four side inclusion by a homotopy changes the
induced band map by a homotopy. -/
public theorem sectionSevenAffineOrderFourBandMapOfRetraction_homotopic
    {E F : A.sectionSevenActualAffineSplit.allocation.orderFourSide ≃ₕ
      A.sectionSevenActualAffineSplit.orderFourFillingSubspace}
    (h : E.toFun.Homotopic F.toFun) :
    (sectionSevenAffineOrderFourBandMapOfRetraction E).Homotopic
      (sectionSevenAffineOrderFourBandMapOfRetraction F) := by
  exact ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.comp
      (.refl A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun)
      (ContinuousMap.Homotopic.comp
        (.refl (nestedSubtypeHomeomorph
          A.sectionSevenActualAffineSplit.allocation.orderFourSide
          A.sectionSevenOrderFourFillingImage
          A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv.toFun)
        h))
    (.refl (IntegralMayerVietoris.interToRight
      A.sectionSevenActualAffineSplit.allocation.orderThreeSide
      A.sectionSevenActualAffineSplit.allocation.orderFourSide))

/-- One geometrically marked inverse of the order-three side inclusion. -/
public structure SectionSevenAffineOrderThreeMarkedRetractionInput where
  retraction : A.sectionSevenActualAffineSplit.allocation.orderThreeSide ≃ₕ
    A.sectionSevenActualAffineSplit.orderThreeFillingSubspace
  invFun_eq : retraction.invFun =
    topologicalSubsetInclusionMap A.sectionSevenActualAffineSplit.orderThreeFillingSubspace
  markedSquare :
    (sectionSevenAffineOrderThreeBandMapOfRetraction retraction).Homotopic
      (sectionSevenAffineBandOrderThreeMarkedProjection A)

/-- One geometrically marked inverse of the order-four side inclusion. -/
public structure SectionSevenAffineOrderFourMarkedRetractionInput where
  retraction : A.sectionSevenActualAffineSplit.allocation.orderFourSide ≃ₕ
    A.sectionSevenActualAffineSplit.orderFourFillingSubspace
  invFun_eq : retraction.invFun =
    topologicalSubsetInclusionMap A.sectionSevenActualAffineSplit.orderFourFillingSubspace
  markedSquare :
    (sectionSevenAffineOrderFourBandMapOfRetraction retraction).Homotopic
      (sectionSevenAffineBandOrderFourMarkedProjection A)

/-- The two paper-specific marked retractions.  All dependence on Lean's selected homotopy
inverses is removed by homotopy-inverse uniqueness. -/
public structure SectionSevenAffineMarkedRetractionInput where
  orderThree : A.SectionSevenAffineOrderThreeMarkedRetractionInput
  orderFour : A.SectionSevenAffineOrderFourMarkedRetractionInput

end SphereSixComplex.Geometry.PaperAnalyticData

end
