module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineBandTrivialization
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticBandHomologyAlignment
public import SphereSixComplex.Paper.Topology.PaperSectionSevenPositiveDegreeCuspReduction
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangNaturalityInterface
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspEllipticInclusionNaturality

/-!
# Final affine reduction for the Section 7 assembly

The concrete affine height split and its central-band equivalence are now fixed.  This module
packages the exact remaining geometry into the two side equivalences and their compatibility
homotopies, then packages the remaining homology calculation into the three marked-coordinate
comparisons.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The fixed affine split used by the remaining Section 7 argument. -/
public noncomputable def actualAffineHeightSplit :
    A.CentralHeightSplit :=
  A.affineCentralHeightSplit A.affineCentralSeparation

/-- The exact remaining geometric input.  The central band field is absent because it is already
supplied by the established product trivialization over the affine strip. -/
public structure AffineRadialCompletionInput where
  orderThreeHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion A.actualAffineHeightSplit.orderThreeFillingSubspace
  orderFourHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion A.actualAffineHeightSplit.orderFourFillingSubspace
  orderThree_inclusion_compatibility :
    (((A.orderThreeFillingImageHomotopyEquiv.toFun.comp
      (orderThreeHomotopyEquivalence.toHomotopyEquiv.trans
        (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderThreeSide
          A.orderThreeFillingImage
          A.actualAffineHeightSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun).comp
        (IntegralMayerVietoris.interToLeft
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.actualAffineHeightSplit.allocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
          A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩ |>.comp
            (A.actualAffineHeightSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
              (A.affineCentralBandHomotopyEquiv
                A.affineCentralSeparation)).toFun)
  orderFour_inclusion_compatibility :
    (((A.orderFourFillingImageHomotopyEquiv.toFun.comp
      (orderFourHomotopyEquivalence.toHomotopyEquiv.trans
        (nestedSubtypeHomeomorph A.actualAffineHeightSplit.allocation.orderFourSide
          A.orderFourFillingImage
          A.actualAffineHeightSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun).comp
        (IntegralMayerVietoris.interToRight
          A.actualAffineHeightSplit.allocation.orderThreeSide
          A.actualAffineHeightSplit.allocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
          A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩ |>.comp
            (A.actualAffineHeightSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
              (A.affineCentralBandHomotopyEquiv
                A.affineCentralSeparation)).toFun)

namespace AffineRadialCompletionInput

variable {A : PaperAnalyticData}

/-- Assemble the actual affine radial input from the four remaining geometric facts. -/
public noncomputable def toRadialInput
    (R : A.AffineRadialCompletionInput) :
    A.actualAffineHeightSplit.RadialInput where
  orderThreeHomotopyEquivalence := R.orderThreeHomotopyEquivalence
  orderFourHomotopyEquivalence := R.orderFourHomotopyEquivalence
  bandHomotopyEquiv :=
    A.affineCentralBandHomotopyEquiv A.affineCentralSeparation
  orderThree_inclusion_compatibility := R.orderThree_inclusion_compatibility
  orderFour_inclusion_compatibility := R.orderFour_inclusion_compatibility

end AffineRadialCompletionInput

variable {A : PaperAnalyticData}

/-- The concrete two-disc cover determined by the completed affine radial geometry. -/
public noncomputable def AffineRadialCompletionInput.twoDiscCover
    (R : A.AffineRadialCompletionInput) :
    A.EllipticTwoDiscCoverData :=
  R.toRadialInput.toRadialRealization.toSectionSevenEllipticTwoDiscCoverData

/-- The canonical band homology alignment for the completed affine radial geometry. -/
public theorem AffineRadialCompletionInput.homologyAlignment
    (R : A.AffineRadialCompletionInput) :
    A.EllipticBandHomologyAlignment R.twoDiscCover :=
  R.toRadialInput.bandHomologyAlignment

/-- The exact three marked-coordinate comparisons remaining after the affine radial geometry has
been completed: one connecting square and two inclusion-coordinate identities. -/
public structure AffineMarkedCompletionInput
    (R : A.AffineRadialCompletionInput) : Prop where
  connectingNaturality :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment
  inclusionNaturality :
    R.twoDiscCover.SectionSevenCuspEllipticInclusionNaturality R.homologyAlignment
      (SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge
        R.homologyAlignment
        (R.twoDiscCover.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
          R.homologyAlignment connectingNaturality))

namespace AffineMarkedCompletionInput

variable {R : A.AffineRadialCompletionInput}

/-- The affine completion package supplies the production positive-degree assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.AffineMarkedCompletionInput R) :
    A.PositiveDegreeHomologyAssembly := by
  let boundary :=
    R.twoDiscCover.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
      R.homologyAlignment C.connectingNaturality
  let marked : R.twoDiscCover.SectionSevenPositiveDegreeActualMapInput R.homologyAlignment :=
    { boundary := boundary
      inclusion := C.inclusionNaturality }
  exact marked.positiveDegreeHomologyAssembly

end AffineMarkedCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData
