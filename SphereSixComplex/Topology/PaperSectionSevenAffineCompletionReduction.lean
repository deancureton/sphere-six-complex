module

public import SphereSixComplex.Geometry.PaperGluingDataReduction
public import SphereSixComplex.Topology.PaperSectionSevenAffineBandTrivialization
public import SphereSixComplex.Topology.PaperSectionSevenEllipticBandHomologyAlignment
public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeCuspReduction
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangNaturalityInterface
public import SphereSixComplex.Topology.PaperSectionSevenCuspEllipticInclusionNaturality

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
public noncomputable def sectionSevenActualAffineSplit :
    A.SectionSevenCentralHeightSplit :=
  A.sectionSevenAffineCentralHeightSplit A.sectionSevenAffineCentralSeparation

/-- The exact remaining geometric input.  The central band field is absent because it is already
supplied by the established product trivialization over the affine strip. -/
public structure SectionSevenAffineRadialCompletionInput where
  orderThreeHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion A.sectionSevenActualAffineSplit.orderThreeFillingSubspace
  orderFourHomotopyEquivalence :
    IsHomotopyEquivalenceInclusion A.sectionSevenActualAffineSplit.orderFourFillingSubspace
  orderThree_inclusion_compatibility :
    (((A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
      (orderThreeHomotopyEquivalence.toHomotopyEquiv.trans
        (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenOrderThreeFillingImage
          A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side).toHomotopyEquiv).toFun).comp
        (IntegralMayerVietoris.interToLeft
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenActualAffineSplit.allocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
          A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩ |>.comp
            (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
              (A.sectionSevenAffineCentralBandHomotopyEquiv
                A.sectionSevenAffineCentralSeparation)).toFun)
  orderFour_inclusion_compatibility :
    (((A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      (orderFourHomotopyEquivalence.toHomotopyEquiv.trans
        (nestedSubtypeHomeomorph A.sectionSevenActualAffineSplit.allocation.orderFourSide
          A.sectionSevenOrderFourFillingImage
          A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side).toHomotopyEquiv).toFun).comp
        (IntegralMayerVietoris.interToRight
          A.sectionSevenActualAffineSplit.allocation.orderThreeSide
          A.sectionSevenActualAffineSplit.allocation.orderFourSide))).Homotopic
      ((RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
          A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩ |>.comp
            (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.toHomotopyEquiv.trans
              (A.sectionSevenAffineCentralBandHomotopyEquiv
                A.sectionSevenAffineCentralSeparation)).toFun)

namespace SectionSevenAffineRadialCompletionInput

variable {A : PaperAnalyticData}

/-- Assemble the actual affine radial input from the four remaining geometric facts. -/
public noncomputable def toRadialInput
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.sectionSevenActualAffineSplit.RadialInput where
  orderThreeHomotopyEquivalence := R.orderThreeHomotopyEquivalence
  orderFourHomotopyEquivalence := R.orderFourHomotopyEquivalence
  bandHomotopyEquiv :=
    A.sectionSevenAffineCentralBandHomotopyEquiv A.sectionSevenAffineCentralSeparation
  orderThree_inclusion_compatibility := R.orderThree_inclusion_compatibility
  orderFour_inclusion_compatibility := R.orderFour_inclusion_compatibility

end SectionSevenAffineRadialCompletionInput

variable {A : PaperAnalyticData}

/-- The concrete two-disc cover determined by the completed affine radial geometry. -/
public noncomputable def SectionSevenAffineRadialCompletionInput.twoDiscCover
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.SectionSevenEllipticTwoDiscCoverData :=
  R.toRadialInput.toRadialRealization.toSectionSevenEllipticTwoDiscCoverData

/-- The canonical band homology alignment for the completed affine radial geometry. -/
public theorem SectionSevenAffineRadialCompletionInput.homologyAlignment
    (R : A.SectionSevenAffineRadialCompletionInput) :
    A.EllipticBandHomologyAlignment R.twoDiscCover :=
  R.toRadialInput.bandHomologyAlignment

/-- The exact three marked-coordinate comparisons remaining after the affine radial geometry has
been completed: one connecting square and two inclusion-coordinate identities. -/
public structure SectionSevenAffineMarkedCompletionInput
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop where
  connectingNaturality :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment
  inclusionNaturality :
    R.twoDiscCover.SectionSevenCuspEllipticInclusionNaturality R.homologyAlignment
      (SectionSevenCuspMarkedBoundaryComparison.pulledBackBoundaryBasisBridge
        R.homologyAlignment
        (R.twoDiscCover.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
          R.homologyAlignment connectingNaturality))

namespace SectionSevenAffineMarkedCompletionInput

variable {R : A.SectionSevenAffineRadialCompletionInput}

/-- The affine completion package supplies the production positive-degree assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.SectionSevenAffineMarkedCompletionInput R) :
    A.SectionSevenPositiveDegreeHomologyAssembly := by
  let boundary :=
    R.twoDiscCover.sectionSevenCuspMarkedBoundaryComparison_of_connectingNaturality
      R.homologyAlignment C.connectingNaturality
  let marked : R.twoDiscCover.SectionSevenPositiveDegreeActualMapInput R.homologyAlignment :=
    { boundary := boundary
      inclusion := C.inclusionNaturality }
  exact marked.positiveDegreeHomologyAssembly

/-- The four geometric facts and three marked-coordinate comparisons discharge the only
remaining construction obligation in `Final.lean`. -/
public theorem exists_paperGluingData
    {R : Geometry.establishedPaperAnalyticData.SectionSevenAffineRadialCompletionInput}
    (C : Geometry.establishedPaperAnalyticData.SectionSevenAffineMarkedCompletionInput R) :
    Nonempty PaperGluingData :=
  Geometry.exists_paperGluingData_of_positiveDegreeAssembly C.positiveDegreeHomologyAssembly

end SectionSevenAffineMarkedCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData
