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

/-- The side equivalences and marked inclusion homotopies for the canonical affine band. -/
public abbrev AffineRadialCompletionInput :=
  A.actualAffineHeightSplit.RadialHomotopyData
    (A.affineCentralBandHomotopyEquiv A.affineCentralSeparation)

variable {A : PaperAnalyticData}

/-- The concrete two-disc cover determined by the completed affine radial geometry. -/
public noncomputable def AffineRadialCompletionInput.twoDiscCover
    (R : A.AffineRadialCompletionInput) :
    A.EllipticTwoDiscCoverData :=
  R.toRadialRealization.toSectionSevenEllipticTwoDiscCoverData

/-- The canonical band homology alignment for the completed affine radial geometry. -/
public theorem AffineRadialCompletionInput.homologyAlignment
    (R : A.AffineRadialCompletionInput) :
    A.EllipticBandHomologyAlignment R.twoDiscCover :=
  R.bandHomologyAlignment

/-- The exact three marked-coordinate comparisons remaining after the affine radial geometry has
been completed: one connecting square and two inclusion-coordinate identities. -/
public structure AffineMarkedCompletionInput
    (R : A.AffineRadialCompletionInput) : Prop where
  connectingNaturality :
    (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
        R.twoDiscCover.cuspPulledBackBoundaryHom =
      (EllipticTwoDiscCoverData.actualCuspFiberFourthCoordinateHom A).comp
        (EllipticTwoDiscCoverData.actualCuspWangBoundaryHom A)
  inclusionNaturality :
    R.twoDiscCover.SectionSevenCuspEllipticInclusionNaturality R.homologyAlignment
      (EllipticTwoDiscCoverData.boundaryBasisBridge_of_coordinate_eq
        R.homologyAlignment
        (R.twoDiscCover.boundaryCoordinate_eq_of_connecting_eq
          R.homologyAlignment connectingNaturality))

namespace AffineMarkedCompletionInput

variable {R : A.AffineRadialCompletionInput}

/-- The affine completion package supplies the production positive-degree assembly. -/
public noncomputable def positiveDegreeHomologyAssembly
    (C : A.AffineMarkedCompletionInput R) :
    A.PositiveDegreeHomologyAssembly := by
  let boundary :=
    R.twoDiscCover.boundaryCoordinate_eq_of_connecting_eq
      R.homologyAlignment C.connectingNaturality
  let marked : R.twoDiscCover.SectionSevenPositiveDegreeActualMapInput R.homologyAlignment :=
    { boundary := boundary
      inclusion := C.inclusionNaturality }
  exact marked.positiveDegreeHomologyAssembly

end AffineMarkedCompletionInput

end SphereSixComplex.Geometry.PaperAnalyticData
