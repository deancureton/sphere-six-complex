module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineBandTrivialization
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticBandHomologyAlignment
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


end SphereSixComplex.Geometry.PaperAnalyticData
