module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineBandTrivialization
public import SphereSixComplex.Paper.Topology.PaperSectionSevenEllipticBandHomologyAlignment
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangNaturalityInterface
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspPullbackWangComparison

/-!
# The affine radial geometry and marked homology data

The actual height split is fixed. The dependent radial completion input supplies its two-disc
cover and the compatible marked homology alignment.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.EllipticFilling
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

variable (A : AnalyticData)

/-- The fixed affine split used by the remaining Section 7 argument. -/
public noncomputable def actualAffineHeightSplit :
    A.CentralHeightSplit :=
  A.affineCentralHeightSplit A.affineCentralSeparation

/-- The side equivalences and marked inclusion homotopies for the canonical affine band. -/
public abbrev AffineRadialCompletionInput :=
  A.actualAffineHeightSplit.RadialHomotopyData
    (A.affineCentralBandHomotopyEquiv A.affineCentralSeparation)

variable {A : AnalyticData}

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


end SphereSixComplex.Geometry.AnalyticData
