module

public import SphereSixComplex.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Topology.PaperEllipticTwoDiscHomologyCoordinatesRealization
public import SphereSixComplex.Topology.PaperSectionSevenPositiveDegreeBases

/-!
# Local homology bases for the final Section 7 attachment

This module joins the Wang calculation for the actual cusp collar to the two-disc
Mayer--Vietoris calculation for the elliptic interior.  It introduces no additional homology or
map-identification hypothesis.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperAffineCyclicQuotientHomologyCoordinates

variable {A : PaperAnalyticData}

/-- A cusp mapping-torus realization and two-disc coordinates supply all four local bases needed
by the final attachment. -/
public noncomputable def sectionSevenCollarInteriorHomologyBases
    (R : A.CuspCollarRadialMappingTorusRealization)
    {D : A.SectionSevenEllipticTwoDiscCoverData}
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D) :
    A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := R.homologyOneEquiv
  ellipticInteriorOne := B.ellipticInteriorHomologyOneEquiv
  cuspCollarTwo := R.homologyTwoEquiv
  ellipticInteriorTwo := B.ellipticInteriorHomologyTwoEquiv

/-- The radial cusp realization, finite-cover calculations, and band-basis naturality supply the
four local bases without assuming either elliptic-interior homology group. -/
public noncomputable def sectionSevenCollarInteriorHomologyBasesOfEllipticRealization
    (R : A.CuspCollarRadialMappingTorusRealization)
    {D : A.SectionSevenEllipticTwoDiscCoverData}
    (F : EllipticFiniteCoverHomologyRealization A.periods)
    (N : A.EllipticBandHomologyAlignment D) :
    A.SectionSevenCollarInteriorHomologyBases :=
  A.sectionSevenCollarInteriorHomologyBases R (N.homologyCoordinates F)

end SphereSixComplex.Geometry.PaperAnalyticData
