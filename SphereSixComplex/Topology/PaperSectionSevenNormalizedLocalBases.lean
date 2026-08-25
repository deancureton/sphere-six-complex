module

public import SphereSixComplex.Topology.PaperEllipticInteriorNormalizedSplitting
public import SphereSixComplex.Topology.PaperSectionSevenLocalHomologyBases

/-!
# Normalized local bases for the final Section 7 attachment

This module replaces the projectively chosen degree-two elliptic-interior basis by the basis
coming from an explicit swept-cycle section.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} {D : A.SectionSevenEllipticTwoDiscCoverData}

/-- The radial cusp model, corrected two-disc coordinates, and a swept-cycle section supply the
four local bases with a geometrically normalized elliptic degree-two coordinate. -/
public noncomputable def sectionSevenNormalizedCollarInteriorHomologyBases
    (R : A.CuspCollarRadialMappingTorusRealization)
    (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting
      (SectionSevenEllipticTwoDiscHomologyCoordinates.presentationTwo (D := D))) :
    A.SectionSevenCollarInteriorHomologyBases where
  cuspCollarOne := R.homologyOneEquiv
  ellipticInteriorOne := B.normalizedEllipticInteriorHomologyOneEquiv
  cuspCollarTwo := R.homologyTwoEquiv
  ellipticInteriorTwo := B.normalizedEllipticInteriorHomologyTwoEquiv S

end SphereSixComplex.Geometry.PaperAnalyticData

