module

public import SphereSixComplex.Paper.Topology.PaperEllipticInteriorNormalizedSplitting
public import SphereSixComplex.Paper.Topology.PaperCuspCollarRadialMappingTorus
public import SphereSixComplex.Paper.Topology.PaperEllipticTwoDiscHomologyCoordinatesRealization
public import SphereSixComplex.Paper.Topology.PaperSectionSevenPositiveDegreeBases

/-!
# Normalized local bases for the final Section 7 attachment

This module replaces the projectively chosen degree-two elliptic-interior basis by the basis
coming from an explicit swept-cycle section.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData} {D : A.EllipticTwoDiscCoverData}

/-- The radial cusp model, corrected two-disc coordinates, and a swept-cycle section supply the
four local bases with a geometrically normalized elliptic degree-two coordinate. -/
public noncomputable def normalizedCollarInteriorHomologyBases
    (R : A.CuspCollarRadialMappingTorusRealization)
    (B : A.EllipticTwoDiscHomologyCoordinates D)
    (S : WangHomologyPresentation.NormalizedSplitting
      (EllipticTwoDiscHomologyCoordinates.presentationTwo (D := D))) :
    A.CollarInteriorHomologyBases where
  cuspCollarOne := R.homologyOneEquiv
  ellipticInteriorOne := B.normalizedEllipticInteriorHomologyOneEquiv
  cuspCollarTwo := R.homologyTwoEquiv
  ellipticInteriorTwo := B.normalizedEllipticInteriorHomologyTwoEquiv S

end SphereSixComplex.Geometry.PaperAnalyticData

