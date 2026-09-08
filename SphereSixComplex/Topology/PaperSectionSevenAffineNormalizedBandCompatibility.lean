module
public import SphereSixComplex.Topology.PaperSectionSevenAffineNormalizedCayleyBounds
public import SphereSixComplex.Topology.PaperSectionSevenAffineNamedSheetCompletion
@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData

public theorem actualMarkedBandHomotopies (A : PaperAnalyticData) :
    A.SectionSevenAffineOverlapBandCompatibility := by
  apply A.markedBandHomotopies_of_affineNamedSheetStabilizingDecks
  · intro x
    apply (A.exists_orderThree_stabilizingDeck_iff_namedCayley_lt x).mpr
    exact A.sectionSevenAffineNormalizedOrderThreeRadialLift_cayley
      (A.sectionSevenAffineBandStripCoordinate x)
  · intro x
    apply (A.exists_orderFour_stabilizingDeck_iff_namedCayley_lt x).mpr
    exact A.sectionSevenAffineNormalizedOrderFourRadialLift_cayley
      (A.sectionSevenAffineBandStripCoordinate x)

end SphereSixComplex.Geometry.PaperAnalyticData
