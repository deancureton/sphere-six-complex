module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNormalizedCayleyBounds
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNamedSheetCompletion
@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData

public theorem actualMarkedBandHomotopies (A : PaperAnalyticData) :
    A.AffineOverlapBandCompatibility := by
  apply A.markedBandHomotopies_of_affineNamedSheetStabilizingDecks
  · intro x
    apply (A.exists_orderThree_stabilizingDeck_iff_namedCayley_lt x).mpr
    exact A.affineNormalizedOrderThreeRadialLift_cayley
      (A.affineBandStripCoordinate x)
  · intro x
    apply (A.exists_orderFour_stabilizingDeck_iff_namedCayley_lt x).mpr
    exact A.affineNormalizedOrderFourRadialLift_cayley
      (A.affineBandStripCoordinate x)

end SphereSixComplex.Geometry.PaperAnalyticData
