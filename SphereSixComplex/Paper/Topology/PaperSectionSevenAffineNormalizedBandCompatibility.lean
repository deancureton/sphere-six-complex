module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNormalizedCayleyBounds
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNamedSheetCompletion
@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.AnalyticData

public theorem homotopic_bandToReducedFiber_coverMap (A : AnalyticData) :
    (affineOrderThreeBandToReducedFiber
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
        A.orderThreeOverlapIsHomotopyEquivalence)).Homotopic
      (affineBandOrderThreeCoverMap A) ∧
    (affineOrderFourBandToReducedFiber
      (orderFourOverlapIsHomotopyEquivalence_inclusion
        A.orderFourOverlapIsHomotopyEquivalence)).Homotopic
      (affineBandOrderFourCoverMap A) := by
  apply A.homotopic_bandToReducedFiber_coverMap_of_stabilizingDecks
  · intro x
    apply (A.exists_orderThree_stabilizingDeck_iff_namedCayley_lt x).mpr
    exact A.affineNormalizedOrderThreeRadialLift_cayley
      (A.affineBandStripCoordinate x)
  · intro x
    apply (A.exists_orderFour_stabilizingDeck_iff_namedCayley_lt x).mpr
    exact A.affineNormalizedOrderFourRadialLift_cayley
      (A.affineBandStripCoordinate x)

end SphereSixComplex.Geometry.AnalyticData
