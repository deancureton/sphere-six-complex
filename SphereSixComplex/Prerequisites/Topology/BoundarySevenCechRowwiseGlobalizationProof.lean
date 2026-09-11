module

public import SphereSixComplex.Prerequisites.Topology.FirstQuadrantRowwiseTotalizationProof
public import SphereSixComplex.Prerequisites.Topology.BoundarySevenCechRowIdentificationsProof

/-!
# Concrete rowwise globalization for the boundary-seven Cech bicomplexes

This file combines the first-quadrant rowwise totalization theorem with the canonical
identifications of the actual Cech rows.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- The rowwise globalization package used by the boundary-seven low-assembly argument. -/
public noncomputable def boundarySevenCechRowwiseGlobalization :
    BoundarySevenCechRowwiseGlobalization where
  totalization := firstQuadrantRowwiseTotalization
  rowIdentifications := boundarySevenCechAugmentationRowIdentifications


end SphereSixComplex
