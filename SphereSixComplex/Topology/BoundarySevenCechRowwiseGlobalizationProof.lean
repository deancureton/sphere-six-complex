module

public import SphereSixComplex.Topology.FirstQuadrantRowwiseTotalizationProof
public import SphereSixComplex.Topology.BoundarySevenCechRowIdentificationsProof

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

/-- The boundary-seven rowwise globalization package exists without any additional
homological-algebra or coherence hypotheses. -/
public theorem boundarySevenCechRowwiseGlobalization_nonempty :
    Nonempty BoundarySevenCechRowwiseGlobalization :=
  ⟨boundarySevenCechRowwiseGlobalization⟩

end SphereSixComplex
