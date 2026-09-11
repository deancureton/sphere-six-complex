module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedStarRealPeriodBridge

/-!
# Uniqueness of the marked affine-strip lift

The regular-coordinate map is a covering map.  Consequently, a lift of the affine vertical
strip is determined by its value at the normalized midpoint.  This is the covering
space comparison needed to identify the base lift produced by the principal gauge with the
named lift used by the marked band trivialization.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open GlobalTorusFamily


/-- Midpoint normalization determines the marked strip lift. -/
public theorem AffineStripLift.eq_named_of_apply_midpoint
    {A : PaperAnalyticData} (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint) :
    L.lift = A.affineNamedStripLift.lift := by
  let U := A.existsUnique_sectionSevenAffineStripContinuousLift
    affineStripMidpoint A.affineNormalizedMidpoint
    A.affineNormalizedMidpoint_projects
  apply U.unique
  · exact ⟨hL, L.lift_comp_coordinate⟩
  · exact ⟨A.affineNamedStripLift_apply_midpoint,
      A.affineNamedStripLift.lift_comp_coordinate⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end
