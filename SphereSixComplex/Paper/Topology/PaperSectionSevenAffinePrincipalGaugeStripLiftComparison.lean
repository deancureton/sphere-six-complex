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

/-- Two continuous lifts of the same regular-coordinate map on the affine strip coincide once
they agree at one point. -/
public theorem regularCoordinate_lifts_eq_of_apply_eq
    {A : PaperAnalyticData}
    (f : C(affineVerticalStrip, regularCoordinateBase))
    (L₁ L₂ : C(affineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)))
    (a₀ : affineVerticalStrip)
    (h₁ : A.regularCoordinate ∘ L₁ = f)
    (h₂ : A.regularCoordinate ∘ L₂ = f)
    (h₀ : L₁ a₀ = L₂ a₀) :
    L₁ = L₂ := by
  let _ : LocallyPathConnectedSpace affineVerticalStrip :=
    affineVerticalStrip_isOpen.locallyPathConnectedSpace
  let _ : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  let _ : SimplyConnectedSpace affineVerticalStrip :=
    SimplyConnectedSpace.ofContractible _
  let U := A.regularCoordinate_isCoveringMap.existsUnique_continuousMap_lifts
    f a₀ (L₁ a₀) (by rw [← h₁]; rfl)
  apply U.unique
  · exact ⟨rfl, h₁⟩
  · exact ⟨h₀.symm, h₂⟩

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
