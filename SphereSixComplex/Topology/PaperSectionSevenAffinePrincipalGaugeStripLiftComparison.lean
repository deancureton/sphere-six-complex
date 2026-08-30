module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedStarRealPeriodBridge

/-!
# Uniqueness of the marked affine-strip lift

The regular-coordinate map is a covering map.  Consequently, a lift of the affine vertical
strip is determined by its value at the selected actual cusp crossing.  This is the covering
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
    (f : C(sectionSevenAffineVerticalStrip, RegularCoordinateBase))
    (L₁ L₂ : C(sectionSevenAffineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)))
    (a₀ : sectionSevenAffineVerticalStrip)
    (h₁ : A.regularCoordinate ∘ L₁ = f)
    (h₂ : A.regularCoordinate ∘ L₂ = f)
    (h₀ : L₁ a₀ = L₂ a₀) :
    L₁ = L₂ := by
  let _ : LocallyPathConnectedSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStrip_isOpen.locallyPathConnectedSpace
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  let _ : SimplyConnectedSpace sectionSevenAffineVerticalStrip :=
    SimplyConnectedSpace.ofContractible _
  let U := A.regularCoordinate_isCoveringMap.existsUnique_continuousMap_lifts
    f a₀ (L₁ a₀) (by rw [← h₁]; rfl)
  apply U.unique
  · exact ⟨rfl, h₁⟩
  · exact ⟨h₀.symm, h₂⟩

/-- Any affine-strip lift through the selected actual cusp representative is the named marked
lift. -/
public theorem SectionSevenAffineStripLift.eq_named_of_apply_actualCuspCrossing
    {A : PaperAnalyticData} (L : A.SectionSevenAffineStripLift)
    (hL : L.lift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint
        A.sectionSevenAffineActualCuspCrossingTime) :
    L.lift = A.sectionSevenAffineNamedStripLift.lift := by
  let U := A.existsUnique_sectionSevenAffineStripContinuousLift
    A.sectionSevenAffineActualCuspCrossingPoint
    (A.actualCuspAngularRegularBasePoint
      A.sectionSevenAffineActualCuspCrossingTime)
    A.regularCoordinate_actualCuspAngularRegularBasePoint_crossing
  apply U.unique
  · exact ⟨hL, L.lift_comp_coordinate⟩
  · exact ⟨A.sectionSevenAffineNamedStripLift_apply_actualCuspCrossing,
      A.sectionSevenAffineNamedStripLift.lift_comp_coordinate⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end
