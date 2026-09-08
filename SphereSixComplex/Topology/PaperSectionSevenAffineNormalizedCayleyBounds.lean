module
public import SphereSixComplex.Topology.PaperSectionSevenAffineNormalizedStripLift
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandEndpointFormula
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularBaseRadialEquivalence
public import SphereSixComplex.Topology.PaperEllipticPathSheet
/-!
# Identity-collar bounds for the normalized affine strip

Radial normalization preserves the exact generator labels of the midpoint meridians.
Collar separation forces those radial paths into the identity collar; connectedness then
extends the bound along the entire lifted strip.
-/

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open GlobalTorusFamily EquivariantQuotientHomeomorph EllipticCayleyHomeomorph
open EllipticLinearCollarGlobalDescent

public def sectionSevenAffineNormalizedOrderThreeHalfPlaneLift (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, A.orderThreeAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.sectionSevenAffineNormalizedStripContinuousLift z, by
      change (A.regularCoordinate (A.sectionSevenAffineNormalizedStripContinuousLift z)).1.re < 2 / 3
      have h := congrArg Subtype.val
        (congrFun A.sectionSevenAffineNormalizedStripContinuousLift_coordinate z)
      change (A.regularCoordinate (A.sectionSevenAffineNormalizedStripContinuousLift z)).1 = z.1 at h
      rw [h]
      exact z.2.2⟩,
    A.sectionSevenAffineNormalizedStripContinuousLift.continuous.subtype_mk _⟩

public def sectionSevenAffineNormalizedOrderThreeRadialLift (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      A.orderThreeAffineDiscBaseLift A.sectionSevenAffineOrderThreeMarkedDiscRadius) :=
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderThreeBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr).invFun.comp
      A.sectionSevenAffineNormalizedOrderThreeHalfPlaneLift

public theorem sectionSevenAffineNormalizedOrderThreeRadialLift_midpoint_cayley
    (A : PaperAnalyticData) :
    ‖(orderThreeCayleyHomeomorph
      (A.sectionSevenAffineNormalizedOrderThreeRadialLift sectionSevenAffineStripMidpoint).1.1 : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
  let Q := A.sectionSevenAffineNormalizedZeroLift
  have hQhalf (t : unitInterval) :
      A.regularCoordinate (Q t) ∈ orderThreeAffineHalfPlaneCoordinateRegion := by
    rw [A.sectionSevenAffineNormalizedZeroLift_projects]
    exact twicePuncturedClockwiseZeroPoint_mem_left t
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  have hr₀ : 0 < r := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  have hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let E := A.orderThreeBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr
  let xbig : A.orderThreeAffineHalfPlaneBaseLift :=
    ⟨A.sectionSevenAffineNormalizedMidpoint, by simpa only [Q.source] using hQhalf 0⟩
  let xbigg : A.orderThreeAffineHalfPlaneBaseLift :=
    ⟨regularSourceEquiv g₁ A.sectionSevenAffineNormalizedMidpoint,
      by simpa only [Q.target] using hQhalf 1⟩
  let Qbig : Path xbig xbigg :=
    { toFun := fun t ↦ ⟨Q t, hQhalf t⟩
      continuous_toFun := Q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact Q.source
      target' := by apply Subtype.ext; exact Q.target }
  have hbigAction : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant orderThreeAffineHalfPlaneCoordinateRegion)
      g₁ xbig = xbigg := by
    apply Subtype.ext
    rfl
  have hsmallEnd : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant (orderThreeAffineDiscCoordinateRegion r))
      g₁ (E.invFun xbig) = E.invFun xbigg := by
    rw [← hbigAction]
    exact (E.invFun_equivariant g₁ xbig).symm
  let QsmallCarrier : Path (E.invFun xbig)
      (actionMap
        (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
          A.regularCoordinate_deck_invariant (orderThreeAffineDiscCoordinateRegion r))
        g₁ (E.invFun xbig)) :=
    (Qbig.map E.invFun.continuous).cast rfl hsmallEnd
  let QsmallRegular := QsmallCarrier.map continuous_subtype_val
  let Qsmall : Path (E.invFun xbig).1.1
      (fuchsianSourceAction g₁ • (E.invFun xbig).1.1) :=
    (QsmallRegular.map continuous_subtype_val).cast rfl (by rfl)
  have hcover (t : unitInterval) : ∃ k : Delta,
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Qsmall t) : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
    obtain ⟨k, hk⟩ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_cayley
      (QsmallCarrier t).1.1 (QsmallCarrier t).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderThree.radius_pos)⟩
  have hbound := A.orderThree_generator_path_stays_standard_collar
    A.starSeparation.orderThree.sourceData _ Qsmall hcover 0
  have hmid : A.sectionSevenAffineNormalizedOrderThreeHalfPlaneLift
      sectionSevenAffineStripMidpoint = xbig := by
    apply Subtype.ext
    change A.sectionSevenAffineNormalizedStripContinuousLift sectionSevenAffineStripMidpoint = _
    exact A.sectionSevenAffineNormalizedStripContinuousLift_midpoint
  change ‖(orderThreeCayleyHomeomorph
    (E.invFun (A.sectionSevenAffineNormalizedOrderThreeHalfPlaneLift
      sectionSevenAffineStripMidpoint)).1.1 : ℂ)‖ < _
  rw [hmid]
  simpa only [Qsmall.source] using hbound

public def sectionSevenAffineNormalizedOrderFourHalfPlaneLift (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip, A.orderFourAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.sectionSevenAffineNormalizedStripContinuousLift z, by
      change 1 / 3 < (A.regularCoordinate (A.sectionSevenAffineNormalizedStripContinuousLift z)).1.re
      have h := congrArg Subtype.val
        (congrFun A.sectionSevenAffineNormalizedStripContinuousLift_coordinate z)
      change (A.regularCoordinate (A.sectionSevenAffineNormalizedStripContinuousLift z)).1 = z.1 at h
      rw [h]
      exact z.2.1⟩,
    A.sectionSevenAffineNormalizedStripContinuousLift.continuous.subtype_mk _⟩

public def sectionSevenAffineNormalizedOrderFourRadialLift (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      A.orderFourAffineDiscBaseLift A.sectionSevenAffineOrderFourMarkedDiscRadius) :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderFourBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr).invFun.comp
      A.sectionSevenAffineNormalizedOrderFourHalfPlaneLift

public theorem sectionSevenAffineNormalizedOrderFourRadialLift_midpoint_cayley
    (A : PaperAnalyticData) :
    ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineNormalizedOrderFourRadialLift sectionSevenAffineStripMidpoint).1.1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  let Q := A.sectionSevenAffineNormalizedOneLift
  have hQhalf (t : unitInterval) :
      A.regularCoordinate (Q t) ∈ orderFourAffineHalfPlaneCoordinateRegion := by
    rw [A.sectionSevenAffineNormalizedOneLift_projects]
    exact twicePuncturedClockwiseOnePoint_mem_right t
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  have hr₀ : 0 < r := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  have hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let E := A.orderFourBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr
  let xbig : A.orderFourAffineHalfPlaneBaseLift :=
    ⟨A.sectionSevenAffineNormalizedMidpoint, by simpa only [Q.source] using hQhalf 0⟩
  let xbigg : A.orderFourAffineHalfPlaneBaseLift :=
    ⟨regularSourceEquiv g₂ A.sectionSevenAffineNormalizedMidpoint,
      by simpa only [Q.target] using hQhalf 1⟩
  let Qbig : Path xbig xbigg :=
    { toFun := fun t ↦ ⟨Q t, hQhalf t⟩
      continuous_toFun := Q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact Q.source
      target' := by apply Subtype.ext; exact Q.target }
  have hbigAction : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant orderFourAffineHalfPlaneCoordinateRegion)
      g₂ xbig = xbigg := by
    apply Subtype.ext
    rfl
  have hsmallEnd : actionMap
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant (orderFourAffineDiscCoordinateRegion r))
      g₂ (E.invFun xbig) = E.invFun xbigg := by
    rw [← hbigAction]
    exact (E.invFun_equivariant g₂ xbig).symm
  let QsmallCarrier : Path (E.invFun xbig)
      (actionMap
        (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
          A.regularCoordinate_deck_invariant (orderFourAffineDiscCoordinateRegion r))
        g₂ (E.invFun xbig)) :=
    (Qbig.map E.invFun.continuous).cast rfl hsmallEnd
  let QsmallRegular := QsmallCarrier.map continuous_subtype_val
  let Qsmall : Path (E.invFun xbig).1.1
      (fuchsianSourceAction g₂ • (E.invFun xbig).1.1) :=
    (QsmallRegular.map continuous_subtype_val).cast rfl (by rfl)
  have hcover (t : unitInterval) : ∃ k : Delta,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Qsmall t) : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
    obtain ⟨k, hk⟩ := A.sectionSevenAffineOrderFourMarkedDiscRadius_cayley
      (QsmallCarrier t).1.1 (QsmallCarrier t).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderFour.radius_pos)⟩
  have hbound := A.orderFour_generator_path_stays_standard_collar
    A.starSeparation.orderFour.sourceData _ Qsmall hcover 0
  have hmid : A.sectionSevenAffineNormalizedOrderFourHalfPlaneLift
      sectionSevenAffineStripMidpoint = xbig := by
    apply Subtype.ext
    change A.sectionSevenAffineNormalizedStripContinuousLift sectionSevenAffineStripMidpoint = _
    exact A.sectionSevenAffineNormalizedStripContinuousLift_midpoint
  change ‖(orderFourCayleyHomeomorph
    (E.invFun (A.sectionSevenAffineNormalizedOrderFourHalfPlaneLift
      sectionSevenAffineStripMidpoint)).1.1 : ℂ)‖ < _
  rw [hmid]
  simpa only [Qsmall.source] using hbound

public theorem sectionSevenAffineNormalizedOrderThreeRadialLift_cayley
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip) :
    ‖(orderThreeCayleyHomeomorph
      (A.sectionSevenAffineNormalizedOrderThreeRadialLift z).1.1 : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
  let : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  let p := PathConnectedSpace.somePath sectionSevenAffineStripMidpoint z
  let Q := ((p.map A.sectionSevenAffineNormalizedOrderThreeRadialLift.continuous).map
    continuous_subtype_val).map continuous_subtype_val
  have hcover (t : unitInterval) : ∃ k : Delta,
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
    obtain ⟨k, hk⟩ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_cayley
      (A.sectionSevenAffineNormalizedOrderThreeRadialLift (p t)).1.1
      (A.sectionSevenAffineNormalizedOrderThreeRadialLift (p t)).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderThree.radius_pos)⟩
  have hzero : ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction 1 • Q 0) : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
    simpa only [map_one, one_smul, Q.source] using
      A.sectionSevenAffineNormalizedOrderThreeRadialLift_midpoint_cayley
  have h := A.orderThree_path_stays_entering_sheet
    A.starSeparation.orderThree.sourceData Q.toContinuousMap hcover 1 hzero 1
  change ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction 1 • Q 1) : ℂ)‖ < _ at h
  simpa only [map_one, one_smul, Q.target] using h

public theorem sectionSevenAffineNormalizedOrderFourRadialLift_cayley
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip) :
    ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineNormalizedOrderFourRadialLift z).1.1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  let : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  let p := PathConnectedSpace.somePath sectionSevenAffineStripMidpoint z
  let Q := ((p.map A.sectionSevenAffineNormalizedOrderFourRadialLift.continuous).map
    continuous_subtype_val).map continuous_subtype_val
  have hcover (t : unitInterval) : ∃ k : Delta,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
    obtain ⟨k, hk⟩ := A.sectionSevenAffineOrderFourMarkedDiscRadius_cayley
      (A.sectionSevenAffineNormalizedOrderFourRadialLift (p t)).1.1
      (A.sectionSevenAffineNormalizedOrderFourRadialLift (p t)).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderFour.radius_pos)⟩
  have hzero : ‖(orderFourCayleyHomeomorph (fuchsianSourceAction 1 • Q 0) : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
    simpa only [map_one, one_smul, Q.source] using
      A.sectionSevenAffineNormalizedOrderFourRadialLift_midpoint_cayley
  have h := A.orderFour_path_stays_entering_sheet
    A.starSeparation.orderFour.sourceData Q.toContinuousMap hcover 1 hzero 1
  change ‖(orderFourCayleyHomeomorph (fuchsianSourceAction 1 • Q 1) : ℂ)‖ < _ at h
  simpa only [map_one, one_smul, Q.target] using h

end SphereSixComplex.Geometry.PaperAnalyticData
