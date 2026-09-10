module
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineNormalizedStripLift
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandEndpointFormula
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRegularBaseRadialEquivalence
public import SphereSixComplex.Paper.Topology.PaperEllipticPathSheet
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

public def affineNormalizedOrderThreeHalfPlaneLift (A : PaperAnalyticData) :
    C(affineVerticalStrip, A.OrderThreeAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.affineNormalizedStripContinuousLift z, by
      change (A.regularCoordinate (A.affineNormalizedStripContinuousLift z)).1.re < 2 / 3
      have h := congrArg Subtype.val
        (congrFun A.affineNormalizedStripContinuousLift_coordinate z)
      change (A.regularCoordinate (A.affineNormalizedStripContinuousLift z)).1 = z.1 at h
      rw [h]
      exact z.2.2⟩,
    A.affineNormalizedStripContinuousLift.continuous.subtype_mk _⟩

public def affineNormalizedOrderThreeRadialLift (A : PaperAnalyticData) :
    C(affineVerticalStrip,
      A.OrderThreeAffineDiscBaseLift A.affineOrderThreeMarkedDiscRadius) :=
  let r := A.affineOrderThreeMarkedDiscRadius
  let hr₀ := A.affineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.affineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderThreeBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr).invFun.comp
      A.affineNormalizedOrderThreeHalfPlaneLift

public theorem affineNormalizedOrderThreeRadialLift_midpoint_cayley
    (A : PaperAnalyticData) :
    ‖(orderThreeCayleyHomeomorph
      (A.affineNormalizedOrderThreeRadialLift affineStripMidpoint).1.1 : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
  let Q := A.affineNormalizedZeroLift
  have hQhalf (t : unitInterval) :
      A.regularCoordinate (Q t) ∈ orderThreeAffineHalfPlaneCoordinateRegion := by
    rw [A.affineNormalizedZeroLift_projects]
    exact twicePuncturedClockwiseZeroPoint_mem_left t
  let r := A.affineOrderThreeMarkedDiscRadius
  have hr₀ : 0 < r := A.affineOrderThreeMarkedDiscRadius_spec.1
  have hr : r ≤ 2 / 3 :=
    A.affineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let E := A.orderThreeBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr
  let xbig : A.OrderThreeAffineHalfPlaneBaseLift :=
    ⟨A.affineNormalizedMidpoint, by simpa only [Q.source] using hQhalf 0⟩
  let xbigg : A.OrderThreeAffineHalfPlaneBaseLift :=
    ⟨regularSourceEquiv g₁ A.affineNormalizedMidpoint,
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
    obtain ⟨k, hk⟩ := A.affineOrderThreeMarkedDiscRadius_cayley
      (QsmallCarrier t).1.1 (QsmallCarrier t).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderThree.radius_pos)⟩
  have hbound := A.orderThree_generator_path_stays_standard_collar
    A.starSeparation.orderThree.sourceData _ Qsmall hcover 0
  have hmid : A.affineNormalizedOrderThreeHalfPlaneLift
      affineStripMidpoint = xbig := by
    apply Subtype.ext
    change A.affineNormalizedStripContinuousLift affineStripMidpoint = _
    exact A.affineNormalizedStripContinuousLift_midpoint
  change ‖(orderThreeCayleyHomeomorph
    (E.invFun (A.affineNormalizedOrderThreeHalfPlaneLift
      affineStripMidpoint)).1.1 : ℂ)‖ < _
  rw [hmid]
  simpa only [Qsmall.source] using hbound

public def affineNormalizedOrderFourHalfPlaneLift (A : PaperAnalyticData) :
    C(affineVerticalStrip, A.OrderFourAffineHalfPlaneBaseLift) :=
  ⟨fun z ↦ ⟨A.affineNormalizedStripContinuousLift z, by
      change 1 / 3 < (A.regularCoordinate (A.affineNormalizedStripContinuousLift z)).1.re
      have h := congrArg Subtype.val
        (congrFun A.affineNormalizedStripContinuousLift_coordinate z)
      change (A.regularCoordinate (A.affineNormalizedStripContinuousLift z)).1 = z.1 at h
      rw [h]
      exact z.2.1⟩,
    A.affineNormalizedStripContinuousLift.continuous.subtype_mk _⟩

public def affineNormalizedOrderFourRadialLift (A : PaperAnalyticData) :
    C(affineVerticalStrip,
      A.OrderFourAffineDiscBaseLift A.affineOrderFourMarkedDiscRadius) :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderFourBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr).invFun.comp
      A.affineNormalizedOrderFourHalfPlaneLift

public theorem affineNormalizedOrderFourRadialLift_midpoint_cayley
    (A : PaperAnalyticData) :
    ‖(orderFourCayleyHomeomorph
      (A.affineNormalizedOrderFourRadialLift affineStripMidpoint).1.1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  let Q := A.affineNormalizedOneLift
  have hQhalf (t : unitInterval) :
      A.regularCoordinate (Q t) ∈ orderFourAffineHalfPlaneCoordinateRegion := by
    rw [A.affineNormalizedOneLift_projects]
    exact twicePuncturedClockwiseOnePoint_mem_right t
  let r := A.affineOrderFourMarkedDiscRadius
  have hr₀ : 0 < r := A.affineOrderFourMarkedDiscRadius_spec.1
  have hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  let E := A.orderFourBaseRadialEquiv (s := r / 2)
    (by linarith) (by linarith) hr
  let xbig : A.OrderFourAffineHalfPlaneBaseLift :=
    ⟨A.affineNormalizedMidpoint, by simpa only [Q.source] using hQhalf 0⟩
  let xbigg : A.OrderFourAffineHalfPlaneBaseLift :=
    ⟨regularSourceEquiv g₂ A.affineNormalizedMidpoint,
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
    obtain ⟨k, hk⟩ := A.affineOrderFourMarkedDiscRadius_cayley
      (QsmallCarrier t).1.1 (QsmallCarrier t).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderFour.radius_pos)⟩
  have hbound := A.orderFour_generator_path_stays_standard_collar
    A.starSeparation.orderFour.sourceData _ Qsmall hcover 0
  have hmid : A.affineNormalizedOrderFourHalfPlaneLift
      affineStripMidpoint = xbig := by
    apply Subtype.ext
    change A.affineNormalizedStripContinuousLift affineStripMidpoint = _
    exact A.affineNormalizedStripContinuousLift_midpoint
  change ‖(orderFourCayleyHomeomorph
    (E.invFun (A.affineNormalizedOrderFourHalfPlaneLift
      affineStripMidpoint)).1.1 : ℂ)‖ < _
  rw [hmid]
  simpa only [Qsmall.source] using hbound

public theorem affineNormalizedOrderThreeRadialLift_cayley
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ‖(orderThreeCayleyHomeomorph
      (A.affineNormalizedOrderThreeRadialLift z).1.1 : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
  let : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  let p := PathConnectedSpace.somePath affineStripMidpoint z
  let Q := ((p.map A.affineNormalizedOrderThreeRadialLift.continuous).map
    continuous_subtype_val).map continuous_subtype_val
  have hcover (t : unitInterval) : ∃ k : Delta,
      ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
    obtain ⟨k, hk⟩ := A.affineOrderThreeMarkedDiscRadius_cayley
      (A.affineNormalizedOrderThreeRadialLift (p t)).1.1
      (A.affineNormalizedOrderThreeRadialLift (p t)).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderThree.radius_pos)⟩
  have hzero : ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction 1 • Q 0) : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
    simpa only [map_one, one_smul, Q.source] using
      A.affineNormalizedOrderThreeRadialLift_midpoint_cayley
  have h := A.orderThree_path_stays_entering_sheet
    A.starSeparation.orderThree.sourceData Q.toContinuousMap hcover 1 hzero 1
  change ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction 1 • Q 1) : ℂ)‖ < _ at h
  simpa only [map_one, one_smul, Q.target] using h

public theorem affineNormalizedOrderFourRadialLift_cayley
    (A : PaperAnalyticData) (z : affineVerticalStrip) :
    ‖(orderFourCayleyHomeomorph
      (A.affineNormalizedOrderFourRadialLift z).1.1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  let : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  let p := PathConnectedSpace.somePath affineStripMidpoint z
  let Q := ((p.map A.affineNormalizedOrderFourRadialLift.continuous).map
    continuous_subtype_val).map continuous_subtype_val
  have hcover (t : unitInterval) : ∃ k : Delta,
      ‖(orderFourCayleyHomeomorph (fuchsianSourceAction k • Q t) : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
    obtain ⟨k, hk⟩ := A.affineOrderFourMarkedDiscRadius_cayley
      (A.affineNormalizedOrderFourRadialLift (p t)).1.1
      (A.affineNormalizedOrderFourRadialLift (p t)).2
    exact ⟨k, hk.trans (half_lt_self A.starSeparation.orderFour.radius_pos)⟩
  have hzero : ‖(orderFourCayleyHomeomorph (fuchsianSourceAction 1 • Q 0) : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
    simpa only [map_one, one_smul, Q.source] using
      A.affineNormalizedOrderFourRadialLift_midpoint_cayley
  have h := A.orderFour_path_stays_entering_sheet
    A.starSeparation.orderFour.sourceData Q.toContinuousMap hcover 1 hzero 1
  change ‖(orderFourCayleyHomeomorph (fuchsianSourceAction 1 • Q 1) : ℂ)‖ < _ at h
  simpa only [map_one, one_smul, Q.target] using h

end SphereSixComplex.Geometry.PaperAnalyticData
