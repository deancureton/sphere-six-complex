module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffinePrincipalGaugeStripLiftComparison

/-!
# Completion interface for the marked affine-band homotopies

The fibre coordinate of a central-band trivialization is meaningful here only after its strip
lift is pinned at the normalized midpoint.  This file proves that such a pinned lift is
the named lift, and reduces the endpoint calculation to the explicit statement that
the real-period endpoint differs from that pinned coordinate by a gauge depending on the strip.
-/

@[expose] public section

noncomputable section

open Set Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.EllipticFilling

/-- The fibre coordinate on the marked band obtained from a specified affine-strip lift. -/
public noncomputable def affineBandFiberCoordinateOfLift
    (A : AnalyticData) (L : A.AffineStripLift) :
    C(A.affineMarkedBand,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  ⟨fun x ↦
      ((A.affineCentralBandProductHomeomorphOfLift
        A.affineCentralSeparation L).symm
          (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x)).2,
    continuous_snd.comp
      ((A.affineCentralBandProductHomeomorphOfLift
        A.affineCentralSeparation L).symm.continuous.comp
          A.actualAffineHeightSplit.sidesIntersectionHomeomorph.continuous)⟩

/-- Pinning a strip lift at the normalized midpoint identifies the whole lift with the named
one, not merely its base coordinate. -/
public theorem AffineStripLift.eq_named
    {A : AnalyticData} (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint) :
    L = A.affineNamedStripLift := by
  have h : L.lift = A.affineNamedStripLift.lift :=
    L.eq_named_of_apply_midpoint hL
  cases L with
  | mk lift lift_coordinate =>
      dsimp at h
      cases h
      have hcoordinate : lift_coordinate =
          A.affineNamedStripLift.lift_coordinate :=
        Subsingleton.elim _ _
      cases hcoordinate
      rfl

/-- Consequently the fibre coordinate obtained from a midpoint-pinned lift is exactly the marked
band coordinate used by the finite-cover projections. -/
public theorem affineBandFiberCoordinateOfLift_eq_marked
    {A : AnalyticData} (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint) :
    A.affineBandFiberCoordinateOfLift L =
      affineBandFiberCoordinate A := by
  rw [L.eq_named hL]
  rfl

/-- The two coordinates used below really describe the actual band point through the named strip
lift.  This is the point-set normalization that is absent from an unmarked trivialization. -/
public theorem affineBandPoint_toCentralFamily_eq_namedStripLiftPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.affineCentralBandToCentralFamily
        A.affineCentralSeparation
          (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x) =
      A.stripLiftPoint A.affineNamedStripLift
        (A.affineBandStripCoordinate x)
        (affineBandFiberCoordinate A x) := by
  let b := A.actualAffineHeightSplit.sidesIntersectionHomeomorph x
  have h := A.affineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    A.affineCentralSeparation
      (A.affineCentralBandMarkedProductHomeomorph
        A.affineCentralSeparation b)
  have hb : (A.affineCentralBandMarkedProductHomeomorph
      A.affineCentralSeparation).symm
        (A.affineCentralBandMarkedProductHomeomorph
          A.affineCentralSeparation b) = b :=
    (A.affineCentralBandMarkedProductHomeomorph
      A.affineCentralSeparation).symm_apply_apply b
  rw [hb] at h
  change A.affineCentralBandToCentralFamily
      A.affineCentralSeparation b =
    A.stripLiftPoint A.affineNamedStripLift
      ((A.affineCentralBandMarkedProductHomeomorph
        A.affineCentralSeparation b).1)
      ((A.affineCentralBandMarkedProductHomeomorph
        A.affineCentralSeparation b).2)
  exact h

/-- The order-three endpoint projection written using an arbitrary specified strip lift and a
strip-dependent real-period gauge. -/
public noncomputable def affineOrderThreeGaugeProjectionOfLift
    (A : AnalyticData) (L : A.AffineStripLift)
    (g : C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.affineMarkedBand, orderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.affineBandStripCoordinate x) +
          A.affineBandFiberCoordinateOfLift L x,
        continuous_add.comp
          ((g.continuous.comp A.affineBandStripCoordinate.continuous).prodMk
            (A.affineBandFiberCoordinateOfLift L).continuous)⟩

/-- The order-four endpoint projection written using an arbitrary specified strip lift and a
strip-dependent real-period gauge. -/
public noncomputable def affineOrderFourGaugeProjectionOfLift
    (A : AnalyticData) (L : A.AffineStripLift)
    (g : C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.affineMarkedBand, orderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.affineBandStripCoordinate x) +
          A.affineBandFiberCoordinateOfLift L x,
        continuous_add.comp
          ((g.continuous.comp A.affineBandStripCoordinate.continuous).prodMk
            (A.affineBandFiberCoordinateOfLift L).continuous)⟩

/-- Midpoint-pinned endpoint formulas determine the marked gauge translations. -/
public noncomputable def AffineMarkedEndpointGaugeTranslation.ofPinnedLift
    {A : AnalyticData} (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint)
    (g₃ g₄ : C(affineVerticalStrip, AdditiveTorus A.duplicatedSectionSevenBandParameter))
    (h₃ : (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
      A.affineOrderThreeStarEndpoint = A.affineOrderThreeGaugeProjectionOfLift L g₃)
    (h₄ : (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
      A.affineOrderFourStarEndpoint = A.affineOrderFourGaugeProjectionOfLift L g₄) :
    A.AffineMarkedEndpointGaugeTranslation := by
  refine
    { orderThreeGauge := g₃
      orderThreeFormula := ?_
      orderFourGauge := g₄
      orderFourFormula := ?_ }
  · rw [h₃]
    unfold affineOrderThreeGaugeProjectionOfLift
    unfold affineOrderThreeGaugeTranslatedProjection
    apply ContinuousMap.ext
    intro x
    have hcoordinate := congrArg
      (fun f : C(A.affineMarkedBand,
        AdditiveTorus A.duplicatedSectionSevenBandParameter) ↦ f x)
      (A.affineBandFiberCoordinateOfLift_eq_marked L
        hL)
    change RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (g₃ (A.affineBandStripCoordinate x) +
              A.affineBandFiberCoordinateOfLift L x)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (g₃ (A.affineBandStripCoordinate x) +
              affineBandFiberCoordinate A x))
    rw [hcoordinate]
  · rw [h₄]
    unfold affineOrderFourGaugeProjectionOfLift
    unfold affineOrderFourGaugeTranslatedProjection
    apply ContinuousMap.ext
    intro x
    have hcoordinate := congrArg
      (fun f : C(A.affineMarkedBand,
        AdditiveTorus A.duplicatedSectionSevenBandParameter) ↦ f x)
      (A.affineBandFiberCoordinateOfLift_eq_marked L
        hL)
    change RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (g₄ (A.affineBandStripCoordinate x) +
              A.affineBandFiberCoordinateOfLift L x)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (g₄ (A.affineBandStripCoordinate x) +
              affineBandFiberCoordinate A x))
    rw [hcoordinate]

/-- Midpoint-pinned endpoint formulas give the marked band homotopies. -/
public theorem homotopic_bandToReducedFiber_coverMap_of_pinnedLift
    {A : AnalyticData} (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint)
    (g₃ g₄ : C(affineVerticalStrip, AdditiveTorus A.duplicatedSectionSevenBandParameter))
    (h₃ : (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
      A.affineOrderThreeStarEndpoint = A.affineOrderThreeGaugeProjectionOfLift L g₃)
    (h₄ : (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
      A.affineOrderFourStarEndpoint = A.affineOrderFourGaugeProjectionOfLift L g₄) :
    (affineOrderThreeBandToReducedFiber
      (orderThreeOverlapIsHomotopyEquivalence_inclusion
        A.orderThreeOverlapIsHomotopyEquivalence)).Homotopic
      (affineBandOrderThreeCoverMap A) ∧
    (affineOrderFourBandToReducedFiber
      (orderFourOverlapIsHomotopyEquivalence_inclusion
        A.orderFourOverlapIsHomotopyEquivalence)).Homotopic
      (affineBandOrderFourCoverMap A) :=
  (AffineMarkedEndpointGaugeTranslation.ofPinnedLift L hL g₃ g₄ h₃ h₄).homotopic_bandToReducedFiber_coverMap

end SphereSixComplex.Geometry.AnalyticData

end
