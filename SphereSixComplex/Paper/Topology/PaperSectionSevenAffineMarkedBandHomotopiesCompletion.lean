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

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

/-- The fibre coordinate on the marked band obtained from a specified affine-strip lift. -/
public noncomputable def affineBandFiberCoordinateOfLift
    (A : PaperAnalyticData) (L : A.AffineStripLift) :
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
    {A : PaperAnalyticData} (L : A.AffineStripLift)
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
    {A : PaperAnalyticData} (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint) :
    A.affineBandFiberCoordinateOfLift L =
      affineBandFiberCoordinate A := by
  rw [L.eq_named hL]
  rfl

/-- The two coordinates used below really describe the actual band point through the named strip
lift.  This is the point-set normalization that is absent from an unmarked trivialization. -/
public theorem affineBandPoint_toCentralFamily_eq_namedStripLiftPoint
    (A : PaperAnalyticData) (x : A.affineMarkedBand) :
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
    (A : PaperAnalyticData) (L : A.AffineStripLift)
    (g : C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.affineMarkedBand, OrderThreeReducedCentralFiber A.periods) :=
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
    (A : PaperAnalyticData) (L : A.AffineStripLift)
    (g : C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.affineMarkedBand, OrderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.affineBandStripCoordinate x) +
          A.affineBandFiberCoordinateOfLift L x,
        continuous_add.comp
          ((g.continuous.comp A.affineBandStripCoordinate.continuous).prodMk
            (A.affineBandFiberCoordinateOfLift L).continuous)⟩

/-- The logarithmic-gauge endpoint interface.  The lift used to read the endpoint is not
arbitrary: its value is pinned at the normalized midpoint.  The two formula fields are
the point-set equalities saying that the explicit star endpoints preserve the fibre
coordinate up to a translation depending only on the affine-strip coordinate. -/
public structure AffinePinnedLiftEndpointGaugeCompatibility
    (A : PaperAnalyticData) where
  stripLift : A.AffineStripLift
  stripLift_apply_midpoint :
    stripLift.lift affineStripMidpoint = A.affineNormalizedMidpoint
  orderThreeGauge :
    C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderThreeFormula :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderThreeStarEndpoint =
      A.affineOrderThreeGaugeProjectionOfLift stripLift orderThreeGauge
  orderFourGauge :
    C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderFourFormula :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderFourStarEndpoint =
      A.affineOrderFourGaugeProjectionOfLift stripLift orderFourGauge

/-- The irreducible two-field proposition, with the pinned lift and the two continuous gauges
made explicit parameters. -/
public structure AffinePinnedLiftEndpointGaugeFormulas
    (A : PaperAnalyticData) (L : A.AffineStripLift)
    (orderThreeGauge orderFourGauge :
      C(affineVerticalStrip,
        AdditiveTorus A.duplicatedSectionSevenBandParameter)) : Prop where
  orderThree :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderThreeStarEndpoint =
      A.affineOrderThreeGaugeProjectionOfLift L orderThreeGauge
  orderFour :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderFourStarEndpoint =
      A.affineOrderFourGaugeProjectionOfLift L orderFourGauge

/-- The pinned-lift endpoint calculation supplies the existing marked gauge-translation
interface. -/
public noncomputable def
    AffinePinnedLiftEndpointGaugeCompatibility.toGaugeTranslation
    {A : PaperAnalyticData}
    (H : A.AffinePinnedLiftEndpointGaugeCompatibility) :
    A.AffineMarkedEndpointGaugeTranslation := by
  refine
    { orderThreeGauge := H.orderThreeGauge
      orderThreeFormula := ?_
      orderFourGauge := H.orderFourGauge
      orderFourFormula := ?_ }
  · rw [H.orderThreeFormula]
    unfold affineOrderThreeGaugeProjectionOfLift
    unfold affineOrderThreeGaugeTranslatedProjection
    apply ContinuousMap.ext
    intro x
    have hcoordinate := congrArg
      (fun f : C(A.affineMarkedBand,
        AdditiveTorus A.duplicatedSectionSevenBandParameter) ↦ f x)
      (A.affineBandFiberCoordinateOfLift_eq_marked H.stripLift
        H.stripLift_apply_midpoint)
    change RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (H.orderThreeGauge (A.affineBandStripCoordinate x) +
              A.affineBandFiberCoordinateOfLift H.stripLift x)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (H.orderThreeGauge (A.affineBandStripCoordinate x) +
              affineBandFiberCoordinate A x))
    rw [hcoordinate]
  · rw [H.orderFourFormula]
    unfold affineOrderFourGaugeProjectionOfLift
    unfold affineOrderFourGaugeTranslatedProjection
    apply ContinuousMap.ext
    intro x
    have hcoordinate := congrArg
      (fun f : C(A.affineMarkedBand,
        AdditiveTorus A.duplicatedSectionSevenBandParameter) ↦ f x)
      (A.affineBandFiberCoordinateOfLift_eq_marked H.stripLift
        H.stripLift_apply_midpoint)
    change RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (H.orderFourGauge (A.affineBandStripCoordinate x) +
              A.affineBandFiberCoordinateOfLift H.stripLift x)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (H.orderFourGauge (A.affineBandStripCoordinate x) +
              affineBandFiberCoordinate A x))
    rw [hcoordinate]

/-- Midpoint pinning and the two gauge formulas supply the marked band homotopies. -/
public theorem markedBandHomotopies_of_pinnedLiftEndpointGaugeCompatibility
    (A : PaperAnalyticData)
    (H : A.AffinePinnedLiftEndpointGaugeCompatibility) :
    A.AffineOverlapBandCompatibility :=
  H.toGaugeTranslation.toBandCompatibility

/-- A midpoint-pinned strip lift and precisely the two explicit endpoint gauge formulas imply the
marked-band compatibility target. -/
public theorem markedBandHomotopies_of_pinnedLiftEndpointGaugeFormulas
    (A : PaperAnalyticData) (L : A.AffineStripLift)
    (hL : L.lift affineStripMidpoint = A.affineNormalizedMidpoint)
    (orderThreeGauge orderFourGauge :
      C(affineVerticalStrip,
        AdditiveTorus A.duplicatedSectionSevenBandParameter))
    (H : A.AffinePinnedLiftEndpointGaugeFormulas L
      orderThreeGauge orderFourGauge) :
    A.AffineOverlapBandCompatibility :=
  markedBandHomotopies_of_pinnedLiftEndpointGaugeCompatibility A
    { stripLift := L
      stripLift_apply_midpoint := hL
      orderThreeGauge := orderThreeGauge
      orderThreeFormula := H.orderThree
      orderFourGauge := orderFourGauge
      orderFourFormula := H.orderFour }

end SphereSixComplex.Geometry.PaperAnalyticData

end
