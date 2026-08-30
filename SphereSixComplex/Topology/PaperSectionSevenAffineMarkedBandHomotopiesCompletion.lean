module

public import SphereSixComplex.Topology.PaperSectionSevenAffinePrincipalGaugeStripLiftComparison

/-!
# Completion interface for the marked affine-band homotopies

The fibre coordinate of a central-band trivialization is meaningful here only after its strip
lift is pinned at the selected actual cusp crossing.  This file proves that such a pinned lift is
the named lift, and reduces the remaining endpoint calculation to the explicit statement that
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
public noncomputable def sectionSevenAffineBandFiberCoordinateOfLift
    (A : PaperAnalyticData) (L : A.SectionSevenAffineStripLift) :
    C(A.SectionSevenAffineMarkedBand,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  ⟨fun x ↦
      ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift
        A.sectionSevenAffineCentralSeparation L).symm
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x)).2,
    continuous_snd.comp
      ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift
        A.sectionSevenAffineCentralSeparation L).symm.continuous.comp
          A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.continuous)⟩

/-- Pinning a strip lift at the actual cusp crossing identifies the whole lift with the named
one, not merely its base coordinate. -/
public theorem SectionSevenAffineStripLift.eq_named
    {A : PaperAnalyticData} (L : A.SectionSevenAffineStripLift)
    (hL : L.lift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime) :
    L = A.sectionSevenAffineNamedStripLift := by
  have h : L.lift = A.sectionSevenAffineNamedStripLift.lift :=
    L.eq_named_of_apply_actualCuspCrossing hL
  cases L with
  | mk lift lift_coordinate =>
      dsimp at h
      cases h
      have hcoordinate : lift_coordinate =
          A.sectionSevenAffineNamedStripLift.lift_coordinate :=
        Subsingleton.elim _ _
      cases hcoordinate
      rfl

/-- Consequently the fibre coordinate obtained from a cusp-pinned lift is exactly the marked
band coordinate used by the finite-cover projections. -/
public theorem sectionSevenAffineBandFiberCoordinateOfLift_eq_marked
    {A : PaperAnalyticData} (L : A.SectionSevenAffineStripLift)
    (hL : L.lift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime) :
    A.sectionSevenAffineBandFiberCoordinateOfLift L =
      sectionSevenAffineBandFiberCoordinate A := by
  rw [L.eq_named hL]
  rfl

/-- The two coordinates used below really describe the actual band point through the named strip
lift.  This is the point-set normalization that is absent from an unmarked trivialization. -/
public theorem sectionSevenAffineBandPoint_toCentralFamily_eq_namedStripLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineCentralBandToCentralFamily
        A.sectionSevenAffineCentralSeparation
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x) =
      A.stripLiftPoint A.sectionSevenAffineNamedStripLift
        (A.sectionSevenAffineBandStripCoordinate x)
        (sectionSevenAffineBandFiberCoordinate A x) := by
  let b := A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x
  have h := A.sectionSevenAffineCentralBandMarkedProductHomeomorph_symm_toCentralFamily
    A.sectionSevenAffineCentralSeparation
      (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
        A.sectionSevenAffineCentralSeparation b)
  have hb : (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation).symm
        (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
          A.sectionSevenAffineCentralSeparation b) = b :=
    (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
      A.sectionSevenAffineCentralSeparation).symm_apply_apply b
  rw [hb] at h
  change A.sectionSevenAffineCentralBandToCentralFamily
      A.sectionSevenAffineCentralSeparation b =
    A.stripLiftPoint A.sectionSevenAffineNamedStripLift
      ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
        A.sectionSevenAffineCentralSeparation b).1)
      ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
        A.sectionSevenAffineCentralSeparation b).2)
  exact h

/-- The order-three endpoint projection written using an arbitrary specified strip lift and a
strip-dependent real-period gauge. -/
public noncomputable def sectionSevenAffineOrderThreeGaugeProjectionOfLift
    (A : PaperAnalyticData) (L : A.SectionSevenAffineStripLift)
    (g : C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.SectionSevenAffineMarkedBand, OrderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.sectionSevenAffineBandStripCoordinate x) +
          A.sectionSevenAffineBandFiberCoordinateOfLift L x,
        continuous_add.comp
          ((g.continuous.comp A.sectionSevenAffineBandStripCoordinate.continuous).prodMk
            (A.sectionSevenAffineBandFiberCoordinateOfLift L).continuous)⟩

/-- The order-four endpoint projection written using an arbitrary specified strip lift and a
strip-dependent real-period gauge. -/
public noncomputable def sectionSevenAffineOrderFourGaugeProjectionOfLift
    (A : PaperAnalyticData) (L : A.SectionSevenAffineStripLift)
    (g : C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.SectionSevenAffineMarkedBand, OrderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.sectionSevenAffineBandStripCoordinate x) +
          A.sectionSevenAffineBandFiberCoordinateOfLift L x,
        continuous_add.comp
          ((g.continuous.comp A.sectionSevenAffineBandStripCoordinate.continuous).prodMk
            (A.sectionSevenAffineBandFiberCoordinateOfLift L).continuous)⟩

/-- The exact remaining logarithmic-gauge input.  The lift used to read the endpoint is not
arbitrary: its value is pinned at the selected actual cusp crossing.  The two formula fields are
the residual point-set equalities saying that the explicit star endpoints preserve the fibre
coordinate up to a translation depending only on the affine-strip coordinate. -/
public structure SectionSevenAffinePinnedLiftEndpointGaugeCompatibility
    (A : PaperAnalyticData) where
  stripLift : A.SectionSevenAffineStripLift
  stripLift_apply_actualCuspCrossing :
    stripLift.lift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime
  orderThreeGauge :
    C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderThreeFormula :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint =
      A.sectionSevenAffineOrderThreeGaugeProjectionOfLift stripLift orderThreeGauge
  orderFourGauge :
    C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderFourFormula :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint =
      A.sectionSevenAffineOrderFourGaugeProjectionOfLift stripLift orderFourGauge

/-- The irreducible two-field proposition, with the pinned lift and the two continuous gauges
made explicit parameters. -/
public structure SectionSevenAffinePinnedLiftEndpointGaugeFormulas
    (A : PaperAnalyticData) (L : A.SectionSevenAffineStripLift)
    (orderThreeGauge orderFourGauge :
      C(sectionSevenAffineVerticalStrip,
        AdditiveTorus A.duplicatedSectionSevenBandParameter)) : Prop where
  orderThree :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint =
      A.sectionSevenAffineOrderThreeGaugeProjectionOfLift L orderThreeGauge
  orderFour :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint =
      A.sectionSevenAffineOrderFourGaugeProjectionOfLift L orderFourGauge

/-- The pinned-lift endpoint calculation supplies the existing marked gauge-translation
interface. -/
public noncomputable def
    SectionSevenAffinePinnedLiftEndpointGaugeCompatibility.toGaugeTranslation
    {A : PaperAnalyticData}
    (H : A.SectionSevenAffinePinnedLiftEndpointGaugeCompatibility) :
    A.SectionSevenAffineMarkedEndpointGaugeTranslation := by
  refine
    { orderThreeGauge := H.orderThreeGauge
      orderThreeFormula := ?_
      orderFourGauge := H.orderFourGauge
      orderFourFormula := ?_ }
  · rw [H.orderThreeFormula]
    unfold sectionSevenAffineOrderThreeGaugeProjectionOfLift
    unfold sectionSevenAffineOrderThreeGaugeTranslatedProjection
    apply ContinuousMap.ext
    intro x
    have hcoordinate := congrArg
      (fun f : C(A.SectionSevenAffineMarkedBand,
        AdditiveTorus A.duplicatedSectionSevenBandParameter) ↦ f x)
      (A.sectionSevenAffineBandFiberCoordinateOfLift_eq_marked H.stripLift
        H.stripLift_apply_actualCuspCrossing)
    change RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (H.orderThreeGauge (A.sectionSevenAffineBandStripCoordinate x) +
              A.sectionSevenAffineBandFiberCoordinateOfLift H.stripLift x)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (H.orderThreeGauge (A.sectionSevenAffineBandStripCoordinate x) +
              sectionSevenAffineBandFiberCoordinate A x))
    rw [hcoordinate]
  · rw [H.orderFourFormula]
    unfold sectionSevenAffineOrderFourGaugeProjectionOfLift
    unfold sectionSevenAffineOrderFourGaugeTranslatedProjection
    apply ContinuousMap.ext
    intro x
    have hcoordinate := congrArg
      (fun f : C(A.SectionSevenAffineMarkedBand,
        AdditiveTorus A.duplicatedSectionSevenBandParameter) ↦ f x)
      (A.sectionSevenAffineBandFiberCoordinateOfLift_eq_marked H.stripLift
        H.stripLift_apply_actualCuspCrossing)
    change RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (H.orderFourGauge (A.sectionSevenAffineBandStripCoordinate x) +
              A.sectionSevenAffineBandFiberCoordinateOfLift H.stripLift x)) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (H.orderFourGauge (A.sectionSevenAffineBandStripCoordinate x) +
              sectionSevenAffineBandFiberCoordinate A x))
    rw [hcoordinate]

/-- Thus the only unproved input is the pair of explicit gauge formulas; the cusp pinning and
all homotopy assembly are discharged here. -/
public theorem markedBandHomotopies_of_pinnedLiftEndpointGaugeCompatibility
    (A : PaperAnalyticData)
    (H : A.SectionSevenAffinePinnedLiftEndpointGaugeCompatibility) :
    A.SectionSevenAffineOverlapBandCompatibility :=
  H.toGaugeTranslation.toBandCompatibility

/-- A cusp-pinned strip lift and precisely the two explicit endpoint gauge formulas imply the
marked-band compatibility target. -/
public theorem markedBandHomotopies_of_pinnedLiftEndpointGaugeFormulas
    (A : PaperAnalyticData) (L : A.SectionSevenAffineStripLift)
    (hL : L.lift A.sectionSevenAffineActualCuspCrossingPoint =
      A.actualCuspAngularRegularBasePoint A.sectionSevenAffineActualCuspCrossingTime)
    (orderThreeGauge orderFourGauge :
      C(sectionSevenAffineVerticalStrip,
        AdditiveTorus A.duplicatedSectionSevenBandParameter))
    (H : A.SectionSevenAffinePinnedLiftEndpointGaugeFormulas L
      orderThreeGauge orderFourGauge) :
    A.SectionSevenAffineOverlapBandCompatibility :=
  markedBandHomotopies_of_pinnedLiftEndpointGaugeCompatibility A
    { stripLift := L
      stripLift_apply_actualCuspCrossing := hL
      orderThreeGauge := orderThreeGauge
      orderThreeFormula := H.orderThree
      orderFourGauge := orderFourGauge
      orderFourFormula := H.orderFour }

end SphereSixComplex.Geometry.PaperAnalyticData

end
