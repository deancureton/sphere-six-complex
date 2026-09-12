module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOrderFourEndpointGaugeFormulaProof

/-!
# Reduction of the order-four endpoint real-period identity

The constructed order-four radial equivalence has an inverse given by flat transport.  This file
uses that explicit inverse to reduce the endpoint calculation to membership of the resulting named
representative in the selected order-four collar.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.EllipticFilling
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The named marked-band point lifted to the order-four affine half-plane carrier. -/
public noncomputable def affineOrderFourNamedHalfPlaneLiftPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.orderFourAffineHalfPlaneLiftCarrier.carrier :=
  let z := A.affineBandStripCoordinate x
  let t := A.affineBandFiberCoordinateOfLift
    A.affineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.affineNamedStripLift.lift z
  ⟨projection (regularParameterMap A.periods)
      (b, A.regularFixedToMoving b v), by
    change 1 / 3 < (A.regularCoordinate b).1.re
    rw [A.affineNamedStripLift.lift_coordinate]
    exact z.2.1⟩

/-- The corresponding point of the order-four affine disc carrier selected by the radial
inverse. -/
public noncomputable def affineOrderFourNamedDiscLiftPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    (A.orderFourAffineDiscLiftCarrier
      A.affineOrderFourMarkedDiscRadius).carrier :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderFourAffineRadialEquivChoice hr₀ hr).invFun
    (A.affineOrderFourNamedHalfPlaneLiftPoint x)

/-- The named half-plane lift represents exactly the actual marked-band point in the central
family. -/
public theorem affineOrderFourNamedHalfPlaneLiftPoint_toCentralFamily
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (Quotient.mk _ (A.affineOrderFourNamedHalfPlaneLiftPoint x)) =
      A.affineCentralBandToCentralFamily
        A.affineCentralSeparation
          (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x) := by
  rw [A.affineBandPoint_toCentralFamily_eq_namedStripLiftPoint]
  unfold affineOrderFourNamedHalfPlaneLiftPoint
  let z := A.affineBandStripCoordinate x
  let t := A.affineBandFiberCoordinateOfLift
    A.affineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.affineNamedStripLift.lift z
  change A.centralQuotientProjection
      (projection (regularParameterMap A.periods)
        (b, A.regularFixedToMoving b v)) = A.stripLiftPoint
          A.affineNamedStripLift z t
  rw [← A.stripLiftPoint_regularMovingToFixed
    A.affineNamedStripLift z (A.regularFixedToMoving b v)]
  rw [A.regularMovingToFixed_regularFixedToMoving]
  simp [v]

/-- In the fixed order-four torus, the named half-plane lift has the marked band coordinate
transported from the common period basis. -/
public theorem orderFourRealPeriod_namedHalfPlaneLiftPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.affineOrderFourNamedHalfPlaneLiftPoint x).1)).2 =
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
        (A.affineBandFiberCoordinateOfLift
          A.affineNamedStripLift x) := by
  let z := A.affineBandStripCoordinate x
  let t := A.affineBandFiberCoordinateOfLift
    A.affineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.affineNamedStripLift.lift z
  change (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (Quotient.mk _ (b, A.regularFixedToMoving b v)))).2 = _
  rw [regularFamilyInclusion_mk, orderFourRealPeriodProductHomeomorph_mk]
  change Quotient.mk _
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (b, A.regularFixedToMoving b v)).2 =
    A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph t
  rw [← Quotient.out_eq t]
  let p₄ := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo
  let e : ComplexTwoSpace ≃L[ℝ] ComplexTwoSpace :=
    A.duplicatedSectionSevenBandFullRank.realEquiv.symm.trans
      (FullRank.ofSetupInequalities p₄.1 p₄.2).realEquiv
  change Quotient.mk _
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (b, A.regularFixedToMoving b v)).2 = Quotient.mk _ (e v)
  apply congrArg (Quotient.mk _)
  simp [e, p₄, movingToFixedCover, regularFixedToMoving, fixedToMovingCover,
    periodCoordinates, fullRankDomain, duplicatedSectionSevenBandFullRank,
    duplicatedSectionSevenBandParameter]

/-- The named disc lift lies over the explicitly constructed order-four radial base. -/
public theorem regularTotalSpaceBase_namedDiscLiftPoint
    {A : AnalyticData}
    (x : A.affineMarkedBand) :
    regularTotalSpaceBase A.periods
        (A.affineOrderFourNamedDiscLiftPoint x).1 =
      A.affineOrderFourRadialBaseLift
        (A.affineBandStripCoordinate x) := by
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  rw [affineOrderFourNamedDiscLiftPoint,
    A.orderFourAffineRadialEquivChoice_invFun]
  rw [A.regularTotalSpaceBase_regularFlatTransport]
  rfl



/-- Affine radial transport preserves the named order-four real-period coordinate. -/
public theorem orderFourRealPeriod_namedDiscLiftPoint
    {A : AnalyticData}
    (x : A.affineMarkedBand) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.affineOrderFourNamedDiscLiftPoint x).1)).2 =
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
        (A.affineBandFiberCoordinateOfLift
          A.affineNamedStripLift x) := by
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  rw [affineOrderFourNamedDiscLiftPoint,
    A.orderFourAffineRadialEquivChoice_invFun]
  rw [A.orderFourRealPeriodProductHomeomorph_regularFlatTransport_snd]
  exact A.orderFourRealPeriod_namedHalfPlaneLiftPoint x

/-- The central-region quotient coordinate of a marked band point is represented by its named
half-plane lift. -/
public theorem affineOrderFourCentralRegionQuotient_band
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.affineOrderFourCentralRegionQuotientHomeomorph
        (A.affineBandToOrderFourCentralRegion x) =
      Quotient.mk _ (A.affineOrderFourNamedHalfPlaneLiftPoint x) := by
  apply A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  let u := A.affineBandToOrderFourCentralRegion x
  let y : A.ellipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightUpperRegion
      A.ellipticCentralHeight (1 / 3 : ℝ) u.2⟩
  have hy : (1 : ℝ) / 3 < A.ellipticCentralHeight y := by
    obtain ⟨y', hy', hxy⟩ := u.2
    have hyy : y' = y := Subtype.ext hxy
    exact hyy ▸ hy'
  calc
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.affineOrderFourCentralRegionQuotientHomeomorph u) =
        A.ellipticCentralImageHomeomorph y :=
      A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient y hy
    _ = A.affineCentralBandToCentralFamily
          A.affineCentralSeparation
            (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x) := rfl
    _ = A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
          (Quotient.mk _ (A.affineOrderFourNamedHalfPlaneLiftPoint x)) :=
      (A.affineOrderFourNamedHalfPlaneLiftPoint_toCentralFamily x).symm

/-- The unembedded order-four affine-disc endpoint used inside the overlap endpoint. -/
public noncomputable def affineOrderFourDiscRegionEndpoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.affineOrderFourDiscRegion
      A.affineOrderFourMarkedDiscRadius :=
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderFourAffineDiscCentralHomotopyEquiv hr₀ hr).invFun
    (A.affineBandToOrderFourCentralRegion x)

/-- The affine-disc quotient coordinate of the endpoint is represented by the selected named
disc lift. -/
public theorem affineOrderFourDiscRegionQuotient_endpoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.affineOrderFourDiscRegionQuotientHomeomorph
        A.affineOrderFourMarkedDiscRadius
        (A.affineOrderFourDiscRegionEndpoint x) =
      Quotient.mk _ (A.affineOrderFourNamedDiscLiftPoint x) := by
  let r := A.affineOrderFourMarkedDiscRadius
  let hr₀ := A.affineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.affineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  change A.affineOrderFourDiscRegionQuotientHomeomorph r
      (A.affineOrderFourDiscRegionQuotientHomeomorph r |>.symm
        ((A.orderFourAffineRadialEquivChoice hr₀ hr).quotientInvFun
          (A.affineOrderFourCentralRegionQuotientHomeomorph
            (A.affineBandToOrderFourCentralRegion x)))) = _
  rw [Homeomorph.apply_symm_apply,
    A.affineOrderFourCentralRegionQuotient_band x]
  rfl

/-- The overlap endpoint and the unembedded disc-region endpoint have the same underlying
elliptic-interior point. -/
public theorem affineOrderFourDiscOverlapEndpoint_val
    (A : AnalyticData) (x : A.affineMarkedBand) :
    (A.affineOrderFourDiscOverlapEndpoint x).1 =
      (A.affineOrderFourDiscRegionEndpoint x).1 :=
  rfl

/-- Undo the principal gauge on the named radial disc representative. -/
public noncomputable def affineOrderFourNamedCollarTotalPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    TotalSpace (parameterMap A.periods) :=
  (orderFourPrincipalGaugeEquiv A.periods).symm
    (regularFamilyInclusion A.periods
      (A.affineOrderFourNamedDiscLiftPoint x).1)

/-- The collar radius of the inverse-gauged named representative is the Cayley radius of its
explicit radial base lift. -/
public theorem orderFourFamilyRadius_namedCollarTotalPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    orderFourFamilyRadius A.periods
        (A.affineOrderFourNamedCollarTotalPoint x) =
      ‖(orderFourCayleyHomeomorph
        (A.affineOrderFourRadialBaseLift
          (A.affineBandStripCoordinate x)).1 : ℂ)‖ := by
  rw [affineOrderFourNamedCollarTotalPoint,
    orderFourFamilyRadius_principalGauge_symm,
    orderFourFamilyRadius.eq_def,
    familyTotalSpaceBase_regularFamilyInclusion,
    regularTotalSpaceBase_namedDiscLiftPoint]

/-- The named radial representative cannot hit the puncture, because its base belongs to the
regular source and the order-four Cayley centre lies over the excluded coordinate `1`. -/
public theorem orderFourFamilyRadius_namedCollarTotalPoint_pos
    (A : AnalyticData) (x : A.affineMarkedBand) :
    0 < orderFourFamilyRadius A.periods
      (A.affineOrderFourNamedCollarTotalPoint x) := by
  rw [A.orderFourFamilyRadius_namedCollarTotalPoint x]
  apply norm_pos_iff.mpr
  apply coe_ne_zero_of_ne_center
  intro hzero
  have hfixed :
      (A.affineOrderFourRadialBaseLift
        (A.affineBandStripCoordinate x)).1 =
        fuchsianTwoFixedPoint := by
    apply orderFourCayleyHomeomorph.injective
    simpa [orderFourCayleyHomeomorph, UpperHalfPlane.cayleyHomeomorph, UpperHalfPlane.cayleyToDisc,
      ComplexUnitDisc.center, orderFourCayley_fixedPoint] using hzero
  have hregular :=
    (A.affineOrderFourRadialBaseLift
      (A.affineBandStripCoordinate x)).2
  have hmem := (A.isRegularBasePoint_iff_coordinate_mem _).mp hregular
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  exact hmem.2 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_two)

/-- Thus collar compatibility is equivalent to the sole remaining analytic inequality: the
chosen radial lift, rather than merely some regular-deck translate of it, lies inside the selected
order-four Cayley radius. -/
public theorem affineOrderFourNamedRadialCollarCompatibility_iff
    (A : AnalyticData) :
    (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius) ↔
      ∀ x : A.affineMarkedBand,
        ‖(orderFourCayleyHomeomorph
          (A.affineOrderFourRadialBaseLift
            (A.affineBandStripCoordinate x)).1 : ℂ)‖ <
          A.starSeparation.orderFour.radius := by
  constructor
  · intro C x
    have hx := C x
    change 0 < orderFourFamilyRadius A.periods
        (A.affineOrderFourNamedCollarTotalPoint x) ∧
      orderFourFamilyRadius A.periods
        (A.affineOrderFourNamedCollarTotalPoint x) <
          A.starSeparation.orderFour.radius at hx
    rw [A.orderFourFamilyRadius_namedCollarTotalPoint x] at hx
    exact hx.2
  · intro h x
    change 0 < orderFourFamilyRadius A.periods
        (A.affineOrderFourNamedCollarTotalPoint x) ∧
      orderFourFamilyRadius A.periods
        (A.affineOrderFourNamedCollarTotalPoint x) <
          A.starSeparation.orderFour.radius
    exact ⟨A.orderFourFamilyRadius_namedCollarTotalPoint_pos x, by
      rw [A.orderFourFamilyRadius_namedCollarTotalPoint x]
      exact h x⟩

/-- The named collar representative as a point of the affine collar carrier. -/
public noncomputable def affineOrderFourNamedCollarLiftPoint
    (A : AnalyticData)
    (C : (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius))
    (x : A.affineMarkedBand) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius).carrier :=
  ⟨A.affineOrderFourNamedCollarTotalPoint x, C x⟩

/-- Gauging the named collar representative recovers the named radial disc representative. -/
public theorem orderFourPrincipalGauge_namedCollarLiftPoint
    (A : AnalyticData)
    (C : (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius))
    (x : A.affineMarkedBand) :
    (orderFourPuncturedCollarGaugeEquiv A.periods
      A.starSeparation.orderFour.radius
      (A.affineOrderFourNamedCollarLiftPoint C x)).1 =
        regularFamilyInclusion A.periods
          (A.affineOrderFourNamedDiscLiftPoint x).1 := by
  change orderFourPrincipalGaugeEquiv A.periods
      ((orderFourPrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (A.affineOrderFourNamedDiscLiftPoint x).1)) = _
  exact (orderFourPrincipalGaugeEquiv A.periods).apply_symm_apply _

/-- The linear collar's regular representative of the named point is exactly the named radial
disc representative. -/
public theorem orderFourCollarToRegular_namedCollarLiftPoint
    (A : AnalyticData)
    (C : (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius))
    (x : A.affineMarkedBand) :
    orderFourCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarGaugeEquiv A.periods
          A.starSeparation.orderFour.radius
          (A.affineOrderFourNamedCollarLiftPoint C x)) =
      (A.affineOrderFourNamedDiscLiftPoint x).1 := by
  apply regularFamilyInclusion_injective A.periods
  rw [regularFamilyInclusion_orderFourCollarToRegular]
  exact A.orderFourPrincipalGauge_namedCollarLiftPoint C x

/-- The named radial disc representative maps to the actual affine-disc endpoint in the central
family. -/
public theorem centralQuotientProjection_namedDiscLiftPoint
    (A : AnalyticData) (x : A.affineMarkedBand) :
    A.centralQuotientProjection
        (A.affineOrderFourNamedDiscLiftPoint x).1 =
      A.ellipticCentralImageHomeomorph
        ⟨(A.affineOrderFourDiscRegionEndpoint x).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            (fun z ↦ ‖(A.ellipticCentralCoordinate z).1 - 1‖)
            A.affineOrderFourMarkedDiscRadius
            (A.affineOrderFourDiscRegionEndpoint x).2⟩ := by
  rw [← A.toCentralFamily_affineOrderFourDiscRegionQuotientHomeomorph
    A.affineOrderFourMarkedDiscRadius
    (A.affineOrderFourDiscRegionEndpoint x)]
  rw [A.affineOrderFourDiscRegionQuotient_endpoint x]
  rfl

/-- The selected star-collar image of the named collar representative is the actual radial
disc endpoint. -/
public theorem starToCentral_namedCollarLiftPoint
    (A : AnalyticData)
    (C : (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius))
    (x : A.affineMarkedBand) :
    A.starToCentral 2
        (Quotient.mk _ (A.affineOrderFourNamedCollarLiftPoint C x)) =
      A.ellipticCentralImageHomeomorph
        ⟨(A.affineOrderFourDiscRegionEndpoint x).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            (fun z ↦ ‖(A.ellipticCentralCoordinate z).1 - 1‖)
            A.affineOrderFourMarkedDiscRadius
            (A.affineOrderFourDiscRegionEndpoint x).2⟩ := by
  rw [A.orderFourStarToCentral_mk]
  rw [A.orderFourCollarToRegular_namedCollarLiftPoint C x]
  exact A.centralQuotientProjection_namedDiscLiftPoint x

/-- Consequently the concrete overlap collar coordinate is the orbit class of the named collar
representative. -/
public theorem orderFourOverlapCollarHomeomorph_endpoint_eq_named
    (A : AnalyticData)
    (C : (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius))
    (x : A.affineMarkedBand) :
    A.orderFourOverlapCollarHomeomorph
        (A.affineOrderFourDiscOverlapEndpoint x) =
      Quotient.mk _ (A.affineOrderFourNamedCollarLiftPoint C x) := by
  apply (A.starToCentral_isOpenEmbedding (2 : Fin 3)).injective
  rw [A.starToCentral_orderFourOverlapCollarHomeomorph]
  rw [A.starToCentral_namedCollarLiftPoint C x]
  apply congrArg A.ellipticCentralImageHomeomorph
  apply Subtype.ext
  exact A.affineOrderFourDiscOverlapEndpoint_val x

/-- The single collar-membership fact implies the full representative-independent endpoint
real-period identity. -/
public theorem affineOrderFourEndpointRealPeriodIdentity
    (A : AnalyticData)
    (C : (∀ x : A.affineMarkedBand,
    A.affineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius)) :
    ∀ (x : A.affineMarkedBand)
      (q : (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier),
    A.orderFourOverlapCollarHomeomorph
        (A.affineOrderFourDiscOverlapEndpoint x) = Quotient.mk _ q →
      RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)
          ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderFourRadialActionData A.periods)).symm
              (orderFourRealPeriodProductHomeomorph A.periods q.1).2) =
        RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)
          ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderFourRadialActionData A.periods)).symm
              (-A.orderFourPrincipalRealPeriodGauge
                  (A.affineOrderFourRadialBaseLift
                    (A.affineBandStripCoordinate x)).1 +
                A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
                  (A.affineBandFiberCoordinateOfLift
                    A.affineNamedStripLift x))) := by
  intro x q hq
  let q₀ := A.affineOrderFourNamedCollarLiftPoint C x
  have hquot : (Quotient.mk _ q : A.StarCollarSource (2 : Fin 3)) =
      Quotient.mk _ q₀ := hq.symm.trans
        (A.orderFourOverlapCollarHomeomorph_endpoint_eq_named C x)
  have hquot' := congrArg
    (restrictedOrbitQuotientInclusion (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius)) hquot
  simp only [restrictedOrbitQuotientInclusion_mk] at hquot'
  rw [A.orderFourRealPeriodCentralProjection_eq_of_quotient_mk_eq q q₀ hquot']
  apply congrArg (RadialEllipticActionData.centralFiberCoverProjection
    (orderFourRadialActionData A.periods))
  apply congrArg (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderFourRadialActionData A.periods)).symm
  change (orderFourRealPeriodProductHomeomorph A.periods
      ((orderFourPrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (A.affineOrderFourNamedDiscLiftPoint x).1))).2 = _
  rw [A.orderFourRealPeriodProductHomeomorph_principalGauge_symm_snd]
  rw [familyTotalSpaceBase_regularFamilyInclusion,
    regularTotalSpaceBase_namedDiscLiftPoint x,
    orderFourRealPeriod_namedDiscLiftPoint x]

end SphereSixComplex.Geometry.AnalyticData

end
