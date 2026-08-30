module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourEndpointGaugeFormulaProof

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

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticHolomorphicLogCover
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The named marked-band point lifted to the order-four affine half-plane carrier. -/
public noncomputable def sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.orderFourAffineHalfPlaneLiftCarrier.carrier :=
  let z := A.sectionSevenAffineBandStripCoordinate x
  let t := A.sectionSevenAffineBandFiberCoordinateOfLift
    A.sectionSevenAffineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.sectionSevenAffineNamedStripLift.lift z
  ⟨projection (regularParameterMap A.periods)
      (b, A.regularFixedToMoving b v), by
    change 1 / 3 < (A.regularCoordinate b).1.re
    rw [A.sectionSevenAffineNamedStripLift.lift_coordinate]
    exact z.2.1⟩

/-- The corresponding point of the order-four affine disc carrier selected by the radial
inverse. -/
public noncomputable def sectionSevenAffineOrderFourNamedDiscLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (A.orderFourAffineDiscLiftCarrier
      A.sectionSevenAffineOrderFourMarkedDiscRadius).carrier :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderFourAffineRadialEquivChoice hr₀ hr).invFun
    (A.sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint x)

/-- The named half-plane lift represents exactly the actual marked-band point in the central
family. -/
public theorem sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint_toCentralFamily
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (Quotient.mk _ (A.sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint x)) =
      A.sectionSevenAffineCentralBandToCentralFamily
        A.sectionSevenAffineCentralSeparation
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x) := by
  rw [A.sectionSevenAffineBandPoint_toCentralFamily_eq_namedStripLiftPoint]
  unfold sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint
  let z := A.sectionSevenAffineBandStripCoordinate x
  let t := A.sectionSevenAffineBandFiberCoordinateOfLift
    A.sectionSevenAffineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.sectionSevenAffineNamedStripLift.lift z
  change A.centralQuotientProjection
      (projection (regularParameterMap A.periods)
        (b, A.regularFixedToMoving b v)) = A.stripLiftPoint
          A.sectionSevenAffineNamedStripLift z t
  rw [← A.stripLiftPoint_regularMovingToFixed
    A.sectionSevenAffineNamedStripLift z (A.regularFixedToMoving b v)]
  rw [A.regularMovingToFixed_regularFixedToMoving]
  simp [v]

/-- In the fixed order-four torus, the named half-plane lift has the marked band coordinate
transported from the common period basis. -/
public theorem orderFourRealPeriod_namedHalfPlaneLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint x).1)).2 =
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
        (A.sectionSevenAffineBandFiberCoordinateOfLift
          A.sectionSevenAffineNamedStripLift x) := by
  let z := A.sectionSevenAffineBandStripCoordinate x
  let t := A.sectionSevenAffineBandFiberCoordinateOfLift
    A.sectionSevenAffineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.sectionSevenAffineNamedStripLift.lift z
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
    {A : PaperAnalyticData}
    (x : A.SectionSevenAffineMarkedBand) :
    regularTotalSpaceBase A.periods
        (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 =
      A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x) := by
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  rw [sectionSevenAffineOrderFourNamedDiscLiftPoint,
    A.orderFourAffineRadialEquivChoice_invFun]
  rw [A.regularTotalSpaceBase_regularFlatTransport]
  rfl

/-- The explicit radial base lies in the chosen affine coordinate disc. -/
public theorem regularCoordinate_namedOrderFourRadialBaseLift_norm_lt_markedRadius
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ‖(A.regularCoordinate
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x))).1 - 1‖ <
      A.sectionSevenAffineOrderFourMarkedDiscRadius := by
  have h := (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).2
  change ‖(A.regularCoordinate
      (regularTotalSpaceBase A.periods
        (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1)).1 - 1‖ <
    A.sectionSevenAffineOrderFourMarkedDiscRadius at h
  rw [A.regularTotalSpaceBase_namedDiscLiftPoint x] at h
  exact h

/-- In particular, the quotient coordinate of the named radial base lies in the standard
order-four affine disc of radius `1/3`. -/
public theorem regularCoordinate_namedOrderFourRadialBaseLift_norm_lt_one_third
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ‖(A.regularCoordinate
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x))).1 - 1‖ < 1 / 3 :=
  (A.regularCoordinate_namedOrderFourRadialBaseLift_norm_lt_markedRadius x).trans_le
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1

/-- Affine radial transport preserves the named order-four real-period coordinate. -/
public theorem orderFourRealPeriod_namedDiscLiftPoint
    {A : PaperAnalyticData}
    (x : A.SectionSevenAffineMarkedBand) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1)).2 =
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
        (A.sectionSevenAffineBandFiberCoordinateOfLift
          A.sectionSevenAffineNamedStripLift x) := by
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  rw [sectionSevenAffineOrderFourNamedDiscLiftPoint,
    A.orderFourAffineRadialEquivChoice_invFun]
  rw [A.orderFourRealPeriodProductHomeomorph_regularFlatTransport_snd]
  exact A.orderFourRealPeriod_namedHalfPlaneLiftPoint x

/-- The central-region quotient coordinate of a marked band point is represented by its named
half-plane lift. -/
public theorem sectionSevenAffineOrderFourCentralRegionQuotient_band
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph
        (A.sectionSevenAffineBandToOrderFourCentralRegion x) =
      Quotient.mk _ (A.sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint x) := by
  apply A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  let u := A.sectionSevenAffineBandToOrderFourCentralRegion x
  let y : A.sectionSevenEllipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightUpperRegion
      A.sectionSevenEllipticCentralHeight (1 / 3 : ℝ) u.2⟩
  have hy : (1 : ℝ) / 3 < A.sectionSevenEllipticCentralHeight y := by
    obtain ⟨y', hy', hxy⟩ := u.2
    have hyy : y' = y := Subtype.ext hxy
    exact hyy ▸ hy'
  calc
    A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
        (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph u) =
        A.sectionSevenEllipticCentralImageHomeomorph y :=
      A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily_centralRegionQuotient y hy
    _ = A.sectionSevenAffineCentralBandToCentralFamily
          A.sectionSevenAffineCentralSeparation
            (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x) := rfl
    _ = A.orderFourAffineHalfPlaneLiftQuotientToCentralFamily
          (Quotient.mk _ (A.sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint x)) :=
      (A.sectionSevenAffineOrderFourNamedHalfPlaneLiftPoint_toCentralFamily x).symm

/-- The unembedded order-four affine-disc endpoint used inside the overlap endpoint. -/
public noncomputable def sectionSevenAffineOrderFourDiscRegionEndpoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderFourDiscRegion
      A.sectionSevenAffineOrderFourMarkedDiscRadius :=
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderFourAffineDiscCentralHomotopyEquiv hr₀ hr).invFun
    (A.sectionSevenAffineBandToOrderFourCentralRegion x)

/-- The affine-disc quotient coordinate of the endpoint is represented by the selected named
disc lift. -/
public theorem sectionSevenAffineOrderFourDiscRegionQuotient_endpoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph
        A.sectionSevenAffineOrderFourMarkedDiscRadius
        (A.sectionSevenAffineOrderFourDiscRegionEndpoint x) =
      Quotient.mk _ (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x) := by
  let r := A.sectionSevenAffineOrderFourMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.1
  let hr : r ≤ 1 - 1 / 3 :=
    A.sectionSevenAffineOrderFourMarkedDiscRadius_spec.2.1.trans (by norm_num)
  change A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r
      (A.sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph r |>.symm
        ((A.orderFourAffineRadialEquivChoice hr₀ hr).quotientInvFun
          (A.sectionSevenAffineOrderFourCentralRegionQuotientHomeomorph
            (A.sectionSevenAffineBandToOrderFourCentralRegion x)))) = _
  rw [Homeomorph.apply_symm_apply,
    A.sectionSevenAffineOrderFourCentralRegionQuotient_band x]
  rfl

/-- The overlap endpoint and the unembedded disc-region endpoint have the same underlying
elliptic-interior point. -/
public theorem sectionSevenAffineOrderFourDiscOverlapEndpoint_val
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (A.sectionSevenAffineOrderFourDiscOverlapEndpoint x).1 =
      (A.sectionSevenAffineOrderFourDiscRegionEndpoint x).1 :=
  rfl

/-- Undo the principal gauge on the named radial disc representative. -/
public noncomputable def sectionSevenAffineOrderFourNamedCollarTotalPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    TotalSpace (parameterMap A.periods) :=
  (orderFourPrincipalGaugeEquiv A.periods).symm
    (regularFamilyInclusion A.periods
      (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1)

/-- The genuinely geometric residue: the inverse-gauged named radial representative lies in the
selected order-four collar. -/
public structure SectionSevenAffineOrderFourNamedRadialCollarCompatibility
    (A : PaperAnalyticData) : Prop where
  collar_mem : ∀ x : A.SectionSevenAffineMarkedBand,
    A.sectionSevenAffineOrderFourNamedCollarTotalPoint x ∈
      orderFourPuncturedFamilyCollar A.periods A.starSeparation.orderFour.radius

/-- The collar radius of the inverse-gauged named representative is the Cayley radius of its
explicit radial base lift. -/
public theorem orderFourFamilyRadius_namedCollarTotalPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    orderFourFamilyRadius A.periods
        (A.sectionSevenAffineOrderFourNamedCollarTotalPoint x) =
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ := by
  rw [sectionSevenAffineOrderFourNamedCollarTotalPoint,
    orderFourFamilyRadius_principalGauge_symm,
    orderFourFamilyRadius.eq_def,
    familyTotalSpaceBase_regularFamilyInclusion,
    regularTotalSpaceBase_namedDiscLiftPoint]

/-- The named radial representative cannot hit the puncture, because its base belongs to the
regular source and the order-four Cayley centre lies over the excluded coordinate `1`. -/
public theorem orderFourFamilyRadius_namedCollarTotalPoint_pos
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    0 < orderFourFamilyRadius A.periods
      (A.sectionSevenAffineOrderFourNamedCollarTotalPoint x) := by
  rw [A.orderFourFamilyRadius_namedCollarTotalPoint x]
  apply norm_pos_iff.mpr
  apply coe_ne_zero_of_ne_center
  intro hzero
  have hfixed :
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 =
        fuchsianTwoFixedPoint := by
    apply orderFourCayleyHomeomorph.injective
    simpa [orderFourCayleyHomeomorph, cayleyHomeomorph, cayleyDiscCoordinate,
      discCenter, orderFourCayley_fixedPoint] using hzero
  have hregular :=
    (A.sectionSevenAffineOrderFourRadialBaseLift
      (A.sectionSevenAffineBandStripCoordinate x)).2
  have hmem := (A.isRegularBasePoint_iff_coordinate_mem _).mp hregular
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  exact hmem.2 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_two)

/-- Thus collar compatibility is equivalent to the sole remaining analytic inequality: the
chosen radial lift, rather than merely some regular-deck translate of it, lies inside the selected
order-four Cayley radius. -/
public theorem sectionSevenAffineOrderFourNamedRadialCollarCompatibility_iff
    (A : PaperAnalyticData) :
    A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility ↔
      ∀ x : A.SectionSevenAffineMarkedBand,
        ‖(orderFourCayleyHomeomorph
          (A.sectionSevenAffineOrderFourRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
          A.starSeparation.orderFour.radius := by
  constructor
  · intro C x
    have hx := C.collar_mem x
    change 0 < orderFourFamilyRadius A.periods
        (A.sectionSevenAffineOrderFourNamedCollarTotalPoint x) ∧
      orderFourFamilyRadius A.periods
        (A.sectionSevenAffineOrderFourNamedCollarTotalPoint x) <
          A.starSeparation.orderFour.radius at hx
    rw [A.orderFourFamilyRadius_namedCollarTotalPoint x] at hx
    exact hx.2
  · intro h
    refine ⟨fun x ↦ ?_⟩
    change 0 < orderFourFamilyRadius A.periods
        (A.sectionSevenAffineOrderFourNamedCollarTotalPoint x) ∧
      orderFourFamilyRadius A.periods
        (A.sectionSevenAffineOrderFourNamedCollarTotalPoint x) <
          A.starSeparation.orderFour.radius
    exact ⟨A.orderFourFamilyRadius_namedCollarTotalPoint_pos x, by
      rw [A.orderFourFamilyRadius_namedCollarTotalPoint x]
      exact h x⟩

/-- The named collar representative as a point of the affine collar carrier. -/
public noncomputable def sectionSevenAffineOrderFourNamedCollarLiftPoint
    (A : PaperAnalyticData)
    (C : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility)
    (x : A.SectionSevenAffineMarkedBand) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius).carrier :=
  ⟨A.sectionSevenAffineOrderFourNamedCollarTotalPoint x, C.collar_mem x⟩

/-- Gauging the named collar representative recovers the named radial disc representative. -/
public theorem orderFourPrincipalGauge_namedCollarLiftPoint
    (A : PaperAnalyticData)
    (C : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility)
    (x : A.SectionSevenAffineMarkedBand) :
    (orderFourPuncturedCollarGaugeEquiv A.periods
      A.starSeparation.orderFour.radius
      (A.sectionSevenAffineOrderFourNamedCollarLiftPoint C x)).1 =
        regularFamilyInclusion A.periods
          (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 := by
  change orderFourPrincipalGaugeEquiv A.periods
      ((orderFourPrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1)) = _
  exact (orderFourPrincipalGaugeEquiv A.periods).apply_symm_apply _

/-- The linear collar's regular representative of the named point is exactly the named radial
disc representative. -/
public theorem orderFourCollarToRegular_namedCollarLiftPoint
    (A : PaperAnalyticData)
    (C : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility)
    (x : A.SectionSevenAffineMarkedBand) :
    orderFourCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarGaugeEquiv A.periods
          A.starSeparation.orderFour.radius
          (A.sectionSevenAffineOrderFourNamedCollarLiftPoint C x)) =
      (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 := by
  apply regularFamilyInclusion_injective A.periods
  rw [regularFamilyInclusion_orderFourCollarToRegular]
  exact A.orderFourPrincipalGauge_namedCollarLiftPoint C x

/-- The named radial disc representative maps to the actual affine-disc endpoint in the central
family. -/
public theorem centralQuotientProjection_namedDiscLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.centralQuotientProjection
        (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨(A.sectionSevenAffineOrderFourDiscRegionEndpoint x).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖)
            A.sectionSevenAffineOrderFourMarkedDiscRadius
            (A.sectionSevenAffineOrderFourDiscRegionEndpoint x).2⟩ := by
  rw [← A.toCentralFamily_sectionSevenAffineOrderFourDiscRegionQuotientHomeomorph
    A.sectionSevenAffineOrderFourMarkedDiscRadius
    (A.sectionSevenAffineOrderFourDiscRegionEndpoint x)]
  rw [A.sectionSevenAffineOrderFourDiscRegionQuotient_endpoint x]
  rfl

/-- The selected star-collar image of the named collar representative is the actual radial
disc endpoint. -/
public theorem starToCentral_namedCollarLiftPoint
    (A : PaperAnalyticData)
    (C : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility)
    (x : A.SectionSevenAffineMarkedBand) :
    A.starToCentral 2
        (Quotient.mk _ (A.sectionSevenAffineOrderFourNamedCollarLiftPoint C x)) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨(A.sectionSevenAffineOrderFourDiscRegionEndpoint x).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            (fun z ↦ ‖(A.sectionSevenEllipticCentralCoordinate z).1 - 1‖)
            A.sectionSevenAffineOrderFourMarkedDiscRadius
            (A.sectionSevenAffineOrderFourDiscRegionEndpoint x).2⟩ := by
  rw [A.orderFourStarToCentral_mk]
  rw [A.orderFourCollarToRegular_namedCollarLiftPoint C x]
  exact A.centralQuotientProjection_namedDiscLiftPoint x

/-- Consequently the concrete overlap collar coordinate is the orbit class of the named collar
representative. -/
public theorem orderFourOverlapCollarHomeomorph_endpoint_eq_named
    (A : PaperAnalyticData)
    (C : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility)
    (x : A.SectionSevenAffineMarkedBand) :
    A.orderFourOverlapCollarHomeomorph
        (A.sectionSevenAffineOrderFourDiscOverlapEndpoint x) =
      Quotient.mk _ (A.sectionSevenAffineOrderFourNamedCollarLiftPoint C x) := by
  apply (A.starToCentral_isOpenEmbedding (2 : Fin 3)).injective
  rw [A.starToCentral_orderFourOverlapCollarHomeomorph]
  rw [A.starToCentral_namedCollarLiftPoint C x]
  apply congrArg A.sectionSevenEllipticCentralImageHomeomorph
  apply Subtype.ext
  exact A.sectionSevenAffineOrderFourDiscOverlapEndpoint_val x

/-- The single collar-membership fact implies the full representative-independent endpoint
real-period identity. -/
public theorem sectionSevenAffineOrderFourEndpointRealPeriodIdentity
    (A : PaperAnalyticData)
    (C : A.SectionSevenAffineOrderFourNamedRadialCollarCompatibility) :
    A.SectionSevenAffineOrderFourEndpointRealPeriodIdentity := by
  refine ⟨?_⟩
  intro x q hq
  let q₀ := A.sectionSevenAffineOrderFourNamedCollarLiftPoint C x
  have hquot : (Quotient.mk _ q : A.starCollarSourceType (2 : Fin 3)) =
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
          (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1))).2 = _
  rw [A.orderFourRealPeriodProductHomeomorph_principalGauge_symm_snd]
  rw [familyTotalSpaceBase_regularFamilyInclusion,
    regularTotalSpaceBase_namedDiscLiftPoint x,
    orderFourRealPeriod_namedDiscLiftPoint x]

end SphereSixComplex.Geometry.PaperAnalyticData

end
