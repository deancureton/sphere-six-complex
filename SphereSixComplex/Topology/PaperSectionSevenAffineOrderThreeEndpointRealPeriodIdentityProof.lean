module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderThreeEndpointGaugeFormulaProof

/-!
# Order-three endpoint real-period identity

The explicit order-three affine radial inverse is fibre transfer, so it preserves the fixed
order-three real-period coordinate.  This file constructs the named half-plane and disc
representatives and proves the endpoint identity from the exact remaining sheet-sensitive
Cayley-radius inequality.
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
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The marked-band point lifted to the order-three affine half-plane carrier. -/
public noncomputable def sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.orderThreeAffineHalfPlaneLiftCarrier.carrier :=
  let z := A.sectionSevenAffineBandStripCoordinate x
  let t := A.sectionSevenAffineBandFiberCoordinateOfLift
    A.sectionSevenAffineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.sectionSevenAffineNamedStripLift.lift z
  ⟨projection (regularParameterMap A.periods)
      (b, A.regularFixedToMoving b v), by
    change (A.regularCoordinate b).1.re < 2 / 3
    rw [A.sectionSevenAffineNamedStripLift.lift_coordinate]
    exact z.2.2⟩

/-- The corresponding point of the order-three affine disc carrier selected by the explicit
radial inverse. -/
public noncomputable def sectionSevenAffineOrderThreeNamedDiscLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (A.orderThreeAffineDiscLiftCarrier
      A.sectionSevenAffineOrderThreeMarkedDiscRadius).carrier := by
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  exact (A.orderThreeAffineRadialLiftEquiv
    (s := r / 2) (by linarith) (by linarith) hr).invFun
      (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x)

/-- The named half-plane lift represents the marked-band point in the central family. -/
public theorem sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint_toCentralFamily
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (Quotient.mk _ (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x)) =
      A.sectionSevenAffineCentralBandToCentralFamily
        A.sectionSevenAffineCentralSeparation
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x) := by
  rw [A.sectionSevenAffineBandPoint_toCentralFamily_eq_namedStripLiftPoint]
  unfold sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint
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

/-- In fixed order-three real-period coordinates, the named half-plane lift has the marked-band
fibre coordinate. -/
public theorem orderThreeRealPeriod_namedHalfPlaneLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x).1)).2 =
      A.sectionSevenAffineBandFiberCoordinateOfLift
        A.sectionSevenAffineNamedStripLift x := by
  let z := A.sectionSevenAffineBandStripCoordinate x
  let t := A.sectionSevenAffineBandFiberCoordinateOfLift
    A.sectionSevenAffineNamedStripLift x
  let v : ComplexTwoSpace := Quotient.out t
  let b := A.sectionSevenAffineNamedStripLift.lift z
  change (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (Quotient.mk _ (b, A.regularFixedToMoving b v)))).2 = t
  rw [regularFamilyInclusion_mk, orderThreeRealPeriodProductHomeomorph_mk]
  rw [← Quotient.out_eq t]
  apply congrArg (Quotient.mk _)
  let p₃ := parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
  let pᵦ := regularParameterMap A.periods b
  change (FullRank.ofSetupInequalities p₃.1 p₃.2).realEquiv
      ((FullRank.ofSetupInequalities pᵦ.1 pᵦ.2).realEquiv.symm
        ((FullRank.ofSetupInequalities pᵦ.1 pᵦ.2).realEquiv
          ((FullRank.ofSetupInequalities p₃.1 p₃.2).realEquiv.symm v))) = v
  rw [(FullRank.ofSetupInequalities pᵦ.1 pᵦ.2).realEquiv.symm_apply_apply]
  exact (FullRank.ofSetupInequalities p₃.1 p₃.2).realEquiv.apply_symm_apply v

/-- The named disc lift lies over the explicit order-three radial base. -/
public theorem regularTotalSpaceBase_namedOrderThreeDiscLiftPoint
    {A : PaperAnalyticData} (x : A.SectionSevenAffineMarkedBand) :
    regularTotalSpaceBase A.periods
        (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 =
      A.sectionSevenAffineOrderThreeRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x) := by
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  change regularTotalSpaceBase A.periods
      (A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv (s := r / 2)
          (by linarith) (by linarith) hr).invFun
            (A.orderThreeHalfPlaneLiftBase
              (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x))).1
        (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x).1) = _
  rw [A.regularTotalSpaceBase_fiberTransfer]
  rfl

/-- The normalized modular coordinate of the named radial base lies in the selected affine
disc. -/
public theorem regularCoordinate_namedOrderThreeRadialBaseLift_norm_lt_markedRadius
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ‖(A.regularCoordinate
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x))).1‖ <
      A.sectionSevenAffineOrderThreeMarkedDiscRadius := by
  have h := (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).2
  change ‖(A.regularCoordinate
      (regularTotalSpaceBase A.periods
        (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1)).1‖ <
    A.sectionSevenAffineOrderThreeMarkedDiscRadius at h
  rw [A.regularTotalSpaceBase_namedOrderThreeDiscLiftPoint x] at h
  exact h

/-- In particular the named radial base has normalized modular coordinate of norm below
`1/3`. -/
public theorem regularCoordinate_namedOrderThreeRadialBaseLift_norm_lt_one_third
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ‖(A.regularCoordinate
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x))).1‖ < 1 / 3 :=
  (A.regularCoordinate_namedOrderThreeRadialBaseLift_norm_lt_markedRadius x).trans_le
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1

/-- Order-three affine radial transport preserves the named real-period coordinate. -/
public theorem orderThreeRealPeriod_namedDiscLiftPoint
    {A : PaperAnalyticData} (x : A.SectionSevenAffineMarkedBand) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1)).2 =
      A.sectionSevenAffineBandFiberCoordinateOfLift
        A.sectionSevenAffineNamedStripLift x := by
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  change (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.fiberTransfer
          ((A.orderThreeBaseRadialEquiv (s := r / 2)
            (by linarith) (by linarith) hr).invFun
              (A.orderThreeHalfPlaneLiftBase
                (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x))).1
          (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x).1))).2 = _
  rw [A.orderThreeRealPeriodProductHomeomorph_fiberTransfer_snd]
  exact A.orderThreeRealPeriod_namedHalfPlaneLiftPoint x

/-- The central-region quotient coordinate of the marked-band point is represented by its
named order-three half-plane lift. -/
public theorem sectionSevenAffineOrderThreeCentralRegionQuotient_band
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph
        (A.sectionSevenAffineBandToOrderThreeCentralRegion x) =
      Quotient.mk _ (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x) := by
  apply A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily_isOpenEmbedding.injective
  let u := A.sectionSevenAffineBandToOrderThreeCentralRegion x
  let y : A.sectionSevenEllipticCentralImage :=
    ⟨u.1, A.mem_centralImage_of_mem_centralHeightLowerRegion
      A.sectionSevenEllipticCentralHeight (2 / 3 : ℝ) u.2⟩
  have hy : A.sectionSevenEllipticCentralHeight y < (2 : ℝ) / 3 := by
    obtain ⟨y', hy', hxy⟩ := u.2
    have hyy : y' = y := Subtype.ext hxy
    exact hyy ▸ hy'
  calc
    A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
        (A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph u) =
        A.sectionSevenEllipticCentralImageHomeomorph y :=
      A.toCentralFamily_sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph u
    _ = A.sectionSevenAffineCentralBandToCentralFamily
          A.sectionSevenAffineCentralSeparation
            (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x) := rfl
    _ = A.orderThreeAffineHalfPlaneLiftQuotientToCentralFamily
          (Quotient.mk _ (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint x)) :=
      (A.sectionSevenAffineOrderThreeNamedHalfPlaneLiftPoint_toCentralFamily x).symm

/-- The unembedded order-three affine-disc endpoint. -/
public noncomputable def sectionSevenAffineOrderThreeDiscRegionEndpoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderThreeDiscRegion
      A.sectionSevenAffineOrderThreeMarkedDiscRadius :=
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  (A.orderThreeAffineDiscCentralHomotopyEquiv hr₀ hr).invFun
    (A.sectionSevenAffineBandToOrderThreeCentralRegion x)

/-- Its affine-disc quotient coordinate is the selected named disc lift. -/
public theorem sectionSevenAffineOrderThreeDiscRegionQuotient_endpoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph
        A.sectionSevenAffineOrderThreeMarkedDiscRadius
        (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x) =
      Quotient.mk _ (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x) := by
  let r := A.sectionSevenAffineOrderThreeMarkedDiscRadius
  let hr₀ := A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.1
  let hr : r ≤ 2 / 3 :=
    A.sectionSevenAffineOrderThreeMarkedDiscRadius_spec.2.1.trans (by norm_num)
  change A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r
      (A.sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph r |>.symm
        ((A.orderThreeAffineRadialLiftEquiv
          (s := r / 2) (by linarith) (by linarith) hr).quotientInvFun
          (A.sectionSevenAffineOrderThreeCentralRegionQuotientHomeomorph
            (A.sectionSevenAffineBandToOrderThreeCentralRegion x)))) = _
  rw [Homeomorph.apply_symm_apply,
    A.sectionSevenAffineOrderThreeCentralRegionQuotient_band x]
  rfl

/-- The overlap endpoint and the disc-region endpoint have the same underlying point. -/
public theorem sectionSevenAffineOrderThreeDiscOverlapEndpoint_val
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    (A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x).1 =
      (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).1 :=
  rfl

/-- Undo the principal gauge on the named radial disc representative. -/
public noncomputable def sectionSevenAffineOrderThreeNamedCollarTotalPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    TotalSpace (parameterMap A.periods) :=
  (orderThreePrincipalGaugeEquiv A.periods).symm
    (regularFamilyInclusion A.periods
      (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1)

/-- Its collar radius is the Cayley radius of the explicit radial base lift. -/
public theorem orderThreeFamilyRadius_namedCollarTotalPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) =
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ := by
  rw [sectionSevenAffineOrderThreeNamedCollarTotalPoint,
    orderThreeFamilyRadius_principalGauge_symm,
    orderThreeFamilyRadius.eq_def,
    familyTotalSpaceBase_regularFamilyInclusion,
    regularTotalSpaceBase_namedOrderThreeDiscLiftPoint]

/-- The named representative does not hit the order-three puncture. -/
public theorem orderThreeFamilyRadius_namedCollarTotalPoint_pos
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    0 < orderThreeFamilyRadius A.periods
      (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) := by
  rw [A.orderThreeFamilyRadius_namedCollarTotalPoint x]
  apply norm_pos_iff.mpr
  apply coe_ne_zero_of_ne_center
  intro hzero
  have hfixed :
      (A.sectionSevenAffineOrderThreeRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 =
        fuchsianOneFixedPoint := by
    apply orderThreeCayleyHomeomorph.injective
    simpa [orderThreeCayleyHomeomorph, cayleyHomeomorph, cayleyDiscCoordinate,
      discCenter, orderThreeCayley_fixedPoint] using hzero
  have hregular :=
    (A.sectionSevenAffineOrderThreeRadialBaseLift
      (A.sectionSevenAffineBandStripCoordinate x)).2
  have hmem := (A.isRegularBasePoint_iff_coordinate_mem _).mp hregular
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
  exact hmem.1 (hfixed ▸ A.modular.sourceCoordinate.coordinate_at_one)

/-- Membership of the named inverse-gauged representative in the selected collar is equivalent
to the single sheet-sensitive Cayley inequality. -/
public theorem sectionSevenAffineOrderThreeNamedCollarTotalPoint_mem_iff
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x ∈
        orderThreePuncturedFamilyCollar A.periods
          A.starSeparation.orderThree.radius ↔
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
  constructor
  · intro hx
    change 0 < orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) ∧
      orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) <
          A.starSeparation.orderThree.radius at hx
    rw [A.orderThreeFamilyRadius_namedCollarTotalPoint x] at hx
    exact hx.2
  · intro hx
    change 0 < orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) ∧
      orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) <
          A.starSeparation.orderThree.radius
    exact ⟨A.orderThreeFamilyRadius_namedCollarTotalPoint_pos x, by
      rw [A.orderThreeFamilyRadius_namedCollarTotalPoint x]
      exact hx⟩

/-- The established overlap inclusion supplies the selected Cayley bound after some regular
deck translation of the named radial base. -/
public theorem exists_regularDeck_namedOrderThreeRadialBase_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ∃ g : Delta,
      ‖(orderThreeCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderThreeRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderThree.radius := by
  let u := A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x
  let z := A.orderThreeOverlapCollarHomeomorph u
  let q := Quotient.out z
  have hq : Quotient.mk _ q = z := Quotient.out_eq z
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let qreg : RegularTotalSpace A.periods :=
    orderThreeCollarToRegular A.periods hproper
      A.starSeparation.orderThree.sourceData
      (orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius q)
  have hstar : A.starToCentral 1 z =
      A.centralQuotientProjection
        (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 := by
    have hend : A.centralQuotientProjection
          (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 =
        A.sectionSevenEllipticCentralImageHomeomorph
          ⟨(A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).1,
            A.mem_centralImage_of_mem_centralHeightLowerRegion
              A.sectionSevenEllipticCentralRadius
              A.sectionSevenAffineOrderThreeMarkedDiscRadius
              (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).2⟩ := by
      rw [← A.toCentralFamily_sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph
        A.sectionSevenAffineOrderThreeMarkedDiscRadius
        (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x)]
      rw [A.sectionSevenAffineOrderThreeDiscRegionQuotient_endpoint x]
      rfl
    rw [show z = A.orderThreeOverlapCollarHomeomorph u by rfl]
    rw [A.starToCentral_orderThreeOverlapCollarHomeomorph]
    rw [hend]
    apply congrArg A.sectionSevenEllipticCentralImageHomeomorph
    apply Subtype.ext
    exact A.sectionSevenAffineOrderThreeDiscOverlapEndpoint_val x
  have hcentral : A.centralQuotientProjection qreg =
      A.centralQuotientProjection
        (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 := by
    rw [← A.orderThreeStarToCentral_mk q, hq]
    exact hstar
  let _ := regularFamilyDeckAction A.periods
  rw [centralQuotientProjection.eq_def] at hcentral
  have hrel := Quotient.exact hcentral
  change MulAction.orbitRel Delta _ qreg
    (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  change regularFamilyDeckMap A.periods g
      (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 = qreg at hg
  refine ⟨g, ?_⟩
  have hbase : fuchsianSourceAction g •
      (A.sectionSevenAffineOrderThreeRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 =
      (regularTotalSpaceBase A.periods qreg).1 := by
    rw [← A.regularTotalSpaceBase_namedOrderThreeDiscLiftPoint x]
    rw [← hg, regularTotalSpaceBase_familyDeckMap]
    rfl
  rw [hbase]
  have hqmem := q.property
  change 0 < orderThreeFamilyRadius A.periods q.1 ∧
    orderThreeFamilyRadius A.periods q.1 <
      A.starSeparation.orderThree.radius at hqmem
  have hqradius : ‖(orderThreeCayleyHomeomorph
      (familyTotalSpaceBase A.periods q.1) : ℂ)‖ <
      A.starSeparation.orderThree.radius := by
    simpa only [orderThreeFamilyRadius.eq_def] using hqmem.2
  have hqregbase : (regularTotalSpaceBase A.periods qreg).1 =
      familyTotalSpaceBase A.periods q.1 := by
    have hinc := regularFamilyInclusion_orderThreeCollarToRegular A.periods hproper
      A.starSeparation.orderThree.sourceData
      (orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius q)
    have hb := congrArg (familyTotalSpaceBase A.periods) hinc
    change familyTotalSpaceBase A.periods
        (regularFamilyInclusion A.periods qreg) =
      familyTotalSpaceBase A.periods
        (orderThreePrincipalGaugeEquiv A.periods q.1) at hb
    rw [familyTotalSpaceBase_regularFamilyInclusion] at hb
    exact hb.trans (familyTotalSpaceBase_orderThreePrincipalGauge A.periods q.1)
  rw [hqregbase]
  exact hqradius

/-- Under the exact Cayley bound, the named representative is a point of the selected affine
collar carrier. -/
public noncomputable def sectionSevenAffineOrderThreeNamedCollarLiftPoint
    (A : PaperAnalyticData)
    (h : ∀ x : A.SectionSevenAffineMarkedBand,
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius)
    (x : A.SectionSevenAffineMarkedBand) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius).carrier :=
  ⟨A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x, by
    change 0 < orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) ∧
      orderThreeFamilyRadius A.periods
        (A.sectionSevenAffineOrderThreeNamedCollarTotalPoint x) <
          A.starSeparation.orderThree.radius
    exact ⟨A.orderThreeFamilyRadius_namedCollarTotalPoint_pos x, by
      rw [A.orderThreeFamilyRadius_namedCollarTotalPoint x]
      exact h x⟩⟩

/-- Gauging the named collar point recovers the named radial disc representative. -/
public theorem orderThreePrincipalGauge_namedCollarLiftPoint
    (A : PaperAnalyticData)
    (h : ∀ x : A.SectionSevenAffineMarkedBand,
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius)
    (x : A.SectionSevenAffineMarkedBand) :
    (orderThreePuncturedCollarGaugeEquiv A.periods
      A.starSeparation.orderThree.radius
      (A.sectionSevenAffineOrderThreeNamedCollarLiftPoint h x)).1 =
        regularFamilyInclusion A.periods
          (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 := by
  change orderThreePrincipalGaugeEquiv A.periods
      ((orderThreePrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1)) = _
  exact (orderThreePrincipalGaugeEquiv A.periods).apply_symm_apply _

/-- The linear collar's regular representative is the named radial disc representative. -/
public theorem orderThreeCollarToRegular_namedCollarLiftPoint
    (A : PaperAnalyticData)
    (h : ∀ x : A.SectionSevenAffineMarkedBand,
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius)
    (x : A.SectionSevenAffineMarkedBand) :
    orderThreeCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction)
        A.starSeparation.orderThree.sourceData
        (orderThreePuncturedCollarGaugeEquiv A.periods
          A.starSeparation.orderThree.radius
          (A.sectionSevenAffineOrderThreeNamedCollarLiftPoint h x)) =
      (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 := by
  apply regularFamilyInclusion_injective A.periods
  rw [regularFamilyInclusion_orderThreeCollarToRegular]
  exact A.orderThreePrincipalGauge_namedCollarLiftPoint h x

/-- The named radial disc representative maps to the actual affine-disc endpoint. -/
public theorem centralQuotientProjection_namedOrderThreeDiscLiftPoint
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    A.centralQuotientProjection
        (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1 =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨(A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            A.sectionSevenEllipticCentralRadius
            A.sectionSevenAffineOrderThreeMarkedDiscRadius
            (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).2⟩ := by
  rw [← A.toCentralFamily_sectionSevenAffineOrderThreeDiscRegionQuotientHomeomorph
    A.sectionSevenAffineOrderThreeMarkedDiscRadius
    (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x)]
  rw [A.sectionSevenAffineOrderThreeDiscRegionQuotient_endpoint x]
  rfl

/-- The selected star-collar image of the named representative is the radial endpoint. -/
public theorem starToCentral_namedOrderThreeCollarLiftPoint
    (A : PaperAnalyticData)
    (h : ∀ x : A.SectionSevenAffineMarkedBand,
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius)
    (x : A.SectionSevenAffineMarkedBand) :
    A.starToCentral 1
        (Quotient.mk _ (A.sectionSevenAffineOrderThreeNamedCollarLiftPoint h x)) =
      A.sectionSevenEllipticCentralImageHomeomorph
        ⟨(A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).1,
          A.mem_centralImage_of_mem_centralHeightLowerRegion
            A.sectionSevenEllipticCentralRadius
            A.sectionSevenAffineOrderThreeMarkedDiscRadius
            (A.sectionSevenAffineOrderThreeDiscRegionEndpoint x).2⟩ := by
  rw [A.orderThreeStarToCentral_mk]
  rw [A.orderThreeCollarToRegular_namedCollarLiftPoint h x]
  exact A.centralQuotientProjection_namedOrderThreeDiscLiftPoint x

/-- The concrete overlap collar coordinate is the orbit class of the named representative. -/
public theorem orderThreeOverlapCollarHomeomorph_endpoint_eq_named
    (A : PaperAnalyticData)
    (h : ∀ x : A.SectionSevenAffineMarkedBand,
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius)
    (x : A.SectionSevenAffineMarkedBand) :
    A.orderThreeOverlapCollarHomeomorph
        (A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x) =
      Quotient.mk _ (A.sectionSevenAffineOrderThreeNamedCollarLiftPoint h x) := by
  apply (A.starToCentral_isOpenEmbedding (1 : Fin 3)).injective
  rw [A.starToCentral_orderThreeOverlapCollarHomeomorph]
  rw [A.starToCentral_namedOrderThreeCollarLiftPoint h x]
  apply congrArg A.sectionSevenEllipticCentralImageHomeomorph
  apply Subtype.ext
  exact A.sectionSevenAffineOrderThreeDiscOverlapEndpoint_val x

/-- The exact named-sheet Cayley bound implies the full representative-independent order-three
endpoint real-period identity. -/
public theorem sectionSevenAffineOrderThreeEndpointRealPeriodIdentity
    (A : PaperAnalyticData)
    (h : ∀ x : A.SectionSevenAffineMarkedBand,
      ‖(orderThreeCayleyHomeomorph
        (A.sectionSevenAffineOrderThreeRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
        A.starSeparation.orderThree.radius) :
    A.SectionSevenAffineOrderThreeEndpointRealPeriodIdentity := by
  refine ⟨?_⟩
  intro x q hq
  let q₀ := A.sectionSevenAffineOrderThreeNamedCollarLiftPoint h x
  have hquot : (Quotient.mk _ q : A.starCollarSourceType (1 : Fin 3)) =
      Quotient.mk _ q₀ := hq.symm.trans
        (A.orderThreeOverlapCollarHomeomorph_endpoint_eq_named h x)
  have hquot' := congrArg
    (restrictedOrbitQuotientInclusion (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius)) hquot
  simp only [restrictedOrbitQuotientInclusion_mk] at hquot'
  rw [A.orderThreeRealPeriodCentralProjection_eq_of_quotient_mk_eq q q₀ hquot']
  apply congrArg (RadialEllipticActionData.centralFiberCoverProjection
    (orderThreeRadialActionData A.periods))
  apply congrArg (RadialEllipticActionData.centralFiberCoverSourceHomeomorph
    (orderThreeRadialActionData A.periods)).symm
  change (orderThreeRealPeriodProductHomeomorph A.periods
      ((orderThreePrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (A.sectionSevenAffineOrderThreeNamedDiscLiftPoint x).1))).2 = _
  rw [A.orderThreeRealPeriodProductHomeomorph_principalGauge_symm_snd]
  rw [familyTotalSpaceBase_regularFamilyInclusion,
    regularTotalSpaceBase_namedOrderThreeDiscLiftPoint x,
    orderThreeRealPeriod_namedDiscLiftPoint x,
    A.sectionSevenAffineOrderThreeEndpointGauge_apply]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
