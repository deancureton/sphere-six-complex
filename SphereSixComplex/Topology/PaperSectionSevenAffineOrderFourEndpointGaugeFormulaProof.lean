module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandHomotopiesCompletion
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandHomotopiesProof
public import SphereSixComplex.Topology.PaperSectionSevenAffineEndpointRadialBaseComparison

/-!
# The order-four affine endpoint gauge formula

The principal logarithmic gauge is a fibre translation.  In fixed order-four real-period
coordinates its effect is addition by a torus element depending only on the regular base.  The
resulting gauge is transported back to the common order-three band torus before it is added to
the fibre coordinate of the named strip lift.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticHolomorphicLogCover
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

/-- The period-basis transport used for the duplicated band preserves addition. -/
public theorem duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph_add
    (A : PaperAnalyticData)
    (x y : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph (x + y) =
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph x +
        A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph y := by
  induction x using Quotient.inductionOn with
  | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
          let p₄ := parameterMap A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo
          let e : ComplexTwoSpace ≃L[ℝ] ComplexTwoSpace :=
            A.duplicatedSectionSevenBandFullRank.realEquiv.symm.trans
              (FullRank.ofSetupInequalities p₄.1 p₄.2).realEquiv
          change Quotient.mk _ (e (x + y)) =
            Quotient.mk _ (e x) + Quotient.mk _ (e y)
          rw [map_add, additiveTorus_mk_add]

/-- The order-four principal translation, expressed in the fixed real-period torus. -/
public noncomputable def orderFourPrincipalRealPeriodGauge
    (A : PaperAnalyticData)
    (z : UpperHalfPlane) :
    AdditiveTorus
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 :=
  Quotient.mk _
    (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zTwo
      (z, orderFourPrincipalGaugeSection A.periods z)).2

/-- The principal gauge changes only the fixed real-period fibre coordinate, by addition of its
base-dependent gauge element. -/
public theorem orderFourRealPeriodProductHomeomorph_principalGauge_snd
    (A : PaperAnalyticData) (q : TotalSpace (parameterMap A.periods)) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (orderFourPrincipalGaugeEquiv A.periods q)).2 =
      A.orderFourPrincipalRealPeriodGauge (familyTotalSpaceBase A.periods q) +
        (orderFourRealPeriodProductHomeomorph A.periods q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
      rcases p with ⟨z, v⟩
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp only [one_smul, familyTotalSpaceBase_mk,
        familyTranslationCover.eq_def]
      simp [movingToFixedCover, periodCoordinates, map_add]

/-- Undoing the principal gauge subtracts the same base-dependent fixed real-period element. -/
public theorem orderFourRealPeriodProductHomeomorph_principalGauge_symm_snd
    (A : PaperAnalyticData) (q : TotalSpace (parameterMap A.periods)) :
    (orderFourRealPeriodProductHomeomorph A.periods
      ((orderFourPrincipalGaugeEquiv A.periods).symm q)).2 =
      -A.orderFourPrincipalRealPeriodGauge (familyTotalSpaceBase A.periods q) +
        (orderFourRealPeriodProductHomeomorph A.periods q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
      rcases p with ⟨z, v⟩
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp only [one_smul, familyTotalSpaceBase_mk,
        familyTranslationCover.eq_def]
      simp [movingToFixedCover, periodCoordinates, map_add]

/-- The zero vector over the explicit order-four radial strip lift lies in a fixed punctured
collar of radius two. -/
public noncomputable def sectionSevenAffineOrderFourRadialZeroCollarPoint
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      orderFourPuncturedFamilyCollar A.periods 2) :=
  ⟨fun z ↦
      ⟨regularFamilyInclusion A.periods
          (regularFamilyZeroSection A.periods
            (A.sectionSevenAffineOrderFourRadialBaseLift z)), by
        constructor
        · rw [orderFourFamilyRadius.eq_def,
            familyTotalSpaceBase_regularFamilyInclusion]
          change 0 < ‖(orderFourCayleyHomeomorph
            (A.sectionSevenAffineOrderFourRadialBaseLift z).1 : ℂ)‖
          rw [norm_pos_iff]
          apply coe_ne_zero_of_ne_center
          intro hcenter
          have hbase :
              (A.sectionSevenAffineOrderFourRadialBaseLift z).1 =
                A.modular.modularParameter.toTriangleUniformization.zTwo := by
            apply orderFourCayleyHomeomorph.injective
            refine hcenter.trans ?_
            rw [(ellipticFixedPoints_eq_of_fuchsian
              A.modular.modularParameter.toTriangleUniformization_sourceAction).2]
            apply Subtype.ext
            exact orderFourCayley_fixedPoint.symm
          have hregular := (A.sectionSevenAffineOrderFourRadialBaseLift z).2
          have hnot := (isRegularBasePoint_iff_not_mem_orbits
            (U := A.modular.modularParameter.toTriangleUniformization)
            (A.sectionSevenAffineOrderFourRadialBaseLift z).1).mp hregular
          apply hnot
          right
          rw [sourceOrbitSet]
          simp only [Set.mem_iUnion, Set.mem_singleton_iff]
          refine ⟨1, ?_⟩
          simpa using hbase
        · rw [orderFourFamilyRadius.eq_def,
            familyTotalSpaceBase_regularFamilyInclusion]
          exact (norm_orderFourCayley_lt_one
            (A.sectionSevenAffineOrderFourRadialBaseLift z).1).trans (by norm_num)⟩,
    (regularFamilyInclusion_continuous A.periods).comp
      ((regularFamilyZeroSection A.periods).continuous.comp
        A.sectionSevenAffineOrderFourRadialBaseLift.continuous) |>.subtype_mk _⟩

/-- The explicit continuous order-four strip gauge, transported back to the common band torus. -/
public noncomputable def sectionSevenAffineOrderFourEndpointGauge
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  let _ := A.totalSpaceCharts
  let e := orderFourPuncturedCollarGaugeHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph 2
  ⟨fun z ↦ A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.symm
      (orderFourRealPeriodProductHomeomorph A.periods
        (e.symm (A.sectionSevenAffineOrderFourRadialZeroCollarPoint z)).1).2,
    A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.symm.continuous.comp
      (continuous_snd.comp
        ((orderFourRealPeriodProductHomeomorph A.periods).continuous.comp
          (continuous_subtype_val.comp
            (e.symm.continuous.comp
              A.sectionSevenAffineOrderFourRadialZeroCollarPoint.continuous))))⟩

/-- Pointwise, the common-band gauge is the inverse period-basis transport of the negative
order-four principal real-period gauge. -/
public theorem sectionSevenAffineOrderFourEndpointGauge_apply
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip) :
    A.sectionSevenAffineOrderFourEndpointGauge z =
      A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.symm
        (-A.orderFourPrincipalRealPeriodGauge
          (A.sectionSevenAffineOrderFourRadialBaseLift z).1) := by
  let _ := A.totalSpaceCharts
  rw [sectionSevenAffineOrderFourEndpointGauge]
  apply congrArg A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.symm
  change (orderFourRealPeriodProductHomeomorph A.periods
      ((orderFourPrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (regularFamilyZeroSection A.periods
            (A.sectionSevenAffineOrderFourRadialBaseLift z))))).2 = _
  rw [A.orderFourRealPeriodProductHomeomorph_principalGauge_symm_snd]
  simp only [regularFamilyZeroSection_apply, regularFamilyInclusion_mk,
    regularBundleInclusion]
  rw [orderFourRealPeriodProductHomeomorph_mk]
  simp [movingToFixedCover, periodCoordinates]
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zTwo).1
  change -A.orderFourPrincipalRealPeriodGauge
      (A.sectionSevenAffineOrderFourRadialBaseLift z).1 +
        (Quotient.mk _ (0 : ComplexTwoSpace) : AdditiveTorus p) =
    -A.orderFourPrincipalRealPeriodGauge
      (A.sectionSevenAffineOrderFourRadialBaseLift z).1
  calc
    _ = -A.orderFourPrincipalRealPeriodGauge
          (A.sectionSevenAffineOrderFourRadialBaseLift z).1 +
        (0 : AdditiveTorus p) := congrArg _ (additiveTorus_mk_zero p)
    _ = _ := add_zero _

/-- The remaining representative-level identity after the explicit gauge and all continuous
maps have been constructed.  It is stated in the fixed order-four torus: the endpoint coordinate
is the negative principal gauge plus the transported named-strip fibre coordinate. -/
public structure SectionSevenAffineOrderFourEndpointRealPeriodIdentity
    (A : PaperAnalyticData) : Prop where
  eq_projection : ∀ (x : A.SectionSevenAffineMarkedBand)
      (q : (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier),
    A.orderFourOverlapCollarHomeomorph
        (A.sectionSevenAffineOrderFourDiscOverlapEndpoint x) = Quotient.mk _ q →
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
                  (A.sectionSevenAffineOrderFourRadialBaseLift
                    (A.sectionSevenAffineBandStripCoordinate x)).1 +
                A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
                  (A.sectionSevenAffineBandFiberCoordinateOfLift
                    A.sectionSevenAffineNamedStripLift x)))

/-- The representative-level identity gives exactly the order-four field of the pinned-lift
endpoint-gauge formulas. -/
public theorem sectionSevenAffineOrderFourEndpointGaugeFormula
    (A : PaperAnalyticData)
    (H : A.SectionSevenAffineOrderFourEndpointRealPeriodIdentity) :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint =
      A.sectionSevenAffineOrderFourGaugeProjectionOfLift
        A.sectionSevenAffineNamedStripLift
        A.sectionSevenAffineOrderFourEndpointGauge := by
  apply ContinuousMap.ext
  intro x
  let u := A.sectionSevenAffineOrderFourDiscOverlapEndpoint x
  change (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u)) = _
  generalize hq : A.orderFourOverlapCollarHomeomorph u = y
  induction y using Quotient.inductionOn with
  | _ q =>
      rw [orderFourSelectedFilling_toFun_starToFilling_mk]
      rw [H.eq_projection x q hq]
      change RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)
          ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderFourRadialActionData A.periods)).symm
              (-A.orderFourPrincipalRealPeriodGauge
                  (A.sectionSevenAffineOrderFourRadialBaseLift
                    (A.sectionSevenAffineBandStripCoordinate x)).1 +
                A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph
                  (A.sectionSevenAffineBandFiberCoordinateOfLift
                    A.sectionSevenAffineNamedStripLift x))) =
        RadialEllipticActionData.centralFiberCoverProjection
          (orderFourRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderFourCoverSource
            (A.sectionSevenAffineOrderFourEndpointGauge
                (A.sectionSevenAffineBandStripCoordinate x) +
              A.sectionSevenAffineBandFiberCoordinateOfLift
                A.sectionSevenAffineNamedStripLift x))
      rw [duplicatedSectionSevenBandToOrderFourCoverSource]
      simp only [Homeomorph.trans_apply]
      congr 2
      rw [A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph_add,
        A.sectionSevenAffineOrderFourEndpointGauge_apply]
      congr 1
      exact
        (A.duplicatedSectionSevenOrderThreeToOrderFourBandHomeomorph.apply_symm_apply _).symm

end SphereSixComplex.Geometry.PaperAnalyticData

end
