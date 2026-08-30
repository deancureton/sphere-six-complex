module

public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandHomotopiesCompletion
public import SphereSixComplex.Topology.PaperSectionSevenAffineMarkedBandHomotopiesProof
public import SphereSixComplex.Topology.PaperSectionSevenAffineEndpointRadialBaseComparison

/-!
# The order-three affine endpoint gauge formula

The principal logarithmic gauge is a fibre translation.  In fixed order-three real-period
coordinates its effect is addition by a torus element depending only on the regular base.
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

/-- The order-three principal translation, expressed in the fixed real-period torus. -/
public noncomputable def orderThreePrincipalRealPeriodGauge
    (A : PaperAnalyticData)
    (z : UpperHalfPlane) :
    AdditiveTorus
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 :=
  Quotient.mk _
    (movingToFixedCover A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne
      (z, orderThreePrincipalGaugeSection A.periods z)).2

/-- The principal gauge changes only the fixed real-period fibre coordinate, by addition of its
base-dependent gauge element. -/
public theorem orderThreeRealPeriodProductHomeomorph_principalGauge_snd
    (A : PaperAnalyticData) (q : TotalSpace (parameterMap A.periods)) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      (orderThreePrincipalGaugeEquiv A.periods q)).2 =
      A.orderThreePrincipalRealPeriodGauge (familyTotalSpaceBase A.periods q) +
        (orderThreeRealPeriodProductHomeomorph A.periods q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
      rcases p with ⟨z, v⟩
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp only [one_smul, familyTotalSpaceBase_mk,
        familyTranslationCover.eq_def]
      simp [movingToFixedCover, periodCoordinates, map_add]

/-- Undoing the principal gauge subtracts the same base-dependent fixed real-period element. -/
public theorem orderThreeRealPeriodProductHomeomorph_principalGauge_symm_snd
    (A : PaperAnalyticData) (q : TotalSpace (parameterMap A.periods)) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      ((orderThreePrincipalGaugeEquiv A.periods).symm q)).2 =
      -A.orderThreePrincipalRealPeriodGauge (familyTotalSpaceBase A.periods q) +
        (orderThreeRealPeriodProductHomeomorph A.periods q).2 := by
  induction q using Quotient.inductionOn with
  | _ p =>
      rcases p with ⟨z, v⟩
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simp only [one_smul, familyTotalSpaceBase_mk,
        familyTranslationCover.eq_def]
      simp [movingToFixedCover, periodCoordinates, map_add]

/-- The zero vector over the explicit order-three radial strip lift lies in a fixed punctured
collar of radius two.  The large auxiliary radius is used only to obtain a global continuous
principal-gauge chart. -/
public noncomputable def sectionSevenAffineOrderThreeRadialZeroCollarPoint
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      orderThreePuncturedFamilyCollar A.periods 2) :=
  ⟨fun z ↦
      ⟨regularFamilyInclusion A.periods
          (regularFamilyZeroSection A.periods
            (A.sectionSevenAffineOrderThreeRadialBaseLift z)), by
        constructor
        · rw [orderThreeFamilyRadius.eq_def,
            familyTotalSpaceBase_regularFamilyInclusion]
          change 0 < ‖(orderThreeCayleyHomeomorph
            (A.sectionSevenAffineOrderThreeRadialBaseLift z).1 : ℂ)‖
          rw [norm_pos_iff]
          apply coe_ne_zero_of_ne_center
          intro hcenter
          have hbase :
              (A.sectionSevenAffineOrderThreeRadialBaseLift z).1 =
                A.modular.modularParameter.toTriangleUniformization.zOne := by
            apply orderThreeCayleyHomeomorph.injective
            refine hcenter.trans ?_
            rw [(ellipticFixedPoints_eq_of_fuchsian
              A.modular.modularParameter.toTriangleUniformization_sourceAction).1]
            apply Subtype.ext
            exact orderThreeCayley_fixedPoint.symm
          have hregular := (A.sectionSevenAffineOrderThreeRadialBaseLift z).2
          have hnot := (isRegularBasePoint_iff_not_mem_orbits
            (U := A.modular.modularParameter.toTriangleUniformization)
            (A.sectionSevenAffineOrderThreeRadialBaseLift z).1).mp hregular
          apply hnot
          left
          rw [sourceOrbitSet]
          simp only [Set.mem_iUnion, Set.mem_singleton_iff]
          refine ⟨1, ?_⟩
          simpa using hbase
        · rw [orderThreeFamilyRadius.eq_def,
            familyTotalSpaceBase_regularFamilyInclusion]
          exact (norm_orderThreeCayley_lt_one
            (A.sectionSevenAffineOrderThreeRadialBaseLift z).1).trans (by norm_num)⟩,
    (regularFamilyInclusion_continuous A.periods).comp
      ((regularFamilyZeroSection A.periods).continuous.comp
        A.sectionSevenAffineOrderThreeRadialBaseLift.continuous) |>.subtype_mk _⟩

/-- The explicit continuous strip gauge: undo the principal logarithmic gauge at the zero vector
over the radial strip lift, then read the fixed order-three real-period coordinate. -/
public noncomputable def sectionSevenAffineOrderThreeEndpointGauge
    (A : PaperAnalyticData) :
    C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :=
  let _ := A.totalSpaceCharts
  let e := orderThreePuncturedCollarGaugeHomeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph 2
  ⟨fun z ↦ (orderThreeRealPeriodProductHomeomorph A.periods
      (e.symm (A.sectionSevenAffineOrderThreeRadialZeroCollarPoint z)).1).2,
    continuous_snd.comp
      ((orderThreeRealPeriodProductHomeomorph A.periods).continuous.comp
        (continuous_subtype_val.comp
          (e.symm.continuous.comp
            A.sectionSevenAffineOrderThreeRadialZeroCollarPoint.continuous)))⟩

/-- Pointwise, the continuous strip gauge is the negative principal real-period gauge evaluated
at the explicit radial base lift. -/
public theorem sectionSevenAffineOrderThreeEndpointGauge_apply
    (A : PaperAnalyticData) (z : sectionSevenAffineVerticalStrip) :
    A.sectionSevenAffineOrderThreeEndpointGauge z =
      -A.orderThreePrincipalRealPeriodGauge
        (A.sectionSevenAffineOrderThreeRadialBaseLift z).1 := by
  let _ := A.totalSpaceCharts
  rw [sectionSevenAffineOrderThreeEndpointGauge]
  change (orderThreeRealPeriodProductHomeomorph A.periods
      ((orderThreePrincipalGaugeEquiv A.periods).symm
        (regularFamilyInclusion A.periods
          (regularFamilyZeroSection A.periods
            (A.sectionSevenAffineOrderThreeRadialBaseLift z))))).2 = _
  rw [A.orderThreeRealPeriodProductHomeomorph_principalGauge_symm_snd]
  simp only [regularFamilyZeroSection_apply, regularFamilyInclusion_mk,
    regularBundleInclusion]
  rw [orderThreeRealPeriodProductHomeomorph_mk]
  simp [movingToFixedCover, periodCoordinates]
  let p := (parameterMap A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne).1
  change -A.orderThreePrincipalRealPeriodGauge
      (A.sectionSevenAffineOrderThreeRadialBaseLift z).1 +
        (Quotient.mk _ (0 : ComplexTwoSpace) : AdditiveTorus p) =
    -A.orderThreePrincipalRealPeriodGauge
      (A.sectionSevenAffineOrderThreeRadialBaseLift z).1
  calc
    _ = -A.orderThreePrincipalRealPeriodGauge
          (A.sectionSevenAffineOrderThreeRadialBaseLift z).1 +
        (0 : AdditiveTorus p) := congrArg _ (additiveTorus_mk_zero p)
    _ = _ := add_zero _

/-- The remaining representative-level identity.  It compares the actual star-collar endpoint
with the explicit inverse-principal-gauge radial model after passing to the finite central cover.
All maps and the gauge in this statement have already been constructed. -/
public structure SectionSevenAffineOrderThreeEndpointRealPeriodIdentity
    (A : PaperAnalyticData) : Prop where
  eq_projection : ∀ (x : A.SectionSevenAffineMarkedBand)
      (q : (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius).carrier),
    A.orderThreeOverlapCollarHomeomorph
        (A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x) = Quotient.mk _ q →
      RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)
          ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
            (orderThreeRadialActionData A.periods)).symm
              (orderThreeRealPeriodProductHomeomorph A.periods q.1).2) =
        RadialEllipticActionData.centralFiberCoverProjection
          (orderThreeRadialActionData A.periods)
          (A.duplicatedSectionSevenBandToOrderThreeCoverSource
            (A.sectionSevenAffineOrderThreeEndpointGauge
                (A.sectionSevenAffineBandStripCoordinate x) +
              A.sectionSevenAffineBandFiberCoordinateOfLift
                A.sectionSevenAffineNamedStripLift x))

/-- The single representative-level identity gives exactly the order-three field of the pinned
lift endpoint-gauge formulas, for the named strip lift and the explicit continuous gauge. -/
public theorem sectionSevenAffineOrderThreeEndpointGaugeFormula
    (A : PaperAnalyticData)
    (H : A.SectionSevenAffineOrderThreeEndpointRealPeriodIdentity) :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint =
      A.sectionSevenAffineOrderThreeGaugeProjectionOfLift
        A.sectionSevenAffineNamedStripLift
        A.sectionSevenAffineOrderThreeEndpointGauge := by
  apply ContinuousMap.ext
  intro x
  let u := A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x
  change (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u)) = _
  generalize hq : A.orderThreeOverlapCollarHomeomorph u = y
  induction y using Quotient.inductionOn with
  | _ q =>
      rw [orderThreeSelectedFilling_toFun_starToFilling_mk]
      exact H.eq_projection x q hq

end SphereSixComplex.Geometry.PaperAnalyticData

end
