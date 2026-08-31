module

public import SphereSixComplex.Topology.PaperEllipticCollarInverseRepresentatives
public import SphereSixComplex.Topology.PaperActualEllipticWholeRelatorReduction
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderThreeEndpointGaugeFormulaProof
public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourEndpointGaugeFormulaProof

/-!
# Explicit regular-family lifts of the elliptic filling-relation loops
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

public noncomputable def orderThreeCollarInverseRepresentativeMap :
    C(OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace),
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius).carrier) where
  toFun := A.orderThreeCollarInverseRepresentative
  continuous_toFun := by
    let D := orderThreeCyclicPuncturedProductData A.periods
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
    let e := orderThreePuncturedProductEquivariantHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
    let hset := Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderThreeTorus A.starSeparation.orderThree.radius from rfl)
    let w : (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) →
        OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × A.orderThreeTorus) :=
      fun q => (q.1, q.2.1, Quotient.mk _ q.2.2)
    have hw : Continuous w := continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_quot_mk.comp (continuous_snd.comp continuous_snd)))
    change Continuous (fun q => e.toHomeomorph.symm
      (hset.symm (angularCover (T := A.orderThreeTorus) 3 D.radius_lt_one.le (w q))))
    exact e.toHomeomorph.symm.continuous.comp
      (hset.symm.continuous.comp
        ((continuous_angularCover (T := A.orderThreeTorus) 3 D.radius_lt_one.le).comp hw))

public noncomputable def orderFourCollarInverseRepresentativeMap :
    C(OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace),
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius).carrier) where
  toFun := A.orderFourCollarInverseRepresentative
  continuous_toFun := by
    let D := orderFourCyclicPuncturedProductData A.periods
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one
    let e := orderFourPuncturedProductEquivariantHomeomorph A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.starSeparation.orderFour.radius A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one
    let hset := Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.orderFourTorus A.starSeparation.orderFour.radius from rfl)
    let w : (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) →
        OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × A.orderFourTorus) :=
      fun q => (q.1, q.2.1, Quotient.mk _ q.2.2)
    have hw : Continuous w := continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_quot_mk.comp (continuous_snd.comp continuous_snd)))
    change Continuous (fun q => e.toHomeomorph.symm
      (hset.symm (angularCover (T := A.orderFourTorus) 4 D.radius_lt_one.le (w q))))
    exact e.toHomeomorph.symm.continuous.comp
      (hset.symm.continuous.comp
        ((continuous_angularCover (T := A.orderFourTorus) 4 D.radius_lt_one.le).comp hw))

public noncomputable def orderThreeCollarRegularRepresentativeMap :
    C(OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace),
      RegularTotalSpace A.periods) := by
  let _ := A.totalSpaceCharts
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact ⟨fun q => orderThreeCollarToRegular A.periods hproper
      A.starSeparation.orderThree.sourceData
      (orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius
        (A.orderThreeCollarInverseRepresentative q)),
    (orderThreeCollarToRegular_isOpenEmbedding A.periods hproper
      A.starSeparation.orderThree.sourceData).continuous.comp
      ((orderThreePuncturedCollarGaugeHomeomorph A.periods
        A.totalSpace_projection_isLocalDiffeomorph
        A.starSeparation.orderThree.radius).continuous.comp
          (A.orderThreeCollarInverseRepresentativeMap.continuous))⟩

public noncomputable def orderFourCollarRegularRepresentativeMap :
    C(OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace),
      RegularTotalSpace A.periods) := by
  let _ := A.totalSpaceCharts
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  exact ⟨fun q => orderFourCollarToRegular A.periods hproper
      A.starSeparation.orderFour.sourceData
      (orderFourPuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderFour.radius
        (A.orderFourCollarInverseRepresentative q)),
    (orderFourCollarToRegular_isOpenEmbedding A.periods hproper
      A.starSeparation.orderFour.sourceData).continuous.comp
      ((orderFourPuncturedCollarGaugeHomeomorph A.periods
        A.totalSpace_projection_isLocalDiffeomorph
        A.starSeparation.orderFour.radius).continuous.comp
          (A.orderFourCollarInverseRepresentativeMap.continuous))⟩

public theorem orderThreeCollarRegularRepresentativeMap_fullTurn
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    A.orderThreeCollarRegularRepresentativeMap (q.1, q.2.1 + 3, q.2.2) =
      A.orderThreeCollarRegularRepresentativeMap q := by
  unfold orderThreeCollarRegularRepresentativeMap
  exact congrArg
    (fun x => orderThreeCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderThree.sourceData
      (orderThreePuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderThree.radius x))
    (A.orderThreeCollarInverseRepresentative_fullTurn q)

public theorem orderFourCollarRegularRepresentativeMap_fullTurn
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    A.orderFourCollarRegularRepresentativeMap (q.1, q.2.1 + 4, q.2.2) =
      A.orderFourCollarRegularRepresentativeMap q := by
  unfold orderFourCollarRegularRepresentativeMap
  exact congrArg
    (fun x => orderFourCollarToRegular A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.starSeparation.orderFour.sourceData
      (orderFourPuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderFour.radius x))
    (A.orderFourCollarInverseRepresentative_fullTurn q)

public theorem orderThreeFillingRelation_regularRepresentative_endpoint
    : letI := A.orderThreeActualEllipticBoundaryAction
      A.orderThreeCollarRegularRepresentativeMap
          (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
            A.orderThreeActualEllipticBoundaryBase) =
        A.orderThreeCollarRegularRepresentativeMap
          A.orderThreeActualEllipticBoundaryBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rw [A.orderThreeActualFillingRelation_boundary_smul]
  exact A.orderThreeCollarRegularRepresentativeMap_fullTurn
    A.orderThreeActualEllipticBoundaryBase

public theorem orderFourFillingRelation_regularRepresentative_endpoint
    : letI := A.orderFourActualEllipticBoundaryAction
      A.orderFourCollarRegularRepresentativeMap
          (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
            A.orderFourActualEllipticBoundaryBase) =
        A.orderFourCollarRegularRepresentativeMap
          A.orderFourActualEllipticBoundaryBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  rw [A.orderFourActualFillingRelation_boundary_smul]
  exact A.orderFourCollarRegularRepresentativeMap_fullTurn
    A.orderFourActualEllipticBoundaryBase

public noncomputable def orderThreeFillingRelationRegularLoop :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path
      (A.orderThreeCollarRegularRepresentativeMap
        A.orderThreeActualEllipticBoundaryBase)
      (A.orderThreeCollarRegularRepresentativeMap
        A.orderThreeActualEllipticBoundaryBase) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact ((A.orderThreeActualEllipticBoundaryDeckStraightLift
    A.orderThreeActualEllipticBoundaryDeckData.fillingRelation).map
      A.orderThreeCollarRegularRepresentativeMap.continuous).cast rfl
        A.orderThreeFillingRelation_regularRepresentative_endpoint.symm

public noncomputable def orderFourFillingRelationRegularLoop :
    letI := A.orderFourActualEllipticBoundaryAction
    Path
      (A.orderFourCollarRegularRepresentativeMap
        A.orderFourActualEllipticBoundaryBase)
      (A.orderFourCollarRegularRepresentativeMap
        A.orderFourActualEllipticBoundaryBase) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact ((A.orderFourActualEllipticBoundaryDeckStraightLift
    A.orderFourActualEllipticBoundaryDeckData.fillingRelation).map
      A.orderFourCollarRegularRepresentativeMap.continuous).cast rfl
        A.orderFourFillingRelation_regularRepresentative_endpoint.symm

public theorem orderThreeCollarRegularRepresentative_base_projects :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.centralQuotientProjection
        (A.orderThreeCollarRegularRepresentativeMap
          A.orderThreeActualEllipticBoundaryBase) =
      A.orderThreeActualEllipticCentralBase := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  have h := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
    A.orderThreeActualEllipticBoundaryDeckData.fillingRelation 0
  simpa [orderThreeCollarRegularRepresentativeMap] using h.symm

public theorem orderFourCollarRegularRepresentative_base_projects :
    letI := A.orderFourActualEllipticBoundaryAction
    A.centralQuotientProjection
        (A.orderFourCollarRegularRepresentativeMap
          A.orderFourActualEllipticBoundaryBase) =
      A.orderFourActualEllipticCentralBase := by
  let _ := A.orderFourActualEllipticBoundaryAction
  have h := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
    A.orderFourActualEllipticBoundaryDeckData.fillingRelation 0
  simpa [orderFourCollarRegularRepresentativeMap] using h.symm

public theorem orderThreeFillingRelationRegularLoop_projects :
    letI := A.orderThreeActualEllipticBoundaryAction
    ((A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm) =
      A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
        A.orderThreeActualEllipticBoundaryDeckData.fillingRelation := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  apply Path.ext
  funext t
  change A.centralQuotientProjection
      (A.orderThreeCollarRegularRepresentativeMap
        (A.orderThreeActualEllipticBoundaryDeckStraightLift
          A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)) =
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t
  symm
  simpa [orderThreeCollarRegularRepresentativeMap,
    orderThreeActualEllipticBoundaryDeckStraightLift] using
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t

public theorem orderFourFillingRelationRegularLoop_projects :
    letI := A.orderFourActualEllipticBoundaryAction
    ((A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm) =
      A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
        A.orderFourActualEllipticBoundaryDeckData.fillingRelation := by
  let _ := A.orderFourActualEllipticBoundaryAction
  apply Path.ext
  funext t
  change A.centralQuotientProjection
      (A.orderFourCollarRegularRepresentativeMap
        (A.orderFourActualEllipticBoundaryDeckStraightLift
          A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)) =
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation t
  symm
  simpa [orderFourCollarRegularRepresentativeMap,
    orderFourActualEllipticBoundaryDeckStraightLift] using
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation t

public theorem orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection :
    letI := A.orderThreeActualEllipticBoundaryAction
    Path.Homotopic.Quotient.mk
        (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
          A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) =
      Path.Homotopic.Quotient.mk
        ((A.orderThreeFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderThreeCollarRegularRepresentative_base_projects.symm
            A.orderThreeCollarRegularRepresentative_base_projects.symm) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact congrArg Path.Homotopic.Quotient.mk
    A.orderThreeFillingRelationRegularLoop_projects.symm

public theorem orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection :
    letI := A.orderFourActualEllipticBoundaryAction
    Path.Homotopic.Quotient.mk
        (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
          A.orderFourActualEllipticBoundaryDeckData.fillingRelation) =
      Path.Homotopic.Quotient.mk
        ((A.orderFourFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderFourCollarRegularRepresentative_base_projects.symm
            A.orderFourCollarRegularRepresentative_base_projects.symm) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact congrArg Path.Homotopic.Quotient.mk
    A.orderFourFillingRelationRegularLoop_projects.symm

public theorem orderThreeActualCanonicalRelatorInCentral_eq_regularLoopProjection :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × ComplexTwoSpace)) :=
      A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeActualCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq
        A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
        (Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let g := Path.Homotopic.Quotient.mk
    (A.orderThreeActualEllipticBoundaryDeckStraightLoop
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)
  let f := A.orderThreeActualOverlapToCentral
  let hb := A.orderThreeActualEllipticCanonicalChosenCover_boundaryBase_eq
  let hover := A.orderThreeActualEllipticCentralBase_eq_overlapCentralBase
  rw [A.orderThreeActualCanonicalRelatorInCentral_eq_fillingRelationStraightLoop]
  change FundamentalGroup.mapOfEq f rfl
      (fundamentalGroupElementOfBaseEq hb g) = _
  have h₁ := mapOfEq_fundamentalGroupElementOfBaseEq hb f hover rfl g
  have h₂ := mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl f hover g
  have h₃ := congrArg (fundamentalGroupElementOfBaseEq hover)
    (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation)
  have h₄ := congrArg (fundamentalGroupElementOfBaseEq hover)
    A.orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection
  exact h₁.trans (h₂.trans (h₃.trans h₄))

public theorem orderFourActualCanonicalRelatorInCentral_eq_regularLoopProjection :
    letI := A.orderFourActualEllipticBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × ComplexTwoSpace)) :=
      A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourActualCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq
        A.orderFourActualEllipticCentralBase_eq_overlapCentralBase
        (Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.orderFourActualEllipticBoundaryCover_simplyConnected
  let g := Path.Homotopic.Quotient.mk
    (A.orderFourActualEllipticBoundaryDeckStraightLoop
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation)
  let f := A.orderFourActualOverlapToCentral
  let hb := A.orderFourActualEllipticCanonicalChosenCover_boundaryBase_eq
  let hover := A.orderFourActualEllipticCentralBase_eq_overlapCentralBase
  rw [A.orderFourActualCanonicalRelatorInCentral_eq_fillingRelationStraightLoop]
  change FundamentalGroup.mapOfEq f rfl
      (fundamentalGroupElementOfBaseEq hb g) = _
  have h₁ := mapOfEq_fundamentalGroupElementOfBaseEq hb f hover rfl g
  have h₂ := mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl f hover g
  have h₃ := congrArg (fundamentalGroupElementOfBaseEq hover)
    (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_class
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation)
  have h₄ := congrArg (fundamentalGroupElementOfBaseEq hover)
    A.orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection
  exact h₁.trans (h₂.trans (h₃.trans h₄))

public theorem orderThreeRealPeriodProductHomeomorph_inverseRepresentative_snd
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      (A.orderThreeCollarInverseRepresentative q).1).2 =
        Quotient.mk _ q.2.2 := by
  have h := congrArg (fun z => z.1.2)
    (A.orderThreePuncturedProductHomeomorph_inverseRepresentative q)
  exact h.trans (angularCover_snd 3
    A.starSeparation.orderThree.radius_lt_one.le
    (q.1, q.2.1, Quotient.mk _ q.2.2))

public theorem orderFourRealPeriodProductHomeomorph_inverseRepresentative_snd
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (A.orderFourCollarInverseRepresentative q).1).2 =
        Quotient.mk _ q.2.2 := by
  have h := congrArg (fun z => z.1.2)
    (A.orderFourPuncturedProductHomeomorph_inverseRepresentative q)
  exact h.trans (angularCover_snd 4
    A.starSeparation.orderFour.radius_lt_one.le
    (q.1, q.2.1, Quotient.mk _ q.2.2))

public theorem orderThreeCollarRegularRepresentativeMap_realPeriod_snd
    (q : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × ComplexTwoSpace)) :
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderThreeCollarRegularRepresentativeMap q))).2 =
      A.orderThreePrincipalRealPeriodGauge
          (familyTotalSpaceBase A.periods
            (A.orderThreeCollarInverseRepresentative q).1) +
        Quotient.mk _ q.2.2 := by
  rw [show regularFamilyInclusion A.periods
      (A.orderThreeCollarRegularRepresentativeMap q) =
        orderThreePrincipalGaugeEquiv A.periods
          (A.orderThreeCollarInverseRepresentative q).1 by
    exact A.regularFamilyInclusion_orderThreeCollarInverseRepresentative q]
  rw [A.orderThreeRealPeriodProductHomeomorph_principalGauge_snd]
  rw [A.orderThreeRealPeriodProductHomeomorph_inverseRepresentative_snd]

public theorem orderFourCollarRegularRepresentativeMap_realPeriod_snd
    (q : OpenRadialInterval A.starSeparation.orderFour.radius ×
      (ℝ × ComplexTwoSpace)) :
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderFourCollarRegularRepresentativeMap q))).2 =
      A.orderFourPrincipalRealPeriodGauge
          (familyTotalSpaceBase A.periods
            (A.orderFourCollarInverseRepresentative q).1) +
        Quotient.mk _ q.2.2 := by
  rw [show regularFamilyInclusion A.periods
      (A.orderFourCollarRegularRepresentativeMap q) =
        orderFourPrincipalGaugeEquiv A.periods
          (A.orderFourCollarInverseRepresentative q).1 by
    exact A.regularFamilyInclusion_orderFourCollarInverseRepresentative q]
  rw [A.orderFourRealPeriodProductHomeomorph_principalGauge_snd]
  rw [A.orderFourRealPeriodProductHomeomorph_inverseRepresentative_snd]

public theorem orderThreeFillingRelationStraightLift_vector
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    (A.orderThreeActualEllipticBoundaryDeckStraightLift
      A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t).2.2 =
        A.orderThreeActualEllipticBoundaryBase.2.2 := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  have h : A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
      A.orderThreeActualEllipticBoundaryBase.2 =
        (A.orderThreeActualEllipticBoundaryBase.2.1 + 3,
          A.orderThreeActualEllipticBoundaryBase.2.2) := by
    change (A.orderThreeActualEllipticBoundaryDeckData.fillingRelation •
      A.orderThreeActualEllipticBoundaryBase).2 = _
    rw [A.orderThreeActualFillingRelation_boundary_smul]
  simp [orderThreeActualEllipticBoundaryDeckStraightLift, h]

public theorem orderFourFillingRelationStraightLift_vector
    (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    (A.orderFourActualEllipticBoundaryDeckStraightLift
      A.orderFourActualEllipticBoundaryDeckData.fillingRelation t).2.2 =
        A.orderFourActualEllipticBoundaryBase.2.2 := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  have h : A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
      A.orderFourActualEllipticBoundaryBase.2 =
        (A.orderFourActualEllipticBoundaryBase.2.1 + 4,
          A.orderFourActualEllipticBoundaryBase.2.2) := by
    change (A.orderFourActualEllipticBoundaryDeckData.fillingRelation •
      A.orderFourActualEllipticBoundaryBase).2 = _
    rw [A.orderFourActualFillingRelation_boundary_smul]
  simp [orderFourActualEllipticBoundaryDeckStraightLift, h]

public theorem orderThreeFillingRelationRegularLoop_realPeriod_snd
    (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderThreeFillingRelationRegularLoop t))).2 =
      A.orderThreePrincipalRealPeriodGauge
          (familyTotalSpaceBase A.periods
            (A.orderThreeCollarInverseRepresentative
              (A.orderThreeActualEllipticBoundaryDeckStraightLift
                A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)).1) +
        Quotient.mk _ A.orderThreeActualEllipticBoundaryBase.2.2 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  change (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderThreeCollarRegularRepresentativeMap
          (A.orderThreeActualEllipticBoundaryDeckStraightLift
            A.orderThreeActualEllipticBoundaryDeckData.fillingRelation t)))).2 = _
  rw [A.orderThreeCollarRegularRepresentativeMap_realPeriod_snd]
  rw [A.orderThreeFillingRelationStraightLift_vector]

public theorem orderFourFillingRelationRegularLoop_realPeriod_snd
    (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderFourFillingRelationRegularLoop t))).2 =
      A.orderFourPrincipalRealPeriodGauge
          (familyTotalSpaceBase A.periods
            (A.orderFourCollarInverseRepresentative
              (A.orderFourActualEllipticBoundaryDeckStraightLift
                A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)).1) +
        Quotient.mk _ A.orderFourActualEllipticBoundaryBase.2.2 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  change (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderFourCollarRegularRepresentativeMap
          (A.orderFourActualEllipticBoundaryDeckStraightLift
            A.orderFourActualEllipticBoundaryDeckData.fillingRelation t)))).2 = _
  rw [A.orderFourCollarRegularRepresentativeMap_realPeriod_snd]
  rw [A.orderFourFillingRelationStraightLift_vector]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
