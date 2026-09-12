module

public import SphereSixComplex.Paper.Topology.PaperEllipticCollarInverseRepresentatives
public import SphereSixComplex.Paper.Topology.PaperActualEllipticWholeRelatorReduction
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOrderThreeEndpointGaugeFormulaProof
public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineOrderFourEndpointGaugeFormulaProof

/-!
# Explicit regular-family lifts of the elliptic filling-relation loops
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

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

variable (A : AnalyticData)

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
      puncturedProduct A.OrderThreeTorus A.starSeparation.orderThree.radius from rfl)
    let w : (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) →
        OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × A.OrderThreeTorus) :=
      fun q => (q.1, q.2.1, Quotient.mk _ q.2.2)
    have hw : Continuous w := continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_quot_mk.comp (continuous_snd.comp continuous_snd)))
    change Continuous (fun q => e.toHomeomorph.symm
      (hset.symm (angularCover (T := A.OrderThreeTorus) 3 D.radius_lt_one.le (w q))))
    exact e.toHomeomorph.symm.continuous.comp
      (hset.symm.continuous.comp
        ((continuous_angularCover (T := A.OrderThreeTorus) 3 D.radius_lt_one.le).comp hw))

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
      puncturedProduct A.OrderFourTorus A.starSeparation.orderFour.radius from rfl)
    let w : (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) →
        OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × A.OrderFourTorus) :=
      fun q => (q.1, q.2.1, Quotient.mk _ q.2.2)
    have hw : Continuous w := continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_quot_mk.comp (continuous_snd.comp continuous_snd)))
    change Continuous (fun q => e.toHomeomorph.symm
      (hset.symm (angularCover (T := A.OrderFourTorus) 4 D.radius_lt_one.le (w q))))
    exact e.toHomeomorph.symm.continuous.comp
      (hset.symm.continuous.comp
        ((continuous_angularCover (T := A.OrderFourTorus) 4 D.radius_lt_one.le).comp hw))

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
    : letI := A.ellipticThreeBoundaryAction
      A.orderThreeCollarRegularRepresentativeMap
          (A.ellipticThreeBoundaryDeckData.fillingRelation •
            A.ellipticThreeBoundaryBase) =
        A.orderThreeCollarRegularRepresentativeMap
          A.ellipticThreeBoundaryBase := by
  let _ := A.ellipticThreeBoundaryAction
  rw [A.ellipticThreeFillingRelation_boundary_smul]
  exact A.orderThreeCollarRegularRepresentativeMap_fullTurn
    A.ellipticThreeBoundaryBase

public theorem orderFourFillingRelation_regularRepresentative_endpoint
    : letI := A.ellipticFourBoundaryAction
      A.orderFourCollarRegularRepresentativeMap
          (A.ellipticFourBoundaryDeckData.fillingRelation •
            A.ellipticFourBoundaryBase) =
        A.orderFourCollarRegularRepresentativeMap
          A.ellipticFourBoundaryBase := by
  let _ := A.ellipticFourBoundaryAction
  rw [A.ellipticFourFillingRelation_boundary_smul]
  exact A.orderFourCollarRegularRepresentativeMap_fullTurn
    A.ellipticFourBoundaryBase

public noncomputable def orderThreeFillingRelationRegularLoop :
    letI := A.ellipticThreeBoundaryAction
    Path
      (A.orderThreeCollarRegularRepresentativeMap
        A.ellipticThreeBoundaryBase)
      (A.orderThreeCollarRegularRepresentativeMap
        A.ellipticThreeBoundaryBase) := by
  let _ := A.ellipticThreeBoundaryAction
  exact ((A.ellipticThreeBoundaryDeckStraightLift
    A.ellipticThreeBoundaryDeckData.fillingRelation).map
      A.orderThreeCollarRegularRepresentativeMap.continuous).cast rfl
        A.orderThreeFillingRelation_regularRepresentative_endpoint.symm

public noncomputable def orderFourFillingRelationRegularLoop :
    letI := A.ellipticFourBoundaryAction
    Path
      (A.orderFourCollarRegularRepresentativeMap
        A.ellipticFourBoundaryBase)
      (A.orderFourCollarRegularRepresentativeMap
        A.ellipticFourBoundaryBase) := by
  let _ := A.ellipticFourBoundaryAction
  exact ((A.ellipticFourBoundaryDeckStraightLift
    A.ellipticFourBoundaryDeckData.fillingRelation).map
      A.orderFourCollarRegularRepresentativeMap.continuous).cast rfl
        A.orderFourFillingRelation_regularRepresentative_endpoint.symm

public theorem orderThreeCollarRegularRepresentative_base_projects :
    letI := A.ellipticThreeBoundaryAction
    A.centralQuotientProjection
        (A.orderThreeCollarRegularRepresentativeMap
          A.ellipticThreeBoundaryBase) =
      A.ellipticThreeCentralBase := by
  let _ := A.ellipticThreeBoundaryAction
  have h := A.ellipticThreeBoundaryDeckStraightCentralLoop_apply_explicit
    A.ellipticThreeBoundaryDeckData.fillingRelation 0
  simpa [orderThreeCollarRegularRepresentativeMap] using h.symm

public theorem orderFourCollarRegularRepresentative_base_projects :
    letI := A.ellipticFourBoundaryAction
    A.centralQuotientProjection
        (A.orderFourCollarRegularRepresentativeMap
          A.ellipticFourBoundaryBase) =
      A.ellipticFourCentralBase := by
  let _ := A.ellipticFourBoundaryAction
  have h := A.ellipticFourBoundaryDeckStraightCentralLoop_apply_explicit
    A.ellipticFourBoundaryDeckData.fillingRelation 0
  simpa [orderFourCollarRegularRepresentativeMap] using h.symm

public theorem orderThreeFillingRelationRegularLoop_projects :
    letI := A.ellipticThreeBoundaryAction
    ((A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm) =
      A.ellipticThreeBoundaryDeckStraightCentralLoop
        A.ellipticThreeBoundaryDeckData.fillingRelation := by
  let _ := A.ellipticThreeBoundaryAction
  apply Path.ext
  funext t
  change A.centralQuotientProjection
      (A.orderThreeCollarRegularRepresentativeMap
        (A.ellipticThreeBoundaryDeckStraightLift
          A.ellipticThreeBoundaryDeckData.fillingRelation t)) =
    A.ellipticThreeBoundaryDeckStraightCentralLoop
      A.ellipticThreeBoundaryDeckData.fillingRelation t
  symm
  simpa [orderThreeCollarRegularRepresentativeMap,
    ellipticThreeBoundaryDeckStraightLift] using
    A.ellipticThreeBoundaryDeckStraightCentralLoop_apply_explicit
      A.ellipticThreeBoundaryDeckData.fillingRelation t

public theorem orderFourFillingRelationRegularLoop_projects :
    letI := A.ellipticFourBoundaryAction
    ((A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm) =
      A.ellipticFourBoundaryDeckStraightCentralLoop
        A.ellipticFourBoundaryDeckData.fillingRelation := by
  let _ := A.ellipticFourBoundaryAction
  apply Path.ext
  funext t
  change A.centralQuotientProjection
      (A.orderFourCollarRegularRepresentativeMap
        (A.ellipticFourBoundaryDeckStraightLift
          A.ellipticFourBoundaryDeckData.fillingRelation t)) =
    A.ellipticFourBoundaryDeckStraightCentralLoop
      A.ellipticFourBoundaryDeckData.fillingRelation t
  symm
  simpa [orderFourCollarRegularRepresentativeMap,
    ellipticFourBoundaryDeckStraightLift] using
    A.ellipticFourBoundaryDeckStraightCentralLoop_apply_explicit
      A.ellipticFourBoundaryDeckData.fillingRelation t

public theorem orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection :
    letI := A.ellipticThreeBoundaryAction
    Path.Homotopic.Quotient.mk
        (A.ellipticThreeBoundaryDeckStraightCentralLoop
          A.ellipticThreeBoundaryDeckData.fillingRelation) =
      Path.Homotopic.Quotient.mk
        ((A.orderThreeFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderThreeCollarRegularRepresentative_base_projects.symm
            A.orderThreeCollarRegularRepresentative_base_projects.symm) := by
  let _ := A.ellipticThreeBoundaryAction
  exact congrArg Path.Homotopic.Quotient.mk
    A.orderThreeFillingRelationRegularLoop_projects.symm

public theorem orderFourFillingRelationStraightCentralLoop_class_eq_regularLoopProjection :
    letI := A.ellipticFourBoundaryAction
    Path.Homotopic.Quotient.mk
        (A.ellipticFourBoundaryDeckStraightCentralLoop
          A.ellipticFourBoundaryDeckData.fillingRelation) =
      Path.Homotopic.Quotient.mk
        ((A.orderFourFillingRelationRegularLoop.map
          A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
            A.orderFourCollarRegularRepresentative_base_projects.symm
            A.orderFourCollarRegularRepresentative_base_projects.symm) := by
  let _ := A.ellipticFourBoundaryAction
  exact congrArg Path.Homotopic.Quotient.mk
    A.orderFourFillingRelationRegularLoop_projects.symm

public theorem ellipticThreeCanonicalRelatorInCentral_eq_regularLoopProjection :
    letI := A.ellipticThreeBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderThree.radius ×
          (ℝ × ComplexTwoSpace)) :=
      A.ellipticThreeBoundaryCover_simplyConnected
    A.ellipticThreeCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq
        A.ellipticThreeCentralBase_eq_overlapCentralBase
        (Path.Homotopic.Quotient.mk
          ((A.orderThreeFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderThreeCollarRegularRepresentative_base_projects.symm
              A.orderThreeCollarRegularRepresentative_base_projects.symm)) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.ellipticThreeBoundaryCover_simplyConnected
  let g := Path.Homotopic.Quotient.mk
    (A.ellipticThreeBoundaryDeckStraightLoop
      A.ellipticThreeBoundaryDeckData.fillingRelation)
  let f := A.ellipticThreeOverlapToCentral
  let hb := A.ellipticThreeCanonicalChosenCover_boundaryBase_eq
  let hover := A.ellipticThreeCentralBase_eq_overlapCentralBase
  rw [A.ellipticThreeCanonicalRelatorInCentral_eq_fillingRelationStraightLoop]
  change FundamentalGroup.mapOfEq f rfl
      (fundamentalGroupElementOfBaseEq hb g) = _
  have h₁ := mapOfEq_fundamentalGroupElementOfBaseEq hb f hover rfl g
  have h₂ := mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl f hover g
  have h₃ := congrArg (fundamentalGroupElementOfBaseEq hover)
    (A.ellipticThreeBoundaryDeckStraightCentralLoop_class
      A.ellipticThreeBoundaryDeckData.fillingRelation)
  have h₄ := congrArg (fundamentalGroupElementOfBaseEq hover)
    A.orderThreeFillingRelationStraightCentralLoop_class_eq_regularLoopProjection
  exact h₁.trans (h₂.trans (h₃.trans h₄))

public theorem ellipticFourCanonicalRelatorInCentral_eq_regularLoopProjection :
    letI := A.ellipticFourBoundaryAction
    letI : SimplyConnectedSpace
        (OpenRadialInterval A.starSeparation.orderFour.radius ×
          (ℝ × ComplexTwoSpace)) :=
      A.ellipticFourBoundaryCover_simplyConnected
    A.ellipticFourCanonicalRelatorInCentral =
      fundamentalGroupElementOfBaseEq
        A.ellipticFourCentralBase_eq_overlapCentralBase
        (Path.Homotopic.Quotient.mk
          ((A.orderFourFillingRelationRegularLoop.map
            A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
              A.orderFourCollarRegularRepresentative_base_projects.symm
              A.orderFourCollarRegularRepresentative_base_projects.symm)) := by
  let _ := A.ellipticFourBoundaryAction
  let _ : SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) :=
    A.ellipticFourBoundaryCover_simplyConnected
  let g := Path.Homotopic.Quotient.mk
    (A.ellipticFourBoundaryDeckStraightLoop
      A.ellipticFourBoundaryDeckData.fillingRelation)
  let f := A.ellipticFourOverlapToCentral
  let hb := A.ellipticFourCanonicalChosenCover_boundaryBase_eq
  let hover := A.ellipticFourCentralBase_eq_overlapCentralBase
  rw [A.ellipticFourCanonicalRelatorInCentral_eq_fillingRelationStraightLoop]
  change FundamentalGroup.mapOfEq f rfl
      (fundamentalGroupElementOfBaseEq hb g) = _
  have h₁ := mapOfEq_fundamentalGroupElementOfBaseEq hb f hover rfl g
  have h₂ := mapOfEq_eq_elementOfBaseEq_mapOfEq_rfl f hover g
  have h₃ := congrArg (fundamentalGroupElementOfBaseEq hover)
    (A.ellipticFourBoundaryDeckStraightCentralLoop_class
      A.ellipticFourBoundaryDeckData.fillingRelation)
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
    letI := A.ellipticThreeBoundaryAction
    (A.ellipticThreeBoundaryDeckStraightLift
      A.ellipticThreeBoundaryDeckData.fillingRelation t).2.2 =
        A.ellipticThreeBoundaryBase.2.2 := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  have h : A.ellipticThreeBoundaryDeckData.fillingRelation •
      A.ellipticThreeBoundaryBase.2 =
        (A.ellipticThreeBoundaryBase.2.1 + 3,
          A.ellipticThreeBoundaryBase.2.2) := by
    change (A.ellipticThreeBoundaryDeckData.fillingRelation •
      A.ellipticThreeBoundaryBase).2 = _
    rw [A.ellipticThreeFillingRelation_boundary_smul]
  simp [ellipticThreeBoundaryDeckStraightLift, h]

public theorem orderFourFillingRelationStraightLift_vector
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    (A.ellipticFourBoundaryDeckStraightLift
      A.ellipticFourBoundaryDeckData.fillingRelation t).2.2 =
        A.ellipticFourBoundaryBase.2.2 := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  have h : A.ellipticFourBoundaryDeckData.fillingRelation •
      A.ellipticFourBoundaryBase.2 =
        (A.ellipticFourBoundaryBase.2.1 + 4,
          A.ellipticFourBoundaryBase.2.2) := by
    change (A.ellipticFourBoundaryDeckData.fillingRelation •
      A.ellipticFourBoundaryBase).2 = _
    rw [A.ellipticFourFillingRelation_boundary_smul]
  simp [ellipticFourBoundaryDeckStraightLift, h]

public theorem orderThreeFillingRelationRegularLoop_realPeriod_snd
    (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderThreeFillingRelationRegularLoop t))).2 =
      A.orderThreePrincipalRealPeriodGauge
          (familyTotalSpaceBase A.periods
            (A.orderThreeCollarInverseRepresentative
              (A.ellipticThreeBoundaryDeckStraightLift
                A.ellipticThreeBoundaryDeckData.fillingRelation t)).1) +
        Quotient.mk _ A.ellipticThreeBoundaryBase.2.2 := by
  let _ := A.ellipticThreeBoundaryAction
  change (orderThreeRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderThreeCollarRegularRepresentativeMap
          (A.ellipticThreeBoundaryDeckStraightLift
            A.ellipticThreeBoundaryDeckData.fillingRelation t)))).2 = _
  rw [A.orderThreeCollarRegularRepresentativeMap_realPeriod_snd]
  rw [A.orderThreeFillingRelationStraightLift_vector]

public theorem orderFourFillingRelationRegularLoop_realPeriod_snd
    (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderFourFillingRelationRegularLoop t))).2 =
      A.orderFourPrincipalRealPeriodGauge
          (familyTotalSpaceBase A.periods
            (A.orderFourCollarInverseRepresentative
              (A.ellipticFourBoundaryDeckStraightLift
                A.ellipticFourBoundaryDeckData.fillingRelation t)).1) +
        Quotient.mk _ A.ellipticFourBoundaryBase.2.2 := by
  let _ := A.ellipticFourBoundaryAction
  change (orderFourRealPeriodProductHomeomorph A.periods
      (regularFamilyInclusion A.periods
        (A.orderFourCollarRegularRepresentativeMap
          (A.ellipticFourBoundaryDeckStraightLift
            A.ellipticFourBoundaryDeckData.fillingRelation t)))).2 = _
  rw [A.orderFourCollarRegularRepresentativeMap_realPeriod_snd]
  rw [A.orderFourFillingRelationStraightLift_vector]

end SphereSixComplex.Geometry.AnalyticData

end

end
