module

public import SphereSixComplex.Geometry.ComplexModelRechart
public import SphereSixComplex.Geometry.PaperAnalyticData
public import SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
public import SphereSixComplex.Geometry.EllipticAnalyticCollarDescent

/-!
# Elliptic filling pieces for the paper data
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticFamilySpecialization EllipticFixedPointCriterion
open EllipticLocalCoordinates EllipticCayleyHomeomorph
open EllipticWholeFiberCompactCover
open EllipticVaryingFamilyQuotient EllipticPuncturedCollarGaugeHomeomorph
open EllipticLinearCollarGlobalDescent EquivariantQuotientHomeomorph

noncomputable section

universe u

variable {G X : Type u} [Group G] [TopologicalSpace X]

public theorem restrictedOrbitRel_eq_mulActionOrbitRel
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    restrictedOrbitRel A S =
      letI := restrictedMulAction A S
      MulAction.orbitRel G S.carrier := by
  rfl

public theorem restrictedIsCancelSMul
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hfree : letI := A; IsCancelSMul G X) :
    letI := restrictedMulAction A S
    IsCancelSMul G S.carrier := by
  let _ := A
  let _ : IsCancelSMul G X := hfree
  let _ := restrictedMulAction A S
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hx
  apply IsCancelSMul.eq_one_of_smul (x := (x : X))
  exact congrArg Subtype.val hx

public theorem restrictedContinuousConstSMul
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hcontinuous : letI := A; ContinuousConstSMul G X) :
    letI := restrictedMulAction A S
    ContinuousConstSMul G S.carrier := by
  let _ := A
  let _ : ContinuousConstSMul G X := hcontinuous
  let _ := restrictedMulAction A S
  exact ⟨fun g => Continuous.subtype_mk
    ((continuous_const_smul g).comp continuous_subtype_val) _⟩

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

@[expose] public noncomputable def orderThreeFillingOpen (r : ℝ) :
    TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
  ⟨{q | orderThreeFamilyRadius A.periods q < r},
    isOpen_lt (orderThreeFamilyRadius_continuous A.periods) continuous_const⟩

@[expose] public noncomputable def orderFourFillingOpen (r : ℝ) :
    TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
  ⟨{q | orderFourFamilyRadius A.periods q < r},
    isOpen_lt (orderFourFamilyRadius_continuous A.periods) continuous_const⟩

@[expose] public noncomputable def orderThreeFillingCarrier (r : ℝ) :
    InvariantOpenCarrier (orderThreeAffineFamilyAction A.periods) where
  carrier := A.orderThreeFillingOpen r
  isOpen_carrier := (A.orderThreeFillingOpen r).2
  invariant g q hq := by
    change orderThreeFamilyRadius A.periods
      (orderThreeAffineFamilyRepresentation A.periods g q) < r
    rw [orderThreeFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact hq

@[expose] public noncomputable def orderFourFillingCarrier (r : ℝ) :
    InvariantOpenCarrier (orderFourAffineFamilyAction A.periods) where
  carrier := A.orderFourFillingOpen r
  isOpen_carrier := (A.orderFourFillingOpen r).2
  invariant g q hq := by
    change orderFourFamilyRadius A.periods
      (orderFourAffineFamilyRepresentation A.periods g q) < r
    rw [orderFourFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact hq

@[expose, instance_reducible]
public noncomputable def orderThreeFillingAction (r : ℝ) :
    MulAction (FiniteCyclic 3) (A.orderThreeFillingOpen r) where
  smul g q := ⟨orderThreeAffineFamilyRepresentation A.periods g q, by
    change orderThreeFamilyRadius A.periods
      (orderThreeAffineFamilyRepresentation A.periods g q) < r
    rw [orderThreeFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact q.property⟩
  one_smul q := by
    apply Subtype.ext
    change orderThreeAffineFamilyRepresentation A.periods 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    apply Subtype.ext
    change orderThreeAffineFamilyRepresentation A.periods (g * h) q =
      orderThreeAffineFamilyRepresentation A.periods g
        (orderThreeAffineFamilyRepresentation A.periods h q)
    rw [map_mul]
    rfl

@[expose, instance_reducible]
public noncomputable def orderFourFillingAction (r : ℝ) :
    MulAction (FiniteCyclic 4) (A.orderFourFillingOpen r) where
  smul g q := ⟨orderFourAffineFamilyRepresentation A.periods g q, by
    change orderFourFamilyRadius A.periods
      (orderFourAffineFamilyRepresentation A.periods g q) < r
    rw [orderFourFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact q.property⟩
  one_smul q := by
    apply Subtype.ext
    change orderFourAffineFamilyRepresentation A.periods 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    apply Subtype.ext
    change orderFourAffineFamilyRepresentation A.periods (g * h) q =
      orderFourAffineFamilyRepresentation A.periods g
        (orderFourAffineFamilyRepresentation A.periods h q)
    rw [map_mul]
    rfl

public abbrev OrderThreeVaryingFilling (r : ℝ) :=
  letI := A.orderThreeFillingAction r
  OrbitQuotient (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)

public abbrev OrderFourVaryingFilling (r : ℝ) :=
  letI := A.orderFourFillingAction r
  OrbitQuotient (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)

@[instance_reducible]
public noncomputable def totalSpaceCharts :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  infer_instance

public theorem totalSpace_isManifold :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) inferInstance A.totalSpaceCharts := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  exact (totalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods RegularSmoothnessOrder).1

public theorem totalSpace_projection_isLocalDiffeomorph :
    letI := A.totalSpaceCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (projection (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  exact (totalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods RegularSmoothnessOrder).2

@[instance_reducible]
public noncomputable def orderThreeFillingSourceCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderThreeFillingOpen r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderThreeFillingOpen r)
  infer_instance

@[instance_reducible]
public noncomputable def orderFourFillingSourceCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderFourFillingOpen r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderFourFillingOpen r)
  infer_instance

public theorem orderThreeFillingSource_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) inferInstance
      (A.orderThreeFillingSourceCharts r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderThreeFillingSourceCharts r
  change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (A.orderThreeFillingOpen r)
  infer_instance

public theorem orderFourFillingSource_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) inferInstance
      (A.orderFourFillingSourceCharts r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderFourFillingSourceCharts r
  change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (A.orderFourFillingOpen r)
  infer_instance

public theorem orderThreeFillingRestrictedAction_contMDiff (r : ℝ) (g : FiniteCyclic 3) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : A.orderThreeFillingOpen r => g • q) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  have hcharts : A.orderThreeFillingSourceCharts r =
      (A.orderThreeFillingOpen r).instChartedSpace := by
    rfl
  rw [hcharts]
  rw [← ContMDiff.subtypeVal_comp_iff (A.orderThreeFillingOpen r)]
  convert (orderThreeAffineFamilyRepresentation_contMDiff A.periods
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).2 g).comp
      (contMDiff_subtype_val (I := GlobalDeckTotalModel)) using 1
  funext q
  rfl

public theorem orderFourFillingRestrictedAction_contMDiff (r : ℝ) (g : FiniteCyclic 4) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : A.orderFourFillingOpen r => g • q) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  have hcharts : A.orderFourFillingSourceCharts r =
      (A.orderFourFillingOpen r).instChartedSpace := by
    rfl
  rw [hcharts]
  rw [← ContMDiff.subtypeVal_comp_iff (A.orderFourFillingOpen r)]
  convert (orderFourAffineFamilyRepresentation_contMDiff A.periods
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).2 g).comp
      (contMDiff_subtype_val (I := GlobalDeckTotalModel)) using 1
  funext q
  rfl

public theorem orderThreeFillingAction_free (r : ℝ) :
    letI := A.orderThreeFillingAction r
    IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) := by
  let _ := A.orderThreeFillingAction r
  let hfree := orderThreeAffineFamilyAction_free A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hq
  let _ := orderThreeAffineFamilyAction A.periods
  let _ : IsCancelSMul (FiniteCyclic 3) (TotalSpace (parameterMap A.periods)) := hfree
  apply IsCancelSMul.eq_one_of_smul (x := (q : TotalSpace (parameterMap A.periods)))
  exact congrArg Subtype.val hq

public theorem orderFourFillingAction_free (r : ℝ) :
    letI := A.orderFourFillingAction r
    IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) := by
  let _ := A.orderFourFillingAction r
  let hfree := orderFourAffineFamilyAction_free A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hq
  let _ := orderFourAffineFamilyAction A.periods
  let _ : IsCancelSMul (FiniteCyclic 4) (TotalSpace (parameterMap A.periods)) := hfree
  apply IsCancelSMul.eq_one_of_smul (x := (q : TotalSpace (parameterMap A.periods)))
  exact congrArg Subtype.val hq

public theorem orderThreeFillingAction_continuousConstSMul (r : ℝ) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  exact ⟨fun g => (A.orderThreeFillingRestrictedAction_contMDiff r g).continuous⟩

public theorem orderFourFillingAction_continuousConstSMul (r : ℝ) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  exact ⟨fun g => (A.orderFourFillingRestrictedAction_contMDiff r g).continuous⟩

public theorem totalSpace_t2 : T2Space (TotalSpace (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  infer_instance

@[instance_reducible]
public noncomputable def orderThreeFillingProductCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  infer_instance

@[instance_reducible]
public noncomputable def orderFourFillingProductCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  infer_instance

public theorem orderThreeFillingProduct_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderThreeVaryingFilling r) inferInstance (A.orderThreeFillingProductCharts r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let _ := A.orderThreeFillingProductCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingRestrictedAction_contMDiff r)).1

public theorem orderFourFillingProduct_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderFourVaryingFilling r) inferInstance (A.orderFourFillingProductCharts r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let _ := A.orderFourFillingProductCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingRestrictedAction_contMDiff r)).1

@[instance_reducible]
public noncomputable def orderThreeFillingComplexCharts (r : ℝ) :
    ChartedSpace ComplexModel (A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingProductCharts r
  exact globalDeckComplexCharts

@[instance_reducible]
public noncomputable def orderFourFillingComplexCharts (r : ℝ) :
    ChartedSpace ComplexModel (A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingProductCharts r
  exact globalDeckComplexCharts

public theorem orderThreeFilling_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (A.OrderThreeVaryingFilling r) inferInstance (A.orderThreeFillingComplexCharts r) := by
  let _ := A.orderThreeFillingProductCharts r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderThreeVaryingFilling r) := A.orderThreeFillingProduct_isManifold r
  exact globalDeckComplexManifold

public theorem orderFourFilling_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (A.OrderFourVaryingFilling r) inferInstance (A.orderFourFillingComplexCharts r) := by
  let _ := A.orderFourFillingProductCharts r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderFourVaryingFilling r) := A.orderFourFillingProduct_isManifold r
  exact globalDeckComplexManifold

public theorem totalSpace_secondCountable :
    SecondCountableTopology (TotalSpace (parameterMap A.periods)) := by
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  exact ContinuousConstSMul.secondCountableTopology

public theorem orderThreeFilling_secondCountable (r : ℝ) :
    SecondCountableTopology (A.OrderThreeVaryingFilling r) := by
  let _ : SecondCountableTopology (TotalSpace (parameterMap A.periods)) :=
    A.totalSpace_secondCountable
  let _ : SecondCountableTopology (A.orderThreeFillingOpen r) := by infer_instance
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  exact ContinuousConstSMul.secondCountableTopology

public theorem orderFourFilling_secondCountable (r : ℝ) :
    SecondCountableTopology (A.OrderFourVaryingFilling r) := by
  let _ : SecondCountableTopology (TotalSpace (parameterMap A.periods)) :=
    A.totalSpace_secondCountable
  let _ : SecondCountableTopology (A.orderFourFillingOpen r) := by infer_instance
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  exact ContinuousConstSMul.secondCountableTopology

public theorem orderThreePuncturedCarrier_subset_filling (r : ℝ) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier ⊆
      A.orderThreeFillingOpen r := by
  intro q hq
  exact hq.2

public theorem orderFourPuncturedCarrier_subset_filling (r : ℝ) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier ⊆
      A.orderFourFillingOpen r := by
  intro q hq
  exact hq.2

@[expose] public def orderThreePuncturedSourceToFillingSource (r : ℝ) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier →
      A.orderThreeFillingOpen r :=
  Set.inclusion (A.orderThreePuncturedCarrier_subset_filling r)

@[expose] public def orderFourPuncturedSourceToFillingSource (r : ℝ) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier →
      A.orderFourFillingOpen r :=
  Set.inclusion (A.orderFourPuncturedCarrier_subset_filling r)

public theorem orderThreePuncturedSourceToFillingSource_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderThreePuncturedSourceToFillingSource r) := by
  apply Topology.IsOpenEmbedding.inclusion
    (A.orderThreePuncturedCarrier_subset_filling r)
  exact (orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier.preimage
      continuous_subtype_val

public theorem orderFourPuncturedSourceToFillingSource_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderFourPuncturedSourceToFillingSource r) := by
  apply Topology.IsOpenEmbedding.inclusion
    (A.orderFourPuncturedCarrier_subset_filling r)
  exact (orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier.preimage
      continuous_subtype_val

@[expose] public noncomputable def orderThreePuncturedCollarToFilling (r : ℝ) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.OrderThreeVaryingFilling r := by
  let _ := A.orderThreeFillingAction r
  refine Quotient.map (A.orderThreePuncturedSourceToFillingSource r) ?_
  intro x y hxy
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  change MulAction.orbitRel (FiniteCyclic 3) _ x y at hxy
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  change MulAction.orbitRel (FiniteCyclic 3) _
    (A.orderThreePuncturedSourceToFillingSource r x)
    (A.orderThreePuncturedSourceToFillingSource r y)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, Subtype.ext ?_⟩
  change orderThreeAffineFamilyRepresentation A.periods g y = x
  exact congrArg Subtype.val hg

@[expose] public noncomputable def orderFourPuncturedCollarToFilling (r : ℝ) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.OrderFourVaryingFilling r := by
  let _ := A.orderFourFillingAction r
  refine Quotient.map (A.orderFourPuncturedSourceToFillingSource r) ?_
  intro x y hxy
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  change MulAction.orbitRel (FiniteCyclic 4) _ x y at hxy
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  change MulAction.orbitRel (FiniteCyclic 4) _
    (A.orderFourPuncturedSourceToFillingSource r x)
    (A.orderFourPuncturedSourceToFillingSource r y)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, Subtype.ext ?_⟩
  change orderFourAffineFamilyRepresentation A.periods g y = x
  exact congrArg Subtype.val hg

@[simp]
public theorem orderThreePuncturedCollarToFilling_mk (r : ℝ)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.orderThreePuncturedCollarToFilling r (Quotient.mk _ q) =
      Quotient.mk _ (A.orderThreePuncturedSourceToFillingSource r q) :=
  by
    rw [orderThreePuncturedCollarToFilling.eq_def]
    rfl

@[simp]
public theorem orderFourPuncturedCollarToFilling_mk (r : ℝ)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.orderFourPuncturedCollarToFilling r (Quotient.mk _ q) =
      Quotient.mk _ (A.orderFourPuncturedSourceToFillingSource r q) :=
  by
    rw [orderFourPuncturedCollarToFilling.eq_def]
    rfl

public theorem orderThreePuncturedCollarToFilling_continuous (r : ℝ) :
    Continuous (A.orderThreePuncturedCollarToFilling r) := by
  rw [orderThreePuncturedCollarToFilling.eq_def]
  exact continuous_quot_map _
    (orderThreePuncturedSourceToFillingSource_isOpenEmbedding (A := A) r).continuous

public theorem orderFourPuncturedCollarToFilling_continuous (r : ℝ) :
    Continuous (A.orderFourPuncturedCollarToFilling r) := by
  rw [orderFourPuncturedCollarToFilling.eq_def]
  exact continuous_quot_map _
    (orderFourPuncturedSourceToFillingSource_isOpenEmbedding (A := A) r).continuous

public theorem orderThreePuncturedCollarToFilling_injective (r : ℝ) :
    Function.Injective (A.orderThreePuncturedCollarToFilling r) := by
  let _ := A.orderThreeFillingAction r
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)
      change MulAction.orbitRel (FiniteCyclic 3) _ x y
      rw [A.orderThreePuncturedCollarToFilling_mk,
        A.orderThreePuncturedCollarToFilling_mk] at hxy
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
      obtain ⟨g, hg⟩ := hxy
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨g, Subtype.ext ?_⟩
      change orderThreeAffineFamilyRepresentation A.periods g y = x
      exact congrArg Subtype.val hg

public theorem orderFourPuncturedCollarToFilling_injective (r : ℝ) :
    Function.Injective (A.orderFourPuncturedCollarToFilling r) := by
  let _ := A.orderFourFillingAction r
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)
      change MulAction.orbitRel (FiniteCyclic 4) _ x y
      rw [A.orderFourPuncturedCollarToFilling_mk,
        A.orderFourPuncturedCollarToFilling_mk] at hxy
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
      obtain ⟨g, hg⟩ := hxy
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨g, Subtype.ext ?_⟩
      change orderFourAffineFamilyRepresentation A.periods g y = x
      exact congrArg Subtype.val hg

public theorem orderThreePuncturedCollarToFilling_isOpenMap (r : ℝ) :
    IsOpenMap (A.orderThreePuncturedCollarToFilling r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  intro U hU
  let pS := Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r))
  let pT := Quotient.mk (MulAction.orbitRel (FiniteCyclic 3)
    (A.orderThreeFillingOpen r))
  have hpre : IsOpen (pS ⁻¹' U) := continuous_quot_mk.isOpen_preimage U hU
  have hsource : IsOpen (A.orderThreePuncturedSourceToFillingSource r '' (pS ⁻¹' U)) :=
    (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).isOpenMap _ hpre
  have htarget : IsOpen (pT ''
      (A.orderThreePuncturedSourceToFillingSource r '' (pS ⁻¹' U))) :=
    isOpenMap_quotient_mk'_mul _ hsource
  convert htarget using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    obtain ⟨s, rfl⟩ := Quotient.mk_surjective x
    exact ⟨A.orderThreePuncturedSourceToFillingSource r s,
      ⟨s, hxU, rfl⟩, (A.orderThreePuncturedCollarToFilling_mk r s).symm⟩
  · rintro ⟨t, ⟨s, hsU, rfl⟩, rfl⟩
    exact ⟨Quotient.mk _ s, hsU, A.orderThreePuncturedCollarToFilling_mk r s⟩

public theorem orderFourPuncturedCollarToFilling_isOpenMap (r : ℝ) :
    IsOpenMap (A.orderFourPuncturedCollarToFilling r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  intro U hU
  let pS := Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r))
  let pT := Quotient.mk (MulAction.orbitRel (FiniteCyclic 4)
    (A.orderFourFillingOpen r))
  have hpre : IsOpen (pS ⁻¹' U) := continuous_quot_mk.isOpen_preimage U hU
  have hsource : IsOpen (A.orderFourPuncturedSourceToFillingSource r '' (pS ⁻¹' U)) :=
    (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).isOpenMap _ hpre
  have htarget : IsOpen (pT ''
      (A.orderFourPuncturedSourceToFillingSource r '' (pS ⁻¹' U))) :=
    isOpenMap_quotient_mk'_mul _ hsource
  convert htarget using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    obtain ⟨s, rfl⟩ := Quotient.mk_surjective x
    exact ⟨A.orderFourPuncturedSourceToFillingSource r s,
      ⟨s, hxU, rfl⟩, (A.orderFourPuncturedCollarToFilling_mk r s).symm⟩
  · rintro ⟨t, ⟨s, hsU, rfl⟩, rfl⟩
    exact ⟨Quotient.mk _ s, hsU, A.orderFourPuncturedCollarToFilling_mk r s⟩

public theorem orderThreePuncturedCollarToFilling_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderThreePuncturedCollarToFilling r) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (A.orderThreePuncturedCollarToFilling_continuous r)
    (A.orderThreePuncturedCollarToFilling_injective r)
    (A.orderThreePuncturedCollarToFilling_isOpenMap r)

public theorem orderFourPuncturedCollarToFilling_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderFourPuncturedCollarToFilling r) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (A.orderFourPuncturedCollarToFilling_continuous r)
    (A.orderFourPuncturedCollarToFilling_injective r)
    (A.orderFourPuncturedCollarToFilling_isOpenMap r)

@[expose] public noncomputable def orderThreePuncturedCollarToCentralFamily
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.CentralFamily := by
  let _ := A.totalSpaceCharts
  exact orderThreeAffineCollarToPuncturedGlobalFamily A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

@[expose] public noncomputable def orderFourPuncturedCollarToCentralFamily
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.CentralFamily := by
  let _ := A.totalSpaceCharts
  exact orderFourAffineCollarToPuncturedGlobalFamily A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

public theorem orderThreePuncturedCollarToCentralFamily_isOpenEmbedding
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsOpenEmbedding (A.orderThreePuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  exact orderThreeAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

public theorem orderFourPuncturedCollarToCentralFamily_isOpenEmbedding
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsOpenEmbedding (A.orderFourPuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  exact orderFourAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

public structure OrderThreeFillingPiece where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  sourceData : OrderThreeLinearCollarSourceData
    (U := A.modular.modularParameter.toTriangleUniformization) radius

public structure OrderFourFillingPiece where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  sourceData : OrderFourLinearCollarSourceData
    (U := A.modular.modularParameter.toTriangleUniformization) radius

public theorem orderThreeLinearCollarSourceData_mono {r' r : ℝ} (hrr : r' ≤ r)
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r' := by
  rw [OrderThreeLinearCollarSourceData.eq_def] at D ⊢
  constructor
  · intro z hz hzr
    exact D.1 z hz (hzr.trans_le hrr)
  · intro z x hzr hxr g hg
    exact D.2 z x (hzr.trans_le hrr) (hxr.trans_le hrr) g hg

public theorem orderFourLinearCollarSourceData_mono {r' r : ℝ} (hrr : r' ≤ r)
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r' := by
  rw [OrderFourLinearCollarSourceData.eq_def] at D ⊢
  constructor
  · intro z hz hzr
    exact D.1 z hz (hzr.trans_le hrr)
  · intro z x hzr hxr g hg
    exact D.2 z x (hzr.trans_le hrr) (hxr.trans_le hrr) g hg

public theorem exists_orderThreeFillingPiece : Nonempty A.OrderThreeFillingPiece := by
  obtain ⟨r, hr, hr1, D⟩ := exists_orderThreeLinearCollarSourceData
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact ⟨⟨r, hr, hr1, D⟩⟩

public theorem exists_orderFourFillingPiece : Nonempty A.OrderFourFillingPiece := by
  obtain ⟨r, hr, hr1, D⟩ := exists_orderFourLinearCollarSourceData
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact ⟨⟨r, hr, hr1, D⟩⟩

public theorem exists_orderThreeFillingPiece_below {R : ℝ} (hR : 0 < R) :
    ∃ P : A.OrderThreeFillingPiece, P.radius < R := by
  obtain ⟨P⟩ := A.exists_orderThreeFillingPiece
  let r := min P.radius (R / 2)
  have hr : 0 < r := lt_min P.radius_pos (half_pos hR)
  have hrr : r ≤ P.radius := min_le_left _ _
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  exact ⟨⟨r, hr, hrr.trans_lt P.radius_lt_one,
    A.orderThreeLinearCollarSourceData_mono hrr P.sourceData⟩, hrR⟩

public theorem exists_orderFourFillingPiece_below {R : ℝ} (hR : 0 < R) :
    ∃ P : A.OrderFourFillingPiece, P.radius < R := by
  obtain ⟨P⟩ := A.exists_orderFourFillingPiece
  let r := min P.radius (R / 2)
  have hr : 0 < r := lt_min P.radius_pos (half_pos hR)
  have hrr : r ≤ P.radius := min_le_left _ _
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  exact ⟨⟨r, hr, hrr.trans_lt P.radius_lt_one,
    A.orderFourLinearCollarSourceData_mono hrr P.sourceData⟩, hrR⟩

@[expose] public noncomputable def orderThreeFillingPiece : A.OrderThreeFillingPiece :=
  Classical.choice A.exists_orderThreeFillingPiece

@[expose] public noncomputable def orderFourFillingPiece : A.OrderFourFillingPiece :=
  Classical.choice A.exists_orderFourFillingPiece

public abbrev SelectedOrderThreeFilling :=
  A.OrderThreeVaryingFilling A.orderThreeFillingPiece.radius

public abbrev SelectedOrderFourFilling :=
  A.OrderFourVaryingFilling A.orderFourFillingPiece.radius

public abbrev ComplexDiscBall (r : ℝ) :=
  {w : ComplexUnitDisc // ‖(w : ℂ)‖ < r}

@[expose] public noncomputable def complexDiscBallHomeomorph
    {r : ℝ} (hr1 : r < 1) : ComplexDiscBall r ≃ₜ Metric.ball (0 : ℂ) r where
  toFun w := ⟨w.1.1, by
    simpa only [Metric.mem_ball, dist_zero_right] using w.2⟩
  invFun w :=
    let hw : ‖(w.1 : ℂ)‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using w.2
    ⟨⟨w.1, hw.trans hr1⟩, hw⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

public theorem complexDiscBall_connected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ConnectedSpace (ComplexDiscBall r) := by
  let _ : ConnectedSpace (Metric.ball (0 : ℂ) r) := by
    apply isConnected_iff_connectedSpace.mp
    exact ⟨Metric.nonempty_ball.mpr hr, (convex_ball (0 : ℂ) r).isPreconnected⟩
  exact (complexDiscBallHomeomorph hr1).symm.surjective.connectedSpace
    (complexDiscBallHomeomorph hr1).symm.continuous

@[expose] public noncomputable def orderThreeFillingCoverMap (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace → A.orderThreeFillingOpen r := fun p =>
  ⟨Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2), by
    rw [orderThreeFillingOpen]
    change orderThreeFamilyRadius A.periods
      (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)) < r
    rw [orderThreeFamilyRadius.eq_def,
      familyTotalSpaceBase_mk, orderThreeCayleyHomeomorph.apply_symm_apply]
    exact p.1.2⟩

@[expose] public noncomputable def orderFourFillingCoverMap (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace → A.orderFourFillingOpen r := fun p =>
  ⟨Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2), by
    rw [orderFourFillingOpen]
    change orderFourFamilyRadius A.periods
      (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2)) < r
    rw [orderFourFamilyRadius.eq_def,
      familyTotalSpaceBase_mk, orderFourCayleyHomeomorph.apply_symm_apply]
    exact p.1.2⟩

public theorem orderThreeFillingCoverMap_continuous (r : ℝ) :
    Continuous (A.orderThreeFillingCoverMap r) := by
  unfold orderThreeFillingCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscBall r × ComplexTwoSpace => (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderThreeCayleyHomeomorph.symm.continuous.comp
      hfst).prodMk continuous_snd)

public theorem orderFourFillingCoverMap_continuous (r : ℝ) :
    Continuous (A.orderFourFillingCoverMap r) := by
  unfold orderFourFillingCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscBall r × ComplexTwoSpace => (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderFourCayleyHomeomorph.symm.continuous.comp
      hfst).prodMk continuous_snd)

public theorem orderThreeFillingCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderThreeFillingCoverMap r) := by
  rintro ⟨q, hq⟩
  change orderThreeFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderThreeCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderThreeFillingCoverMap.eq_def]
      change Quotient.mk _
        (orderThreeCayleyHomeomorph.symm (orderThreeCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderThreeCayleyHomeomorph.symm_apply_apply]

public theorem orderFourFillingCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderFourFillingCoverMap r) := by
  rintro ⟨q, hq⟩
  change orderFourFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderFourCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderFourFillingCoverMap.eq_def]
      change Quotient.mk _
        (orderFourCayleyHomeomorph.symm (orderFourCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderFourCayleyHomeomorph.symm_apply_apply]

public theorem orderThreeFilling_connected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ConnectedSpace (A.OrderThreeVaryingFilling r) := by
  let _ : ConnectedSpace (ComplexDiscBall r) := complexDiscBall_connected hr hr1
  let _ : ConnectedSpace (A.orderThreeFillingOpen r) :=
    (A.orderThreeFillingCoverMap_surjective r).connectedSpace
      (orderThreeFillingCoverMap_continuous (A := A) r)
  let _ := A.orderThreeFillingAction r
  infer_instance

public theorem orderFourFilling_connected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ConnectedSpace (A.OrderFourVaryingFilling r) := by
  let _ : ConnectedSpace (ComplexDiscBall r) := complexDiscBall_connected hr hr1
  let _ : ConnectedSpace (A.orderFourFillingOpen r) :=
    (A.orderFourFillingCoverMap_surjective r).connectedSpace
      (orderFourFillingCoverMap_continuous (A := A) r)
  let _ := A.orderFourFillingAction r
  infer_instance

public abbrev SelectedOrderThreePuncturedCollar :=
  Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.orderThreeFillingPiece.radius))

public abbrev SelectedOrderFourPuncturedCollar :=
  Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.orderFourFillingPiece.radius))

@[instance_reducible]
public noncomputable def selectedOrderThreeFillingComplexCharts :
    ChartedSpace ComplexModel A.SelectedOrderThreeFilling :=
  A.orderThreeFillingComplexCharts A.orderThreeFillingPiece.radius

@[instance_reducible]
public noncomputable def selectedOrderFourFillingComplexCharts :
    ChartedSpace ComplexModel A.SelectedOrderFourFilling :=
  A.orderFourFillingComplexCharts A.orderFourFillingPiece.radius

public noncomputable instance selectedOrderThreeFillingManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      A.SelectedOrderThreeFilling inferInstance
      A.selectedOrderThreeFillingComplexCharts :=
  A.orderThreeFilling_isManifold A.orderThreeFillingPiece.radius

public noncomputable instance selectedOrderFourFillingManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      A.SelectedOrderFourFilling inferInstance
      A.selectedOrderFourFillingComplexCharts :=
  A.orderFourFilling_isManifold A.orderFourFillingPiece.radius

public noncomputable instance selectedOrderThreeFillingConnected :
    ConnectedSpace A.SelectedOrderThreeFilling :=
  A.orderThreeFilling_connected A.orderThreeFillingPiece.radius_pos
    A.orderThreeFillingPiece.radius_lt_one

public noncomputable instance selectedOrderFourFillingConnected :
    ConnectedSpace A.SelectedOrderFourFilling :=
  A.orderFourFilling_connected A.orderFourFillingPiece.radius_pos
    A.orderFourFillingPiece.radius_lt_one

public noncomputable instance selectedOrderThreeFillingSecondCountable :
    SecondCountableTopology A.SelectedOrderThreeFilling :=
  A.orderThreeFilling_secondCountable A.orderThreeFillingPiece.radius

public noncomputable instance selectedOrderFourFillingSecondCountable :
    SecondCountableTopology A.SelectedOrderFourFilling :=
  A.orderFourFilling_secondCountable A.orderFourFillingPiece.radius

@[expose] public noncomputable def selectedOrderThreePuncturedCollarToFilling :
    A.SelectedOrderThreePuncturedCollar → A.SelectedOrderThreeFilling :=
  A.orderThreePuncturedCollarToFilling A.orderThreeFillingPiece.radius

@[expose] public noncomputable def selectedOrderFourPuncturedCollarToFilling :
    A.SelectedOrderFourPuncturedCollar → A.SelectedOrderFourFilling :=
  A.orderFourPuncturedCollarToFilling A.orderFourFillingPiece.radius

public theorem selectedOrderThreePuncturedCollarToFilling_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderThreePuncturedCollarToFilling :=
  A.orderThreePuncturedCollarToFilling_isOpenEmbedding
    A.orderThreeFillingPiece.radius

public theorem selectedOrderFourPuncturedCollarToFilling_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderFourPuncturedCollarToFilling :=
  A.orderFourPuncturedCollarToFilling_isOpenEmbedding
    A.orderFourFillingPiece.radius

@[expose] public noncomputable def selectedOrderThreePuncturedCollarToCentralFamily :
    A.SelectedOrderThreePuncturedCollar → A.CentralFamily :=
  A.orderThreePuncturedCollarToCentralFamily A.orderThreeFillingPiece.sourceData

@[expose] public noncomputable def selectedOrderFourPuncturedCollarToCentralFamily :
    A.SelectedOrderFourPuncturedCollar → A.CentralFamily :=
  A.orderFourPuncturedCollarToCentralFamily A.orderFourFillingPiece.sourceData

public theorem selectedOrderThreePuncturedCollarToCentralFamily_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderThreePuncturedCollarToCentralFamily :=
  A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding
    A.orderThreeFillingPiece.sourceData

public theorem selectedOrderFourPuncturedCollarToCentralFamily_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderFourPuncturedCollarToCentralFamily :=
  A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding
    A.orderFourFillingPiece.sourceData

end PaperAnalyticData

end

end SphereSixComplex.Geometry
