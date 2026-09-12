module

public import SphereSixComplex.Paper.Geometry.PaperAnalyticFillingPieces
public import SphereSixComplex.Paper.Geometry.PaperCentralFamilyTopology
public import SphereSixComplex.Prerequisites.Geometry.LocalDiffeomorphOperations
import all SphereSixComplex.Prerequisites.Geometry.LocalDiffeomorphOperations
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import all SphereSixComplex.Paper.Geometry.PaperAnalyticFillingPieces
import all SphereSixComplex.Paper.Geometry.RegularBaseTopology
import all SphereSixComplex.Paper.Geometry.RegularTorusFamily

/-!
# Analytic elliptic filling collars
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open Set Topology

noncomputable section

universe u v w

@[expose] public section

open ComplexTorus GlobalTorusFamily

private theorem isLocalDiffeomorph_globalDeckComplex
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) N]
    [IsManifold globalDeckTotalModel ∞ M]
    [IsManifold globalDeckTotalModel ∞ N]
    {f : M → N}
    (h : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞ f) :
    letI := globalDeckComplexCharts (M := M)
    letI := globalDeckComplexCharts (M := N)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f := by
  let cMProduct : ChartedSpace (ℂ × ComplexTwoSpace) M := globalDeckProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) M := cMProduct
  let mM : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ M := by
    simpa only [globalDeckTotalModel, globalDeckBaseModel, globalDeckFiberModel,
      modelWithCornersSelf_prod] using
      (inferInstance : IsManifold globalDeckTotalModel ∞ M)
  let _ : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ M := mM
  let cNProduct : ChartedSpace (ℂ × ComplexTwoSpace) N := globalDeckProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) N := cNProduct
  let mN : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ N := by
    simpa only [globalDeckTotalModel, globalDeckBaseModel, globalDeckFiberModel,
      modelWithCornersSelf_prod] using
      (inferInstance : IsManifold globalDeckTotalModel ∞ N)
  let _ : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ N := mN
  let dM := linearRechartDiffeomorph (n := ∞) (M := M) globalDeckComplexModelEquiv
  let dN := linearRechartDiffeomorph (n := ∞) (M := N) globalDeckComplexModelEquiv
  let _ : ChartedSpace ComplexModel M := globalDeckComplexCharts
  let _ : ChartedSpace ComplexModel N := globalDeckComplexCharts
  intro x
  have hx : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ id x :=
    dM.symm.isLocalDiffeomorph x
  have hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace))
      (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ f x := by
    simpa only [globalDeckTotalModel, globalDeckBaseModel, globalDeckFiberModel,
      modelWithCornersSelf_prod] using h x
  have hxf := IsLocalDiffeomorphAt.comp
    (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) N hx hf
  have hy : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace))
      (modelWithCornersSelf ℂ ComplexModel) ∞ id (f x) :=
    dN.isLocalDiffeomorph (f x)
  have hresult := IsLocalDiffeomorphAt.comp
    (modelWithCornersSelf ℂ ComplexModel) N hxf hy
  simpa only [Function.comp_id, Function.id_comp] using hresult

open SphereSixComplex Periods TriangleGroup
open ComplexTorus TorusFamily GlobalTorusFamily AnalyticTorusFamily
open EllipticVaryingFamilyQuotient EllipticAnalyticCollarDescent
open EllipticPuncturedCollarGaugeHomeomorph EquivariantQuotientHomeomorph
open EllipticLinearCollarGlobalDescent
open EllipticLocalCoordinates EllipticCayleyHomeomorph
open EllipticWholeFiberCompactCover
open TriangleGroup.FuchsianArithmeticTermination

namespace AnalyticData

variable (A : AnalyticData)

public abbrev OrderThreeAffinePuncturedQuotient (r : ℝ) :=
  Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r))

public abbrev OrderFourAffinePuncturedQuotient (r : ℝ) :=
  Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r))

public theorem orderThreeAffinePuncturedAction_contMDiff (r : ℝ)
    (g : FiniteCyclic 3) :
    letI := A.totalSpaceCharts
    ContMDiff globalDeckTotalModel globalDeckTotalModel ∞
      (fun q : (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier =>
          restrictedActionMap (orderThreeAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r) g q) := by
  let _ := A.totalSpaceCharts
  let _ : IsManifold globalDeckTotalModel ∞
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let S : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨(orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier⟩
  have hcharts : orderThreeAffinePuncturedCarrierCharts A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r =
        S.instChartedSpace := rfl
  rw [hcharts]
  apply (ContMDiff.subtypeVal_comp_iff S _).mp
  change ContMDiff globalDeckTotalModel globalDeckTotalModel ∞
    (fun q : S => orderThreeAffineFamilyRepresentation A.periods g q)
  exact (orderThreeAffineFamilyRepresentation_contMDiff A.periods
    A.totalSpace_projection_isLocalDiffeomorph g).comp
      (contMDiff_subtype_val (I := globalDeckTotalModel))

@[instance_reducible]
public noncomputable def orderThreeAffinePuncturedQuotientCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (A.OrderThreeAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsManifold globalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold globalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold globalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space S.carrier := by
    let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
    infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) S.carrier :=
    restrictedIsCancelSMul (orderThreeAffineFamilyAction A.periods) S
      (orderThreeAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 3) S.carrier :=
    ⟨fun g => (A.orderThreeAffinePuncturedAction_contMDiff r g).continuous⟩
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace)
    (OrbitQuotient (M := S.carrier) (G := FiniteCyclic 3))
  infer_instance

public theorem orderThreeAffinePuncturedQuotient_isManifold (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    IsManifold globalDeckTotalModel ∞ (A.OrderThreeAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsManifold globalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold globalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold globalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space S.carrier := by
    let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
    infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) S.carrier :=
    restrictedIsCancelSMul (orderThreeAffineFamilyAction A.periods) S
      (orderThreeAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 3) S.carrier :=
    ⟨fun g => (A.orderThreeAffinePuncturedAction_contMDiff r g).continuous⟩
  let _ := A.orderThreeAffinePuncturedQuotientCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    globalDeckTotalModel ∞ (A.orderThreeAffinePuncturedAction_contMDiff r)).1

private theorem orderThreeAffinePuncturedProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.totalSpaceCharts
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsManifold globalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold globalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold globalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space S.carrier := by
    let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
    infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) S.carrier :=
    restrictedIsCancelSMul (orderThreeAffineFamilyAction A.periods) S
      (orderThreeAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 3) S.carrier :=
    ⟨fun g => (A.orderThreeAffinePuncturedAction_contMDiff r g).continuous⟩
  let _ := A.orderThreeAffinePuncturedQuotientCharts r
  change IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
    (quotientProjection (M := S.carrier) (G := FiniteCyclic 3))
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    globalDeckTotalModel ∞ (A.orderThreeAffinePuncturedAction_contMDiff r)).2

private theorem orderThreeFillingProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    letI := A.orderThreeFillingProductCharts r
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (quotientProjection (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold globalDeckTotalModel ∞ (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let _ := A.orderThreeFillingProductCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    globalDeckTotalModel ∞ (A.orderThreeFillingRestrictedAction_contMDiff r)).2

public theorem orderThreePuncturedCollarToFilling_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    letI := A.orderThreeFillingProductCharts r
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (A.orderThreePuncturedCollarToFilling r) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts r
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ := A.orderThreeFillingProductCharts r
  apply isLocalDiffeomorph_of_comp_surjective
    (A.orderThreeAffinePuncturedProjection_isLocalDiffeomorph r)
    Quotient.mk_surjective
  let U : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨(orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier⟩
  let V := A.orderThreeFillingOpen r
  have hUV : U ≤ V := A.orderThreePuncturedCarrier_subset_filling r
  let hinc := opensInclusion_isLocalDiffeomorph (I := globalDeckTotalModel)
    hUV
  have hcomp : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      ((quotientProjection (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)) ∘
        A.orderThreePuncturedSourceToFillingSource r) := by
    intro q
    exact (hinc q).comp globalDeckTotalModel (A.OrderThreeVaryingFilling r)
      (A.orderThreeFillingProjection_isLocalDiffeomorph r
        (TopologicalSpace.Opens.inclusion hUV q))
  convert hcomp using 1
  funext q
  exact A.orderThreePuncturedCollarToFilling_mk r q

public theorem orderFourAffinePuncturedAction_contMDiff (r : ℝ)
    (g : FiniteCyclic 4) :
    letI := A.totalSpaceCharts
    ContMDiff globalDeckTotalModel globalDeckTotalModel ∞
      (fun q : (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier =>
          restrictedActionMap (orderFourAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r) g q) := by
  let _ := A.totalSpaceCharts
  let _ : IsManifold globalDeckTotalModel ∞
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let S : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨(orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier⟩
  have hcharts : orderFourAffinePuncturedCarrierCharts A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r =
        S.instChartedSpace := rfl
  rw [hcharts]
  apply (ContMDiff.subtypeVal_comp_iff S _).mp
  change ContMDiff globalDeckTotalModel globalDeckTotalModel ∞
    (fun q : S => orderFourAffineFamilyRepresentation A.periods g q)
  exact (orderFourAffineFamilyRepresentation_contMDiff A.periods
    A.totalSpace_projection_isLocalDiffeomorph g).comp
      (contMDiff_subtype_val (I := globalDeckTotalModel))

@[instance_reducible]
public noncomputable def orderFourAffinePuncturedQuotientCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (A.OrderFourAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsManifold globalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold globalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold globalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space S.carrier := by
    let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
    infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) S.carrier :=
    restrictedIsCancelSMul (orderFourAffineFamilyAction A.periods) S
      (orderFourAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 4) S.carrier :=
    ⟨fun g => (A.orderFourAffinePuncturedAction_contMDiff r g).continuous⟩
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace)
    (OrbitQuotient (M := S.carrier) (G := FiniteCyclic 4))
  infer_instance

public theorem orderFourAffinePuncturedQuotient_isManifold (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts r
    IsManifold globalDeckTotalModel ∞ (A.OrderFourAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsManifold globalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold globalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold globalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space S.carrier := by
    let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
    infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) S.carrier :=
    restrictedIsCancelSMul (orderFourAffineFamilyAction A.periods) S
      (orderFourAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 4) S.carrier :=
    ⟨fun g => (A.orderFourAffinePuncturedAction_contMDiff r g).continuous⟩
  let _ := A.orderFourAffinePuncturedQuotientCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    globalDeckTotalModel ∞ (A.orderFourAffinePuncturedAction_contMDiff r)).1

private theorem orderFourAffinePuncturedProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts r
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.totalSpaceCharts
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsManifold globalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold globalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold globalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space S.carrier := by
    let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
    infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) S.carrier :=
    restrictedIsCancelSMul (orderFourAffineFamilyAction A.periods) S
      (orderFourAffineFamilyAction_free A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let _ : ContinuousConstSMul (FiniteCyclic 4) S.carrier :=
    ⟨fun g => (A.orderFourAffinePuncturedAction_contMDiff r g).continuous⟩
  let _ := A.orderFourAffinePuncturedQuotientCharts r
  change IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
    (quotientProjection (M := S.carrier) (G := FiniteCyclic 4))
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    globalDeckTotalModel ∞ (A.orderFourAffinePuncturedAction_contMDiff r)).2

private theorem orderFourFillingProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    letI := A.orderFourFillingProductCharts r
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (quotientProjection (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold globalDeckTotalModel ∞ (A.orderFourFillingOpen r) :=
    A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let _ := A.orderFourFillingProductCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    globalDeckTotalModel ∞ (A.orderFourFillingRestrictedAction_contMDiff r)).2

public theorem orderFourPuncturedCollarToFilling_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts r
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    letI := A.orderFourFillingProductCharts r
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (A.orderFourPuncturedCollarToFilling r) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts r
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ := A.orderFourFillingProductCharts r
  apply isLocalDiffeomorph_of_comp_surjective
    (A.orderFourAffinePuncturedProjection_isLocalDiffeomorph r)
    Quotient.mk_surjective
  let U : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨(orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier⟩
  let V := A.orderFourFillingOpen r
  have hUV : U ≤ V := A.orderFourPuncturedCarrier_subset_filling r
  let hinc := opensInclusion_isLocalDiffeomorph (I := globalDeckTotalModel) hUV
  have hcomp : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      ((quotientProjection (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)) ∘
        A.orderFourPuncturedSourceToFillingSource r) := by
    intro q
    exact (hinc q).comp globalDeckTotalModel (A.OrderFourVaryingFilling r)
      (A.orderFourFillingProjection_isLocalDiffeomorph r
        (TopologicalSpace.Opens.inclusion hUV q))
  convert hcomp using 1
  funext q
  exact A.orderFourPuncturedCollarToFilling_mk r q

@[instance_reducible]
public noncomputable def regularTotalSpaceProductCharts :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace A.periods) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold globalDeckBaseModel ∞
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a ∞).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  infer_instance

private theorem regularBundleInclusion_isLocalDiffeomorph :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    letI : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
        (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) := prodChartedSpace ℂ _ ComplexTwoSpace _
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (regularBundleInclusion
        (U := A.modular.modularParameter.toTriangleUniformization)) := by
  dsimp only
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace) := prodChartedSpace ℂ _ ComplexTwoSpace _
  have hbase : IsLocalDiffeomorph globalDeckBaseModel globalDeckBaseModel ∞
      (fun z : RegularBase
        (U := A.modular.modularParameter.toTriangleUniformization) => z.1) := by
    change IsLocalDiffeomorph globalDeckBaseModel globalDeckBaseModel ∞
      (Subtype.val : regularBaseOpen hproper → UpperHalfPlane)
    exact openSubtypeVal_isLocalDiffeomorph
      (I := globalDeckBaseModel) (regularBaseOpen hproper)
  have hfiber := (Diffeomorph.refl globalDeckFiberModel ComplexTwoSpace ∞).isLocalDiffeomorph
  change IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
    (Prod.map (fun z : RegularBase
      (U := A.modular.modularParameter.toTriangleUniformization) => z.1) id)
  exact isLocalDiffeomorph_prodMap hbase hfiber

private theorem regularTotalSpaceProjection_isLocalDiffeomorph :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    letI : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
        (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) := prodChartedSpace ℂ _ ComplexTwoSpace _
    letI := A.regularTotalSpaceProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (projection (regularParameterMap A.periods)) := by
  dsimp only
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace) := prodChartedSpace ℂ _ ComplexTwoSpace _
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold globalDeckBaseModel ∞
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a ∞).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let _ := A.regularTotalSpaceProductCharts
  exact (regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper ∞).2

public theorem regularFamilyInclusion_isLocalDiffeomorph :
    letI := A.totalSpaceCharts
    letI := A.regularTotalSpaceProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (regularFamilyInclusion A.periods) := by
  let _ := A.totalSpaceCharts
  let _ := A.regularTotalSpaceProductCharts
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace) := prodChartedSpace ℂ _ ComplexTwoSpace _
  apply isLocalDiffeomorph_of_comp_surjective
    (regularTotalSpaceProjection_isLocalDiffeomorph (A := A)) Quotient.mk_surjective
  have hcomp : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      ((projection (parameterMap A.periods)) ∘
        regularBundleInclusion
          (U := A.modular.modularParameter.toTriangleUniformization)) := by
    intro q
    exact (regularBundleInclusion_isLocalDiffeomorph (A := A) q).comp globalDeckTotalModel
      (TotalSpace (parameterMap A.periods))
      (A.totalSpace_projection_isLocalDiffeomorph
        (regularBundleInclusion q))
  convert hcomp using 1
  funext q
  exact regularFamilyInclusion_mk A.periods q

private theorem orderThreeCollarToRegular_isLocalDiffeomorph {r : ℝ}
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.totalSpaceCharts
    letI := A.regularTotalSpaceProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (orderThreeCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction) D) := by
  let _ := A.totalSpaceCharts
  let _ := A.regularTotalSpaceProductCharts
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨orderThreePuncturedFamilyCollar A.periods r,
      orderThreePuncturedFamilyCollar_isOpen A.periods r⟩
  have hcharts : orderThreePuncturedCollarCharts A.periods r = O.instChartedSpace := rfl
  rw [hcharts]
  apply isLocalDiffeomorph_of_comp_left
    (A.regularFamilyInclusion_isLocalDiffeomorph)
    (regularFamilyInclusion_injective A.periods)
  have hsub := openSubtypeVal_isLocalDiffeomorph
    (I := globalDeckTotalModel) O
  convert hsub using 1
  · rfl
  · funext q
    exact regularFamilyInclusion_orderThreeCollarToRegular A.periods hproper D q

private theorem totalSpace_isManifold_analytic :
    letI := A.totalSpaceCharts
    IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  simpa [AnalyticData.totalSpaceCharts] using
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph A.periods ω).1

private theorem totalSpaceProjection_isLocalDiffeomorph_analytic :
    letI := A.totalSpaceCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  simpa [AnalyticData.totalSpaceCharts] using
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph A.periods ω).2

private theorem centralFamilyProjection_isLocalDiffeomorph :
    letI := regularFamilyDeckAction A.periods
    letI := A.regularTotalSpaceProductCharts
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold globalDeckBaseModel ∞
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a ∞).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  let cProduct : ChartedSpace (ℂ × ComplexTwoSpace) A.CentralFamily :=
    A.centralFamilyProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) A.CentralFamily := cProduct
  simpa [AnalyticData.centralFamilyProductCharts, regularSmoothnessOrder] using
    (fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.modular.modularParameter A.periods).2

public theorem orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (A.orderThreePuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts r
  let _ := A.regularTotalSpaceProductCharts
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold globalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) :=
    A.totalSpace_isManifold_analytic
  apply isLocalDiffeomorph_of_comp_surjective
    (A.orderThreeAffinePuncturedProjection_isLocalDiffeomorph r)
    Quotient.mk_surjective
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularFamilyDeckAction A.periods
  let gauge := orderThreePuncturedCollarGaugeDiffeomorph A.periods
    A.totalSpaceProjection_isLocalDiffeomorph_analytic r
  have hcarriercharts : orderThreeAffinePuncturedCarrierCharts A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r =
        orderThreePuncturedCollarCharts A.periods r := rfl
  rw [hcarriercharts]
  have hcomp : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      ((quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) ∘
        orderThreeCollarToRegular A.periods hproper D ∘ gauge) := by
    intro q
    exact IsLocalDiffeomorphAt.comp globalDeckTotalModel A.CentralFamily
      (IsLocalDiffeomorphAt.comp globalDeckTotalModel (RegularTotalSpace A.periods)
        (gauge.isLocalDiffeomorph q)
        (A.orderThreeCollarToRegular_isLocalDiffeomorph D (gauge q)))
      (A.centralFamilyProjection_isLocalDiffeomorph
        (orderThreeCollarToRegular A.periods hproper D (gauge q)))
  have heq : A.orderThreePuncturedCollarToCentralFamily D ∘
      Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)) =
      (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) ∘
        orderThreeCollarToRegular A.periods hproper D ∘ gauge := by
    funext q
    rfl
  rw [heq]
  exact hcomp

private theorem orderFourCollarToRegular_isLocalDiffeomorph {r : ℝ}
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.totalSpaceCharts
    letI := A.regularTotalSpaceProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (orderFourCollarToRegular A.periods
        (sourceActionProperlyDiscontinuous_of_eq
          A.modular.modularParameter.toTriangleUniformization_sourceAction) D) := by
  let _ := A.totalSpaceCharts
  let _ := A.regularTotalSpaceProductCharts
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨orderFourPuncturedFamilyCollar A.periods r,
      orderFourPuncturedFamilyCollar_isOpen A.periods r⟩
  have hcharts : orderFourPuncturedCollarCharts A.periods r = O.instChartedSpace := rfl
  rw [hcharts]
  apply isLocalDiffeomorph_of_comp_left
    (A.regularFamilyInclusion_isLocalDiffeomorph)
    (regularFamilyInclusion_injective A.periods)
  have hsub := openSubtypeVal_isLocalDiffeomorph
    (I := globalDeckTotalModel) O
  convert hsub using 1
  · rfl
  · funext q
    exact regularFamilyInclusion_orderFourCollarToRegular A.periods hproper D q

public theorem orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts r
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      (A.orderFourPuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts r
  let _ := A.regularTotalSpaceProductCharts
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold globalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) :=
    A.totalSpace_isManifold_analytic
  apply isLocalDiffeomorph_of_comp_surjective
    (A.orderFourAffinePuncturedProjection_isLocalDiffeomorph r)
    Quotient.mk_surjective
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularFamilyDeckAction A.periods
  let gauge := orderFourPuncturedCollarGaugeDiffeomorph A.periods
    A.totalSpaceProjection_isLocalDiffeomorph_analytic r
  have hcarriercharts : orderFourAffinePuncturedCarrierCharts A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r =
        orderFourPuncturedCollarCharts A.periods r := rfl
  rw [hcarriercharts]
  have hcomp : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ∞
      ((quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) ∘
        orderFourCollarToRegular A.periods hproper D ∘ gauge) := by
    intro q
    exact IsLocalDiffeomorphAt.comp globalDeckTotalModel A.CentralFamily
      (IsLocalDiffeomorphAt.comp globalDeckTotalModel (RegularTotalSpace A.periods)
        (gauge.isLocalDiffeomorph q)
        (A.orderFourCollarToRegular_isLocalDiffeomorph D (gauge q)))
      (A.centralFamilyProjection_isLocalDiffeomorph
        (orderFourCollarToRegular A.periods hproper D (gauge q)))
  have heq : A.orderFourPuncturedCollarToCentralFamily D ∘
      Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)) =
      (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) ∘
        orderFourCollarToRegular A.periods hproper D ∘ gauge := by
    funext q
    rfl
  rw [heq]
  exact hcomp

public def analyticCollarDiscPoint (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ComplexUnitDisc :=
  ⟨((r / 2 : ℝ) : ℂ), by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith⟩

public theorem analyticCollarDiscPoint_norm (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ‖(analyticCollarDiscPoint r hr hr1 : ℂ)‖ = r / 2 := by
  rw [analyticCollarDiscPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (half_pos hr)]

public theorem orderThreeAffinePuncturedQuotient_nonempty
    (P : A.OrderThreeFillingPiece) :
    Nonempty (A.OrderThreeAffinePuncturedQuotient P.radius) := by
  let r := P.radius
  let w := analyticCollarDiscPoint r P.radius_pos P.radius_lt_one
  let q : TotalSpace (parameterMap A.periods) :=
    Quotient.mk _ (orderThreeCayleyHomeomorph.symm w, 0)
  have hq : q ∈ orderThreePuncturedFamilyCollar A.periods r := by
    change 0 < orderThreeFamilyRadius A.periods q ∧
      orderThreeFamilyRadius A.periods q < r
    dsimp only [q]
    rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk,
      orderThreeCayleyHomeomorph.apply_symm_apply,
      analyticCollarDiscPoint_norm r P.radius_pos P.radius_lt_one]
    exact ⟨half_pos P.radius_pos, half_lt_self P.radius_pos⟩
  exact ⟨Quotient.mk _ ⟨q, hq⟩⟩

public theorem orderFourAffinePuncturedQuotient_nonempty
    (P : A.OrderFourFillingPiece) :
    Nonempty (A.OrderFourAffinePuncturedQuotient P.radius) := by
  let r := P.radius
  let w := analyticCollarDiscPoint r P.radius_pos P.radius_lt_one
  let q : TotalSpace (parameterMap A.periods) :=
    Quotient.mk _ (orderFourCayleyHomeomorph.symm w, 0)
  have hq : q ∈ orderFourPuncturedFamilyCollar A.periods r := by
    change 0 < orderFourFamilyRadius A.periods q ∧
      orderFourFamilyRadius A.periods q < r
    dsimp only [q]
    rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk,
      orderFourCayleyHomeomorph.apply_symm_apply,
      analyticCollarDiscPoint_norm r P.radius_pos P.radius_lt_one]
    exact ⟨half_pos P.radius_pos, half_lt_self P.radius_pos⟩
  exact ⟨Quotient.mk _ ⟨q, hq⟩⟩



public theorem centralFamilyProduct_isManifold :
    letI := A.centralFamilyProductCharts
    IsManifold globalDeckTotalModel ∞ A.CentralFamily := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold globalDeckBaseModel ∞
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a ∞).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper ∞
  let _ : IsManifold globalDeckTotalModel ∞ (RegularTotalSpace A.periods) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional globalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  let _ := A.centralFamilyProductCharts
  simpa [AnalyticData.centralFamilyProductCharts, regularSmoothnessOrder] using
    (fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.modular.modularParameter A.periods).1

public theorem orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
    (P : A.OrderThreeFillingPiece) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts P.radius
    letI := globalDeckComplexCharts (M := A.OrderThreeAffinePuncturedQuotient P.radius)
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderThreePuncturedCollarToCentralFamily P.sourceData) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts P.radius
  let _ : IsManifold globalDeckTotalModel ∞
      (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    A.orderThreeAffinePuncturedQuotient_isManifold P.radius
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold globalDeckTotalModel ∞ A.CentralFamily :=
    A.centralFamilyProduct_isManifold
  let h := A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph P.sourceData
  let _ : ChartedSpace ComplexModel (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.centralFamilyComplexCharts
  simpa only [AnalyticData.centralFamilyComplexCharts] using
    (isLocalDiffeomorph_globalDeckComplex h)

public theorem orderThreePuncturedCollarToFilling_isLocalDiffeomorph_complex
    (P : A.OrderThreeFillingPiece) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts P.radius
    letI := globalDeckComplexCharts (M := A.OrderThreeAffinePuncturedQuotient P.radius)
    letI := A.orderThreeFillingComplexCharts P.radius
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderThreePuncturedCollarToFilling P.radius) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts P.radius
  let _ : IsManifold globalDeckTotalModel ∞
      (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    A.orderThreeAffinePuncturedQuotient_isManifold P.radius
  let _ := A.orderThreeFillingSourceCharts P.radius
  let _ := A.orderThreeFillingAction P.radius
  let _ := A.orderThreeFillingProductCharts P.radius
  let _ : IsManifold globalDeckTotalModel ∞
      (A.OrderThreeVaryingFilling P.radius) :=
    A.orderThreeFillingProduct_isManifold P.radius
  let h := A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph P.radius
  let _ : ChartedSpace ComplexModel (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.orderThreeFillingComplexCharts P.radius
  simpa only [AnalyticData.orderThreeFillingComplexCharts] using
    (isLocalDiffeomorph_globalDeckComplex h)

public theorem orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
    (P : A.OrderFourFillingPiece) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts P.radius
    letI := globalDeckComplexCharts (M := A.OrderFourAffinePuncturedQuotient P.radius)
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderFourPuncturedCollarToCentralFamily P.sourceData) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts P.radius
  let _ : IsManifold globalDeckTotalModel ∞
      (A.OrderFourAffinePuncturedQuotient P.radius) :=
    A.orderFourAffinePuncturedQuotient_isManifold P.radius
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold globalDeckTotalModel ∞ A.CentralFamily :=
    A.centralFamilyProduct_isManifold
  let h := A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph P.sourceData
  let _ : ChartedSpace ComplexModel (A.OrderFourAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.centralFamilyComplexCharts
  simpa only [AnalyticData.centralFamilyComplexCharts] using
    (isLocalDiffeomorph_globalDeckComplex h)

public theorem orderFourPuncturedCollarToFilling_isLocalDiffeomorph_complex
    (P : A.OrderFourFillingPiece) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts P.radius
    letI := globalDeckComplexCharts (M := A.OrderFourAffinePuncturedQuotient P.radius)
    letI := A.orderFourFillingComplexCharts P.radius
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderFourPuncturedCollarToFilling P.radius) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts P.radius
  let _ : IsManifold globalDeckTotalModel ∞
      (A.OrderFourAffinePuncturedQuotient P.radius) :=
    A.orderFourAffinePuncturedQuotient_isManifold P.radius
  let _ := A.orderFourFillingSourceCharts P.radius
  let _ := A.orderFourFillingAction P.radius
  let _ := A.orderFourFillingProductCharts P.radius
  let _ : IsManifold globalDeckTotalModel ∞
      (A.OrderFourVaryingFilling P.radius) :=
    A.orderFourFillingProduct_isManifold P.radius
  let h := A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph P.radius
  let _ : ChartedSpace ComplexModel (A.OrderFourAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.orderFourFillingComplexCharts P.radius
  simpa only [AnalyticData.orderFourFillingComplexCharts] using
    (isLocalDiffeomorph_globalDeckComplex h)

public noncomputable def orderThreeFillingCollarPartialDiffeomorph
    (P : A.OrderThreeFillingPiece) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderThreeFillingComplexCharts P.radius
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (A.OrderThreeVaryingFilling P.radius) ∞ := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts P.radius
  let _ : ChartedSpace ComplexModel (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.centralFamilyComplexCharts
  let _ := A.orderThreeFillingComplexCharts P.radius
  let _ : Nonempty (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    A.orderThreeAffinePuncturedQuotient_nonempty P
  exact partialDiffeomorphBetweenOpenEmbeddings
    (A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding P.sourceData)
    (A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph_complex P)
    (A.orderThreePuncturedCollarToFilling_isOpenEmbedding P.radius)
    (A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph_complex P)

public noncomputable def orderFourFillingCollarPartialDiffeomorph
    (P : A.OrderFourFillingPiece) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderFourFillingComplexCharts P.radius
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (A.OrderFourVaryingFilling P.radius) ∞ := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts P.radius
  let _ : ChartedSpace ComplexModel (A.OrderFourAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.centralFamilyComplexCharts
  let _ := A.orderFourFillingComplexCharts P.radius
  let _ : Nonempty (A.OrderFourAffinePuncturedQuotient P.radius) :=
    A.orderFourAffinePuncturedQuotient_nonempty P
  exact partialDiffeomorphBetweenOpenEmbeddings
    (A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding P.sourceData)
    (A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph_complex P)
    (A.orderFourPuncturedCollarToFilling_isOpenEmbedding P.radius)
    (A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph_complex P)

@[simp]
public theorem orderThreeFillingCollarPartialDiffeomorph_source
    (P : A.OrderThreeFillingPiece) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderThreeFillingComplexCharts P.radius
    (A.orderThreeFillingCollarPartialDiffeomorph P).source =
      range (A.orderThreePuncturedCollarToCentralFamily P.sourceData) := by
  simp [orderThreeFillingCollarPartialDiffeomorph]

@[simp]
public theorem orderThreeFillingCollarPartialDiffeomorph_target
    (P : A.OrderThreeFillingPiece) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderThreeFillingComplexCharts P.radius
    (A.orderThreeFillingCollarPartialDiffeomorph P).target =
      range (A.orderThreePuncturedCollarToFilling P.radius) := by
  simp [orderThreeFillingCollarPartialDiffeomorph]

@[simp]
public theorem orderThreeFillingCollarPartialDiffeomorph_apply
    (P : A.OrderThreeFillingPiece) (x : A.OrderThreeAffinePuncturedQuotient P.radius) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderThreeFillingComplexCharts P.radius
    A.orderThreeFillingCollarPartialDiffeomorph P
        (A.orderThreePuncturedCollarToCentralFamily P.sourceData x) =
      A.orderThreePuncturedCollarToFilling P.radius x := by
  simp [orderThreeFillingCollarPartialDiffeomorph]

@[simp]
public theorem orderFourFillingCollarPartialDiffeomorph_source
    (P : A.OrderFourFillingPiece) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderFourFillingComplexCharts P.radius
    (A.orderFourFillingCollarPartialDiffeomorph P).source =
      range (A.orderFourPuncturedCollarToCentralFamily P.sourceData) := by
  simp [orderFourFillingCollarPartialDiffeomorph]

@[simp]
public theorem orderFourFillingCollarPartialDiffeomorph_target
    (P : A.OrderFourFillingPiece) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderFourFillingComplexCharts P.radius
    (A.orderFourFillingCollarPartialDiffeomorph P).target =
      range (A.orderFourPuncturedCollarToFilling P.radius) := by
  simp [orderFourFillingCollarPartialDiffeomorph]

@[simp]
public theorem orderFourFillingCollarPartialDiffeomorph_apply
    (P : A.OrderFourFillingPiece) (x : A.OrderFourAffinePuncturedQuotient P.radius) :
    letI := A.centralFamilyComplexCharts
    letI := A.orderFourFillingComplexCharts P.radius
    A.orderFourFillingCollarPartialDiffeomorph P
        (A.orderFourPuncturedCollarToCentralFamily P.sourceData x) =
      A.orderFourPuncturedCollarToFilling P.radius x := by
  simp [orderFourFillingCollarPartialDiffeomorph]

end AnalyticData

end

end

end SphereSixComplex.Geometry
