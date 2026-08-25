module

public import SphereSixComplex.Geometry.CuspPuncturedCollarBridge
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import SphereSixComplex.Geometry.LocalDiffeomorphTransport
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Analytic cusp filling collar

This module upgrades the explicit topological cusp collar to an ambient complex partial
diffeomorphism.  Its only external analytic input is the standard local-biholomorphism theorem
for the explicit coordinatewise exponential.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.CuspAnalyticFillingCollar

open Set Topology
open SphereSixComplex SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus AnalyticTorusFamily TorusFamily GlobalTorusFamily
open CuspCombinatorics CuspFilling CuspLocalPhaseAction CuspPeriodExpansion
open CuspPuncturedCollarBridge StandardInfiniteA2ToricModel
open EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

noncomputable section

/-- The explicit exponential-radius domain is open in its additive complex vector space. -/
public theorem additiveCuspRadiusCover_isOpen (r : ℝ) :
    IsOpen (additiveCuspRadiusCover r) := by
  rw [additiveCuspRadiusCover, denseTorusCuspRegion]
  have hcoord : Continuous (fun x : DenseTorus ↦ ((x 2 : ℂˣ) : ℂ)) :=
    Units.continuous_val.comp (continuous_apply 2)
  exact (isOpen_lt
    (hcoord.norm.comp
      denseCuspExponentialCover_isQuotientMap.continuous)
    continuous_const)

/-- Product-model charts on the open additive exponential-radius domain. -/
@[expose, instance_reducible]
public noncomputable def additiveCuspRadiusCoverCharts (r : ℝ) :
    ChartedSpace AdditiveCuspCover (additiveCuspRadiusCover r) := by
  let U : TopologicalSpace.Opens AdditiveCuspCover :=
    ⟨additiveCuspRadiusCover r, additiveCuspRadiusCover_isOpen r⟩
  change ChartedSpace AdditiveCuspCover U
  infer_instance

private theorem additiveCuspRadiusCover_isManifold (r : ℝ) :
    letI := additiveCuspRadiusCoverCharts r
    IsManifold (modelWithCornersSelf ℂ AdditiveCuspCover) ∞
      (additiveCuspRadiusCover r) := by
  let _ := additiveCuspRadiusCoverCharts r
  let U : TopologicalSpace.Opens AdditiveCuspCover :=
    ⟨additiveCuspRadiusCover r, additiveCuspRadiusCover_isOpen r⟩
  change IsManifold (modelWithCornersSelf ℂ AdditiveCuspCover) ∞ U
  infer_instance

private theorem additiveCuspRadiusCover_subtypeVal_contMDiff (r : ℝ) :
    letI := additiveCuspRadiusCoverCharts r
    ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ AdditiveCuspCover) ∞
      (Subtype.val : additiveCuspRadiusCover r → AdditiveCuspCover) := by
  let _ := additiveCuspRadiusCoverCharts r
  let U : TopologicalSpace.Opens AdditiveCuspCover :=
    ⟨additiveCuspRadiusCover r, additiveCuspRadiusCover_isOpen r⟩
  change ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
    (modelWithCornersSelf ℂ AdditiveCuspCover) ∞ (Subtype.val : U → AdditiveCuspCover)
  exact contMDiff_subtype_val

private theorem openSubtypeVal_isLocalDiffeomorph
    {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold (modelWithCornersSelf ℂ V) ∞ M]
    (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) ∞
      (Subtype.val : U → M) := by
  classical
  intro x
  let inv : M → U := fun y => if h : y ∈ U then ⟨y, h⟩ else x
  let phi : PartialDiffeomorph (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) U M ∞ :=
    { toPartialEquiv :=
        { toFun := Subtype.val
          invFun := inv
          source := univ
          target := U
          map_source' := fun y _ ↦ y.2
          map_target' := fun _ _ ↦ trivial
          left_inv' := by
            intro y _
            apply Subtype.ext
            exact congrArg Subtype.val (dif_pos y.2)
          right_inv' := by
            intro y hy
            exact congrArg Subtype.val (dif_pos hy) }
      open_source := isOpen_univ
      open_target := U.isOpen
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U inv U y]
        apply contMDiffWithinAt_id.congr
        · intro z hz
          exact congrArg Subtype.val (dif_pos hz)
        · exact congrArg Subtype.val (dif_pos hy) }
  exact PartialDiffeomorph.isLocalDiffeomorphAt
    (I := modelWithCornersSelf ℂ V) (J := modelWithCornersSelf ℂ V)
    (n := ∞) phi trivial

private theorem openSubtypeVal_isLocalDiffeomorph_model
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → M) := by
  classical
  intro x
  let inv : M → U := fun y => if h : y ∈ U then ⟨y, h⟩ else x
  let phi : PartialDiffeomorph I I U M ∞ :=
    { toPartialEquiv :=
        { toFun := Subtype.val
          invFun := inv
          source := univ
          target := U
          map_source' := fun y _ ↦ y.2
          map_target' := fun _ _ ↦ trivial
          left_inv' := by
            intro y _
            apply Subtype.ext
            exact congrArg Subtype.val (dif_pos y.2)
          right_inv' := by
            intro y hy
            exact congrArg Subtype.val (dif_pos hy) }
      open_source := isOpen_univ
      open_target := U.isOpen
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U inv U y]
        apply contMDiffWithinAt_id.congr
        · intro z hz
          exact congrArg Subtype.val (dif_pos hz)
        · exact congrArg Subtype.val (dif_pos hy) }
  exact PartialDiffeomorph.isLocalDiffeomorphAt
    (I := I) (J := I) (n := ∞) phi trivial

/-- A local diffeomorphism whose range lies in an open submanifold remains locally
biholomorphic after restricting its codomain.  This is the standard open-submanifold
codomain-restriction theorem missing from Mathlib's current local-diffeomorphism API. -/
public theorem isLocalDiffeomorph_codRestrict_open
    {V V' M N : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V']
    [TopologicalSpace M] [ChartedSpace V M]
    [TopologicalSpace N] [ChartedSpace V' N]
    [IsManifold (modelWithCornersSelf ℂ V) ∞ M]
    [IsManifold (modelWithCornersSelf ℂ V') ∞ N]
    (U : TopologicalSpace.Opens N) (f : M → N)
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V') ∞ f) (hU : ∀ x, f x ∈ U) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V') ∞ (fun x ↦ (⟨f x, hU x⟩ : U)) := by
  intro x
  obtain ⟨phi, hx, heq⟩ := hf x
  let g : M → U := fun y ↦ ⟨f y, hU y⟩
  let psi : PartialDiffeomorph (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V') M U ∞ :=
    { toPartialEquiv :=
        { toFun := g
          invFun := fun y ↦ phi.invFun y.1
          source := phi.source
          target := Subtype.val ⁻¹' phi.target
          map_source' := by
            intro y hy
            change f y ∈ phi.target
            rw [heq hy]
            exact phi.map_source hy
          map_target' := fun _ hy ↦ phi.map_target hy
          left_inv' := by
            intro y hy
            change phi.invFun (f y) = y
            rw [heq hy]
            exact phi.left_inv hy
          right_inv' := by
            intro y hy
            apply Subtype.ext
            exact (heq (phi.map_target hy)).trans (phi.right_inv hy) }
      open_source := phi.open_source
      open_target := phi.open_target.preimage continuous_subtype_val
      contMDiffOn_toFun := by
        intro y hy
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U g phi.source y]
        exact (phi.contMDiffOn_toFun y hy).congr
          (fun z hz ↦ heq hz) (heq hy)
      contMDiffOn_invFun :=
        phi.contMDiffOn_invFun.comp contMDiff_subtype_val.contMDiffOn
          (fun _ hy ↦ hy) }
  exact ⟨psi, hx, fun _ _ ↦ rfl⟩

private noncomputable def partialDiffeomorphOfLocalCovers
    {E F G H H' H'' X A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ F H'}
    {K : ModelWithCorners ℂ G H''}
    [TopologicalSpace X] [ChartedSpace H X]
    [TopologicalSpace A] [ChartedSpace H' A]
    [TopologicalSpace B] [ChartedSpace H'' B]
    {n : WithTop ℕ∞}
    (e : OpenPartialHomeomorph A B) {p : X → A} {q : X → B}
    (hp : IsLocalDiffeomorph I J n p) (hq : IsLocalDiffeomorph I K n q)
    (hcompat : ∀ x, e (p x) = q x)
    (hp_source : ∀ x, p x ∈ e.source)
    (hsource : e.source ⊆ Set.range p) (htarget : e.target ⊆ Set.range q) :
    PartialDiffeomorph J K A B n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := by
    intro y hy
    obtain ⟨x, rfl⟩ := hsource hy
    let s := (hp x).localInverse
    have hs : ContMDiffAt J I n s (p x) := (hp x).localInverse_contMDiffAt
    have hqs : ContMDiffAt J K n (q ∘ s) (p x) :=
      (hq x).contMDiffAt.comp_of_eq hs (by
        rw [(hp x).localInverse_left_inv (hp x).localInverse_mem_target])
    have hevent : e =ᶠ[nhds (p x)] q ∘ s := by
      filter_upwards [(hp x).localInverse_eventuallyEq_right] with z hz
      calc
        e z = e (p (s z)) := congrArg e hz.symm
        _ = q (s z) := hcompat (s z)
    exact hqs.congr_of_eventuallyEq hevent |>.contMDiffWithinAt
  contMDiffOn_invFun := by
    intro y hy
    obtain ⟨x, rfl⟩ := htarget hy
    let s := (hq x).localInverse
    have hs : ContMDiffAt K I n s (q x) := (hq x).localInverse_contMDiffAt
    have hps : ContMDiffAt K J n (p ∘ s) (q x) :=
      (hp x).contMDiffAt.comp_of_eq hs (by
        rw [(hq x).localInverse_left_inv (hq x).localInverse_mem_target])
    have hevent : e.symm =ᶠ[nhds (q x)] p ∘ s := by
      filter_upwards [(hq x).localInverse_eventuallyEq_right] with z hz
      change q (s z) = z at hz
      calc
        e.symm z = e.symm (e (p (s z))) := by rw [hcompat, hz]
        _ = p (s z) := e.left_inv (hp_source (s z))
    exact hps.congr_of_eventuallyEq hevent |>.contMDiffWithinAt

/-- The normalized regular bundle chart region as an ambient open subset. -/
@[expose] public noncomputable def regularCuspBundleOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    TopologicalSpace.Opens
      (RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace) :=
  ⟨{p | p.1.1 ∈ normalizedCuspRegion N W.localWitness.radius},
    W.region_open.preimage (continuous_subtype_val.comp continuous_fst)⟩

/-- Standard complex coordinates on the normalized regular bundle region. -/
public def regularCuspBundleCoordinates
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    regularCuspBundleRegion W → ModelProd ℂ ComplexTwoSpace :=
  fun p ↦ ((p.1.1.1 : ℂ), p.1.2)

public theorem regularCuspBundleCoordinates_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (regularCuspBundleCoordinates W) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  have hregular : IsOpenEmbedding
      (fun z : RegularBase (U := E.modularParameter.toTriangleUniformization) ↦ (z.1 : ℂ)) := by
    have hsub : IsOpenEmbedding
        (Subtype.val : RegularBase (U := E.modularParameter.toTriangleUniformization) →
          UpperHalfPlane) :=
      (isOpen_isRegularBasePoint hproper).isOpenEmbedding_subtypeVal
    convert UpperHalfPlane.isOpenEmbedding_coe.comp hsub using 1
    funext z
    rfl
  let productCoordinates :
      RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace →
        ModelProd ℂ ComplexTwoSpace :=
    fun p ↦ ((p.1.1 : ℂ), p.2)
  have hproduct : IsOpenEmbedding productCoordinates := by
    have hproduct' : IsOpenEmbedding
        (fun p : RegularBase (U := E.modularParameter.toTriangleUniformization) ×
            ComplexTwoSpace ↦ ((p.1.1 : ℂ), p.2)) :=
      hregular.prodMap Topology.IsOpenEmbedding.id
    simpa only [ModelProd, instTopologicalSpaceModelProd] using hproduct'
  have hregion : IsOpenEmbedding
      (Subtype.val : regularCuspBundleRegion W →
        RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace) :=
    (regularCuspBundleOpen W).isOpen.isOpenEmbedding_subtypeVal
  convert hproduct.comp hregion using 1
  funext p
  rfl

public theorem additiveCuspRadiusCover_nonempty (r : ℝ) (hr : 0 < r) :
    Nonempty (additiveCuspRadiusCover r) := by
  let u : ℂˣ := Units.mk0 (r / 2 : ℂ) (by
    exact_mod_cast (div_ne_zero (ne_of_gt hr) (by norm_num : (2 : ℝ) ≠ 0)))
  let x : DenseTorus := ![1, 1, u]
  obtain ⟨p, hp⟩ := denseCuspExponentialCover_isQuotientMap.surjective x
  refine ⟨⟨p, ?_⟩⟩
  change ‖(((denseCuspExponentialCover p 2 : ℂˣ) : ℂ))‖ < r
  rw [hp]
  change ‖(r / 2 : ℂ)‖ < r
  rw [norm_div, Complex.norm_real]
  norm_num [Real.norm_eq_abs, abs_of_pos hr]
  exact hr

public theorem regularCuspBundleRegion_nonempty
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Nonempty (regularCuspBundleRegion W) :=
  (additiveCuspBundleHomeomorph W).toEquiv.nonempty_congr.mp
    (additiveCuspRadiusCover_nonempty W.localWitness.radius W.localWitness.radius_pos)

/-- Product charts inherited from the ambient regular vector bundle. -/
@[expose, instance_reducible]
public noncomputable def regularCuspBundleRegionCharts
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (regularCuspBundleRegion W) :=
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let U := regularCuspBundleOpen W
  show ChartedSpace (ModelProd ℂ ComplexTwoSpace) U from inferInstance

private theorem normalizedLift_contMDiffOn
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
      (fun s : ℂ ↦ (N.lift s : ℂ)) (cuspHalfPlane N.height) := by
  have hmd : MDiff[cuspHalfPlane N.height] (fun s : ℂ ↦ (N.lift s : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp_mdifferentiableOn N.lift_holomorphic
  exact ((mdifferentiableOn_iff_differentiableOn.mp hmd).contDiffOn
    (isOpen_lt continuous_const Complex.continuous_im)).contMDiffOn

private theorem additiveCuspBundleHomeomorph_contMDiff
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := regularCuspBundleRegionCharts W
    ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      GlobalDeckTotalModel ∞
      (additiveCuspBundleHomeomorph W) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := regularBaseChartedSpace hproper
  let _ := regularCuspBundleRegionCharts W
  have hs : ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ℂ) ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ p.1.2) :=
    contDiff_snd.contMDiff.comp
      (additiveCuspRadiusCover_subtypeVal_contMDiff W.localWitness.radius)
  have hliftVal : ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ℂ) ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ (N.lift p.1.2 : ℂ)) :=
    (normalizedLift_contMDiffOn N).comp_contMDiff hs
      (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
  have hzeta : ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexTwoSpace) ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ p.1.1) :=
    contDiff_fst.contMDiff.comp
      (additiveCuspRadiusCover_subtypeVal_contMDiff W.localWitness.radius)
  have hliftUpper : ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      GlobalDeckBaseModel ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ N.lift p.1.2) :=
    hliftVal.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe
  have hliftRegular : ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      GlobalDeckBaseModel ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        (⟨N.lift p.1.2, W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2⟩ :
          RegularBase (U := E.modularParameter.toTriangleUniformization))) := by
    apply (ContMDiff.subtypeVal_comp_iff (regularBaseOpen hproper) _).mp
    exact hliftUpper
  have hambient : ContMDiff (modelWithCornersSelf ℂ AdditiveCuspCover)
      GlobalDeckTotalModel ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        ((additiveCuspBundleHomeomorph W p).1 :
          RegularBase (U := E.modularParameter.toTriangleUniformization) ×
            ComplexTwoSpace)) := by
    exact hliftRegular.prodMk hzeta
  apply (ContMDiff.subtypeVal_comp_iff (regularCuspBundleOpen W) _).mp
  exact hambient

private theorem additiveCuspBundleHomeomorph_symm_contMDiff
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := regularCuspBundleRegionCharts W
    ContMDiff GlobalDeckTotalModel
      (modelWithCornersSelf ℂ AdditiveCuspCover) ∞
      (additiveCuspBundleHomeomorph W).symm := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := regularBaseChartedSpace hproper
  let _ := regularCuspBundleRegionCharts W
  have hval : ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (Subtype.val : regularCuspBundleRegion W →
        RegularBase (U := E.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) :=
    by
      change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
        (Subtype.val : (regularCuspBundleOpen W) →
          RegularBase (U := E.modularParameter.toTriangleUniformization) ×
            ComplexTwoSpace)
      exact contMDiff_subtype_val
  have hbase : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel ∞
      (fun p : regularCuspBundleRegion W ↦ p.1.1) :=
    contMDiff_fst.comp hval
  have hregularVal : ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel ∞
      (Subtype.val : RegularBase (U := E.modularParameter.toTriangleUniformization) →
        UpperHalfPlane) := by
    change ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel ∞
      (Subtype.val : (regularBaseOpen hproper) → UpperHalfPlane)
    exact contMDiff_subtype_val
  have hbaseUpper : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel ∞
      (fun p : regularCuspBundleRegion W ↦ p.1.1.1) :=
    hregularVal.comp hbase
  have htau : ContMDiff GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) ∞
      (fun p : regularCuspBundleRegion W ↦
        (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ)) :=
    (tau_contMDiff (assembledFuchsianPeriodFunctions E D) ∞).comp hbaseUpper
  have hzeta : ContMDiff GlobalDeckTotalModel
      (modelWithCornersSelf ℂ ComplexTwoSpace) ∞
      (fun p : regularCuspBundleRegion W ↦ p.1.2) :=
    contMDiff_snd.comp hval
  have hambient : ContMDiff GlobalDeckTotalModel
      (modelWithCornersSelf ℂ AdditiveCuspCover) ∞
      (fun p : regularCuspBundleRegion W ↦
        (p.1.2,
          (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ))) :=
    (contMDiff_prod_module_iff _).2 ⟨hzeta, htau⟩
  apply (ContMDiff.subtypeVal_comp_iff
    (⟨additiveCuspRadiusCover W.localWitness.radius,
      additiveCuspRadiusCover_isOpen W.localWitness.radius⟩ :
      TopologicalSpace.Opens AdditiveCuspCover) _).mp
  convert hambient using 1
  funext p
  rfl

private noncomputable def additiveCuspBundleDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := regularCuspBundleRegionCharts W
    Diffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover) GlobalDeckTotalModel
      (additiveCuspRadiusCover W.localWitness.radius) (regularCuspBundleRegion W) ∞ := by
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := regularCuspBundleRegionCharts W
  exact
    { toEquiv := (additiveCuspBundleHomeomorph W).toEquiv
      contMDiff_toFun := additiveCuspBundleHomeomorph_contMDiff W
      contMDiff_invFun := additiveCuspBundleHomeomorph_symm_contMDiff W }

/-! ## The coordinatewise exponential is locally biholomorphic

The dense torus is charted by its open embedding into `ℂ³`, so the exponential cover reads in
coordinates as `(z₀, z₁, s) ↦ (e^{2πi z₀}, e^{2πi z₁}, e^{2πi s})`.  That map is holomorphic with
everywhere invertible derivative — the diagonal scaling by the three nonzero numbers
`2πi e^{2πi ·}` — so the inverse function theorem makes it a local biholomorphism, and the two
transport lemmas move that back to the manifolds. -/

/-- The scalar `2πi`, the frequency of the cusp exponential. -/
private noncomputable def twoPiI : ℂ := 2 * Real.pi * Complex.I

private theorem twoPiI_ne_zero : twoPiI ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The coordinate representative of the cusp exponential cover. -/
private noncomputable def expCoords (p : AdditiveCuspCover) : ComplexModel :=
  denseTorusComplexCoordinates (denseCuspExponentialCover p)

/-- The linear identification of the additive cusp cover `ℂ² × ℂ` with `ℂ³`. -/
private noncomputable def additiveCoordEquiv : AdditiveCuspCover ≃L[ℂ] ComplexModel :=
  (ContinuousLinearEquiv.equivOfInverse
      (ContinuousLinearMap.pi
        ![(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).comp
            (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ℂ),
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).comp
            (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) ℂ),
          ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) ℂ])
      ((ContinuousLinearMap.pi
          ![ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 0,
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 1]).prod
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 2))
      (by
        intro v
        ext i
        · fin_cases i <;> rfl
        · rfl)
      (by
        intro v
        funext i
        fin_cases i <;> rfl)).trans
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm

/-- The exponential in the three coordinates of `ℂ³`. -/
private noncomputable def expOnThree (x : ComplexModel) : ComplexModel :=
  WithLp.toLp 2 (fun i ↦ Complex.exp (twoPiI * WithLp.ofLp x i))

private theorem expCoords_eq : expCoords = expOnThree ∘ additiveCoordEquiv := by
  funext p
  apply congrArg (WithLp.toLp 2)
  funext i
  fin_cases i <;> rfl

private theorem contDiff_expOnThree : ContDiff ℂ ∞ expOnThree := by
  have h : ContDiff ℂ ∞
      (fun x : ComplexModel ↦ (fun i ↦ Complex.exp (twoPiI * WithLp.ofLp x i))) := by
    refine contDiff_pi.mpr fun i ↦ ?_
    have hcoord : ContDiff ℂ ∞ (fun x : ComplexModel ↦ WithLp.ofLp x i) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) i).contDiff.comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).contDiff
    exact Complex.contDiff_exp.comp (contDiff_const.mul hcoord)
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm.contDiff.comp h

/-- Diagonal scaling of `ℂ³` by three nonzero factors. -/
private noncomputable def diagScale (a : Fin 3 → ℂˣ) : ComplexModel ≃L[ℂ] ComplexModel :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).trans
    (ContinuousLinearEquiv.piCongrRight
      (fun i ↦ ContinuousLinearEquiv.unitsEquivAut ℂ (a i)))).trans
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm

/-- The derivative of the coordinate exponential at a point of `ℂ³`. -/
private noncomputable def expOnThreeDeriv (x : ComplexModel) : ComplexModel ≃L[ℂ] ComplexModel :=
  diagScale (fun i ↦ Units.mk0 (twoPiI * Complex.exp (twoPiI * WithLp.ofLp x i))
    (mul_ne_zero twoPiI_ne_zero (Complex.exp_ne_zero _)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem hasFDerivAt_expOnThree (x : ComplexModel) :
    HasFDerivAt expOnThree ((expOnThreeDeriv x : ComplexModel →L[ℂ] ComplexModel)) x := by
  set c : Fin 3 → ℂ := fun i ↦ twoPiI * Complex.exp (twoPiI * WithLp.ofLp x i) with hc
  have hpi : HasFDerivAt (fun y : ComplexModel ↦ (fun i ↦ Complex.exp (twoPiI * WithLp.ofLp y i)))
      (ContinuousLinearMap.pi fun i ↦ (c i) •
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) i).comp
          (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ) :
            ComplexModel →L[ℂ] (Fin 3 → ℂ)))) x := by
    refine hasFDerivAt_pi.mpr fun i ↦ ?_
    set L : ComplexModel →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) i).comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ) :
          ComplexModel →L[ℂ] (Fin 3 → ℂ)) with hL
    have hcoord : HasFDerivAt (fun y : ComplexModel ↦ WithLp.ofLp y i) L x := L.hasFDerivAt
    have hmul := hcoord.const_mul twoPiI
    have hexp := (Complex.hasDerivAt_exp (twoPiI * WithLp.ofLp x i)).comp_hasFDerivAt x hmul
    have hsmul : Complex.exp (twoPiI * WithLp.ofLp x i) • (twoPiI • L) = c i • L := by
      rw [smul_smul, hc]
      congr 1
      exact mul_comm _ _
    rwa [hsmul] at hexp
  have hcomp := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm.hasFDerivAt.comp x hpi
  refine hcomp.congr_fderiv ?_
  ext y i
  show c i * WithLp.ofLp y i = WithLp.ofLp y i * c i
  exact mul_comm _ _

set_option maxHeartbeats 1000000 in
private theorem isLocalDiffeomorph_expCoords :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞ expCoords := by
  rw [expCoords_eq]
  refine isLocalDiffeomorph_of_contDiff_of_hasFDerivAt_equiv
    (contDiff_expOnThree.comp additiveCoordEquiv.contDiff) fun p ↦ ?_
  refine ⟨additiveCoordEquiv.trans (expOnThreeDeriv (additiveCoordEquiv p)), ?_⟩
  have hchain :=
    (hasFDerivAt_expOnThree (additiveCoordEquiv p)).comp p additiveCoordEquiv.hasFDerivAt
  refine hchain.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rfl

private theorem isLocalDiffeomorph_denseCuspExponentialCover :
    letI := denseTorusCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞ denseCuspExponentialCover := by
  refine isLocalDiffeomorph_of_comp_isOpenEmbedding
    denseTorusComplexCoordinates_isOpenEmbedding ?_
  exact isLocalDiffeomorph_expCoords

namespace Established

/-- The coordinatewise complex exponential is locally biholomorphic on every open radius
restriction: in the charts of both sides it is
`(z₀, z₁, s) ↦ (e^{2πi z₀}, e^{2πi z₁}, e^{2πi s})`, whose derivative is the diagonal scaling by
the nonzero numbers `2πi e^{2πi ·}`. -/
public theorem denseCuspExponentialCover_isLocalDiffeomorph (r : ℝ) :
    letI := additiveCuspRadiusCoverCharts r
    letI := denseTorusCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p : additiveCuspRadiusCover r ↦ denseCuspExponentialCover p) := by
  letI := additiveCuspRadiusCoverCharts r
  letI := denseTorusCharts
  exact isLocalDiffeomorph_comp isLocalDiffeomorph_denseCuspExponentialCover
    (openSubtypeVal_isLocalDiffeomorph
      ⟨additiveCuspRadiusCover r, additiveCuspRadiusCover_isOpen r⟩)

end Established

/-- Composing the coordinate exponential with the canonical dense-torus chart gives a local
biholomorphism into the punctured local toric carrier. -/
public theorem additiveCuspExponentialPoint_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := M.topology
    letI := M.charts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
          (mem_ball_zero_iff.mpr p.2)) := by
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := denseTorusCharts
  let _ := M.topology
  let _ := M.charts
  let _ : IsManifold (modelWithCornersSelf ℂ AdditiveCuspCover) ∞
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspRadiusCover_isManifold W.localWitness.radius
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ M.Carrier := M.manifold
  have hexp := Established.denseCuspExponentialCover_isLocalDiffeomorph
    W.localWitness.radius
  have hambient : IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (M.torusEmbedding ∘ fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        denseCuspExponentialCover p) := by
    intro p
    exact IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ComplexModel) M.Carrier
      (hexp p) (M.torusEmbedding_isLocalDiffeomorph (denseCuspExponentialCover p))
  have hmem : ∀ p : additiveCuspRadiusCover W.localWitness.radius,
      (M.torusEmbedding (denseCuspExponentialCover p)) ∈
        cuspNeighborhood M W.localWitness.radius := by
    intro p
    change M.t (M.torusEmbedding (denseCuspExponentialCover p)) ∈
      Metric.ball 0 W.localWitness.radius
    rw [M.t_torus]
    exact mem_ball_zero_iff.mpr p.2
  have hlocal := isLocalDiffeomorph_codRestrict_open
    (cuspNeighborhood M W.localWitness.radius)
    (M.torusEmbedding ∘ fun p : additiveCuspRadiusCover W.localWitness.radius ↦
      denseCuspExponentialCover p) hambient hmem
  convert hlocal using 1
  funext p
  apply Subtype.ext
  rfl

/-- The normalized cusp lift and its exact inverse `tau` give a locally biholomorphic product
chart from additive cusp coordinates to the regular vector-bundle cover. -/
public theorem additiveCuspBundleMap_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := regularBaseChartedSpace hproper
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      GlobalDeckTotalModel ∞
      (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        (additiveCuspBundleHomeomorph W p).1) := by
  dsimp only
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := regularBaseChartedSpace hproper
  let _ := regularCuspBundleRegionCharts W
  let _ : IsManifold GlobalDeckBaseModel ∞
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ : IsManifold GlobalDeckTotalModel ∞
      (RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace) :=
    inferInstance
  have hbundle := (additiveCuspBundleDiffeomorph W).isLocalDiffeomorph
  have hinclusion : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (Subtype.val : regularCuspBundleRegion W →
        RegularBase (U := E.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) := by
    change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (Subtype.val : (regularCuspBundleOpen W) →
        RegularBase (U := E.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace)
    exact openSubtypeVal_isLocalDiffeomorph_model GlobalDeckTotalModel
      (regularCuspBundleOpen W)
  intro p
  have hcomp := IsLocalDiffeomorphAt.comp GlobalDeckTotalModel _
    (hbundle p) (hinclusion (additiveCuspBundleHomeomorph W p))
  convert hcomp using 1
  funext x
  rfl

private noncomputable def additiveCuspCoverToPuncturedQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius → puncturedLocalCuspQuotient W :=
  fun p ↦ Quotient.mk _
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ p))

private theorem puncturedLocalCuspQuotientMap_additiveCover
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspQuotientMap W (additiveCuspCoverToPuncturedQuotient W p) =
      additiveCuspCoverToGlobal W p := by
  rw [additiveCuspCoverToPuncturedQuotient, puncturedLocalCuspQuotientMap_mk]
  dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply]
  rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]

/-- The additive exponential cover mapped into the full local filling. -/
public noncomputable def additiveCuspCoverToFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius → actualLocalCuspFilling W :=
  fun p ↦ Quotient.mk _
    (localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
      (mem_ball_zero_iff.mpr p.2))

public theorem additiveCuspCoverToFilling_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := actualLocalCuspFillingCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (additiveCuspCoverToFilling W) := by
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := actualLocalCuspFillingCharts W
  let f := fun p : additiveCuspRadiusCover W.localWitness.radius ↦
    localCuspExponentialPoint M W.localWitness.radius p.1.1 p.1.2
      (mem_ball_zero_iff.mpr p.2)
  have hf := additiveCuspExponentialPoint_isLocalDiffeomorph W
  have hq := actualLocalCuspFilling_projection_isLocalDiffeomorph W
  intro p
  have hcomp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      ((Quotient.mk _ : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) ∘ f) p :=
    IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ComplexModel)
      (actualLocalCuspFilling W) (hf p) (hq (f p))
  convert hcomp using 1
  funext x
  rfl

private theorem puncturedLocalCuspToFilling_additiveCover
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspToFilling W (additiveCuspCoverToPuncturedQuotient W p) =
      additiveCuspCoverToFilling W p := by
  rw [additiveCuspCoverToPuncturedQuotient, puncturedLocalCuspToFilling_mk]
  unfold additiveCuspCoverToFilling
  apply congrArg (Quotient.mk _)
  exact additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius p

private theorem additiveCuspCoverToGlobal_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set.range (additiveCuspCoverToGlobal W) = puncturedGlobalCuspCollar W := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, rfl⟩
    exact actualPuncturedGlobalCuspPoint_mem_collar W p.1.2
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2 p.1.1
  · rw [← puncturedLocalCuspQuotientMap_range W]
    rintro y ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | _ u =>
      let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      obtain ⟨v, hv⟩ := e.surjective u
      induction v using Quotient.inductionOn with
      | _ p =>
        refine ⟨p, ?_⟩
        rw [← puncturedLocalCuspQuotientMap_additiveCover W p]
        apply congrArg (puncturedLocalCuspQuotientMap W)
        change Quotient.mk _ (e (Quotient.mk _ p)) = Quotient.mk _ u
        rw [hv]

private theorem additiveCuspCoverToFilling_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set.range (additiveCuspCoverToFilling W) = actualLocalCuspFillingCollar W := by
  rw [actualLocalCuspFillingCollar]
  apply Set.Subset.antisymm
  · rintro y ⟨p, rfl⟩
    exact ⟨additiveCuspCoverToPuncturedQuotient W p,
      (puncturedLocalCuspToFilling_additiveCover W p).symm⟩
  · rintro y ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | _ u =>
      let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      obtain ⟨v, hv⟩ := e.surjective u
      induction v using Quotient.inductionOn with
      | _ p =>
        refine ⟨p, ?_⟩
        rw [← puncturedLocalCuspToFilling_additiveCover W p]
        apply congrArg (puncturedLocalCuspToFilling W)
        change Quotient.mk _ (e (Quotient.mk _ p)) = Quotient.mk _ u
        rw [hv]

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

public theorem additiveCuspCoverToGlobal_isLocalDiffeomorph
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) :
    letI := additiveCuspRadiusCoverCharts W.localWitness.radius
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (additiveCuspCoverToGlobal W) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel ∞
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a ↦ (regularPeriodSection_contMDiff A.periods hproper a ∞).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  let htotal := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper ∞
  let _ : IsManifold GlobalDeckTotalModel ∞ (RegularTotalSpace A.periods) := htotal.1
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  let _ := A.centralFamilyProductCharts
  let hcentral :=
    (fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.modular.modularParameter A.periods)
  let _ : IsManifold GlobalDeckTotalModel ∞ A.CentralFamily := by
    simpa [PaperAnalyticData.centralFamilyProductCharts, RegularSmoothnessOrder] using hcentral.1
  let hb := additiveCuspBundleMap_isLocalDiffeomorph W
  let q₁ : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace → RegularTotalSpace A.periods :=
    projection (regularParameterMap A.periods)
  let q₂ : RegularTotalSpace A.periods → A.CentralFamily := quotientProjection
  have hproduct : IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      GlobalDeckTotalModel ∞ (additiveCuspCoverToGlobal W) := by
    intro p
    have h₁ : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ AdditiveCuspCover)
        GlobalDeckTotalModel ∞ (q₁ ∘ fun x ↦ (additiveCuspBundleHomeomorph W x).1) p :=
      IsLocalDiffeomorphAt.comp GlobalDeckTotalModel (RegularTotalSpace A.periods)
        (hb p) (htotal.2 ((additiveCuspBundleHomeomorph W p).1))
    have h₂ : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ AdditiveCuspCover)
        GlobalDeckTotalModel ∞
        (q₂ ∘ q₁ ∘ fun x ↦ (additiveCuspBundleHomeomorph W x).1) p :=
      IsLocalDiffeomorphAt.comp GlobalDeckTotalModel A.CentralFamily h₁ (by
        simpa [q₂, PaperAnalyticData.centralFamilyProductCharts, RegularSmoothnessOrder] using
          hcentral.2 (q₁ ((additiveCuspBundleHomeomorph W p).1)))
    convert h₂ using 1
    funext x
    exact additiveCuspCoverToGlobal_eq_quotientProjections W x
  let cProduct : ChartedSpace (ℂ × ComplexTwoSpace) A.CentralFamily :=
    A.centralFamilyProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) A.CentralFamily := cProduct
  have hproductManifold : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞
      A.CentralFamily := by
    simpa only [GlobalDeckTotalModel, GlobalDeckBaseModel, GlobalDeckFiberModel,
      modelWithCornersSelf_prod] using hcentral.1
  let _ : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞
      A.CentralFamily := hproductManifold
  let cComplex : ChartedSpace ComplexModel A.CentralFamily :=
    linearRechart globalDeckComplexModelEquiv
  let _ : ChartedSpace ComplexModel A.CentralFamily := cComplex
  let d := linearRechartDiffeomorph (n := ∞) (M := A.CentralFamily)
    globalDeckComplexModelEquiv
  intro p
  have hp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞
      (additiveCuspCoverToGlobal W) p := by
    simpa only [GlobalDeckTotalModel, GlobalDeckBaseModel, GlobalDeckFiberModel,
      modelWithCornersSelf_prod] using hproduct p
  have h := IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ComplexModel)
    A.CentralFamily hp (d.isLocalDiffeomorph (additiveCuspCoverToGlobal W p))
  convert h using 1
  · change A.centralFamilyComplexCharts = cComplex
    unfold PaperAnalyticData.centralFamilyComplexCharts globalDeckComplexCharts
    rfl
  · funext x
    rfl

/-- The actual cusp correspondence as an ambient complex partial diffeomorphism. -/
public noncomputable def actualPuncturedCuspCollarPartialDiffeomorph
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) :
    letI := A.centralFamilyComplexCharts
    letI := actualLocalCuspFillingCharts W
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (actualLocalCuspFilling W) ∞ := by
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := A.centralFamilyComplexCharts
  let _ := actualLocalCuspFillingCharts W
  let e := actualPuncturedCuspCollarOpenPartialHomeomorph W
  have hp := additiveCuspCoverToGlobal_isLocalDiffeomorph A W
  have hq := additiveCuspCoverToFilling_isLocalDiffeomorph W
  apply partialDiffeomorphOfLocalCovers e hp hq
  · intro p
    rw [← puncturedLocalCuspQuotientMap_additiveCover W p,
      ← puncturedLocalCuspToFilling_additiveCover W p]
    exact actualPuncturedCuspCollarOpenPartialHomeomorph_apply W
      (additiveCuspCoverToPuncturedQuotient W p)
  · intro p
    rw [actualPuncturedCuspCollarOpenPartialHomeomorph_source,
      ← additiveCuspCoverToGlobal_range W]
    exact ⟨p, rfl⟩
  · rw [actualPuncturedCuspCollarOpenPartialHomeomorph_source,
      ← additiveCuspCoverToGlobal_range W]
  · rw [actualPuncturedCuspCollarOpenPartialHomeomorph_target,
      ← additiveCuspCoverToFilling_range W]

public theorem actualPuncturedCuspCollarPartialDiffeomorph_source
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) :
    letI := A.centralFamilyComplexCharts
    letI := actualLocalCuspFillingCharts W
    (actualPuncturedCuspCollarPartialDiffeomorph A W).source =
      puncturedGlobalCuspCollar W := by
  let _ := A.centralFamilyComplexCharts
  let _ := actualLocalCuspFillingCharts W
  change (actualPuncturedCuspCollarOpenPartialHomeomorph W).source = _
  exact actualPuncturedCuspCollarOpenPartialHomeomorph_source W

public theorem actualPuncturedCuspCollarPartialDiffeomorph_target
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel) :
    letI := A.centralFamilyComplexCharts
    letI := actualLocalCuspFillingCharts W
    (actualPuncturedCuspCollarPartialDiffeomorph A W).target =
      actualLocalCuspFillingCollar W := by
  let _ := A.centralFamilyComplexCharts
  let _ := actualLocalCuspFillingCharts W
  change (actualPuncturedCuspCollarOpenPartialHomeomorph W).target = _
  exact actualPuncturedCuspCollarOpenPartialHomeomorph_target W

public theorem actualPuncturedCuspCollarPartialDiffeomorph_apply
    (W : ActualPuncturedCuspCollarWitness A.cuspCoordinate A.toricModel)
    (q : puncturedLocalCuspQuotient W) :
    letI := A.centralFamilyComplexCharts
    letI := actualLocalCuspFillingCharts W
    actualPuncturedCuspCollarPartialDiffeomorph A W
        (puncturedLocalCuspQuotientMap W q) =
      puncturedLocalCuspToFilling W q := by
  let _ := A.centralFamilyComplexCharts
  let _ := actualLocalCuspFillingCharts W
  change actualPuncturedCuspCollarOpenPartialHomeomorph W
      (puncturedLocalCuspQuotientMap W q) = _
  exact actualPuncturedCuspCollarOpenPartialHomeomorph_apply W q

end PaperAnalyticData

end

end SphereSixComplex.Geometry.CuspAnalyticFillingCollar
