module

public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import all SphereSixComplex.Geometry.PaperAnalyticFillingPieces
import all SphereSixComplex.Geometry.RegularBaseTopology
import all SphereSixComplex.Geometry.RegularTorusFamily

/-!
# Analytic elliptic filling collars
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open Set Topology

noncomputable section

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
variable [ChartedSpace H M] [ChartedSpace H N] [ChartedSpace H P]
variable {n : WithTop ℕ∞}

/-- A local diffeomorphism can be cancelled on the right through a surjective local
diffeomorphism. -/
private theorem isLocalDiffeomorph_of_comp_surjective
    {p : M → N} {f : N → P}
    (hp : IsLocalDiffeomorph I I n p) (hsurj : Function.Surjective p)
    (hcomp : IsLocalDiffeomorph I I n (f ∘ p)) :
    IsLocalDiffeomorph I I n f := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  let L := (hp x).localInverse
  let K := (hcomp x).localInverse
  refine ⟨L.trans K.symm, ?_, ?_⟩
  · constructor
    · exact (hp x).localInverse_mem_source
    · change L (p x) ∈ K.target
      rw [(hp x).localInverse_left_inv (hp x).localInverse_mem_target]
      exact (hcomp x).localInverse_mem_target
  · intro y hy
    change y ∈ L.source ∧ L y ∈ K.symm.source at hy
    change f y = K.symm (L y)
    have hz := (hcomp x).localInverse_right_inv (K.symm.map_source hy.2)
    change (f ∘ p) (K (K.symm (L y))) = K.symm (L y) at hz
    calc
      f y = f (p (L y)) := congrArg f ((hp x).localInverse_right_inv hy.1).symm
      _ = (f ∘ p) (K (K.symm (L y))) :=
        congrArg (f ∘ p) (K.right_inv hy.2).symm
      _ = K.symm (L y) := hz

private noncomputable def opensInclusionPartialDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {U V : TopologicalSpace.Opens X} (h : U ≤ V) [Nonempty U] :
    PartialDiffeomorph I I U V ∞ := by
  let f : U → V := TopologicalSpace.Opens.inclusion h
  let hopen : IsOpenEmbedding f := Topology.IsOpenEmbedding.inclusion h
    (U.2.preimage continuous_subtype_val)
  exact {
    toPartialEquiv := (hopen.toOpenPartialHomeomorph f).toPartialEquiv
    open_source := isOpen_univ
    open_target := by
      rw [hopen.toOpenPartialHomeomorph_target]
      exact hopen.isOpen_range
    contMDiffOn_toFun := (contMDiff_inclusion h).contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ y).mp
      apply contMDiff_subtype_val.contMDiffAt.contMDiffWithinAt.congr
      · intro z hz
        change ((hopen.toOpenPartialHomeomorph f).symm z : X) = z
        exact congrArg Subtype.val
          (IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
            (by rwa [hopen.toOpenPartialHomeomorph_target] at hz))
      · change ((hopen.toOpenPartialHomeomorph f).symm y : X) = y
        exact congrArg Subtype.val
          (IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
            (by rwa [hopen.toOpenPartialHomeomorph_target] at hy))
  }

private theorem opensInclusion_isLocalDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {U V : TopologicalSpace.Opens X} (h : U ≤ V) :
    IsLocalDiffeomorph I I ∞ (TopologicalSpace.Opens.inclusion h) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  exact (opensInclusionPartialDiffeomorph (I := I) h).isLocalDiffeomorphAt
    I I ∞ (by simp [opensInclusionPartialDiffeomorph])

private noncomputable def openSubtypeValPartialDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (U : TopologicalSpace.Opens X) [Nonempty U] :
    PartialDiffeomorph I I U X ∞ := by
  let f : U → X := Subtype.val
  let hopen : IsOpenEmbedding f := U.2.isOpenEmbedding_subtypeVal
  exact {
    toPartialEquiv := (hopen.toOpenPartialHomeomorph f).toPartialEquiv
    open_source := isOpen_univ
    open_target := by
      rw [hopen.toOpenPartialHomeomorph_target]
      change IsOpen (Set.range (Subtype.val : U → X))
      rw [Subtype.range_val]
      exact U.2
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ y).mp
      apply contMDiffAt_id.contMDiffWithinAt.congr
      · intro z hz
        exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
          (by rwa [hopen.toOpenPartialHomeomorph_target] at hz)
      · exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
          (by rwa [hopen.toOpenPartialHomeomorph_target] at hy)
  }

private theorem openSubtypeVal_isLocalDiffeomorph
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (U : TopologicalSpace.Opens X) :
    IsLocalDiffeomorph I I ∞ (Subtype.val : U → X) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  exact (openSubtypeValPartialDiffeomorph (I := I) U).isLocalDiffeomorphAt
    I I ∞ (by simp [openSubtypeValPartialDiffeomorph])

private def partialDiffeomorphProd
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' N' : Type*} [TopologicalSpace M'] [TopologicalSpace N']
    [ChartedSpace H' M'] [ChartedSpace H' N']
    (Phi : PartialDiffeomorph I I M N n)
    (Psi : PartialDiffeomorph I' I' M' N' n) :
    PartialDiffeomorph (I.prod I') (I.prod I') (M × M') (N × N') n where
  toPartialEquiv := Phi.toPartialEquiv.prod Psi.toPartialEquiv
  open_source := Phi.open_source.prod Psi.open_source
  open_target := Phi.open_target.prod Psi.open_target
  contMDiffOn_toFun := Phi.contMDiffOn_toFun.prodMap Psi.contMDiffOn_toFun
  contMDiffOn_invFun := Phi.contMDiffOn_invFun.prodMap Psi.contMDiffOn_invFun

private theorem isLocalDiffeomorph_prodMap
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' N' : Type*} [TopologicalSpace M'] [TopologicalSpace N']
    [ChartedSpace H' M'] [ChartedSpace H' N']
    {f : M → N} {g : M' → N'}
    (hf : IsLocalDiffeomorph I I n f) (hg : IsLocalDiffeomorph I' I' n g) :
    IsLocalDiffeomorph (I.prod I') (I.prod I') n (Prod.map f g) := by
  intro x
  obtain ⟨Phi, hx, hPhi⟩ := hf x.1
  obtain ⟨Psi, hy, hPsi⟩ := hg x.2
  refine ⟨partialDiffeomorphProd Phi Psi, ⟨hx, hy⟩, ?_⟩
  intro y hy
  exact Prod.ext (hPhi hy.1) (hPsi hy.2)

private theorem isLocalDiffeomorph_of_comp_left
    {f : M → N} {g : N → P}
    (hg : IsLocalDiffeomorph I I n g) (hginj : Function.Injective g)
    (hcomp : IsLocalDiffeomorph I I n (g ∘ f)) :
    IsLocalDiffeomorph I I n f := by
  intro x
  obtain ⟨Phi, hx, hPhi⟩ := hcomp x
  let L := (hg (f x)).localInverse
  refine ⟨Phi.trans L, ?_, ?_⟩
  · change x ∈ Phi.source ∧ Phi x ∈ L.source
    refine ⟨hx, ?_⟩
    rw [← hPhi hx]
    exact (hg (f x)).localInverse_mem_source
  · intro y hy
    change y ∈ Phi.source ∧ Phi y ∈ L.source at hy
    change f y = L (Phi y)
    apply hginj
    rw [(hg (f x)).localInverse_right_inv hy.2]
    exact hPhi hy.1

@[expose] public section

/-- An injective local diffeomorphism, viewed on its open range, is a partial
diffeomorphism. -/
public noncomputable def partialDiffeomorphOfOpenEmbedding
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) :
    PartialDiffeomorph I I M N n where
  toPartialEquiv := (hopen.toOpenPartialHomeomorph f).toPartialEquiv
  open_source := isOpen_univ
  open_target := by
    rw [hopen.toOpenPartialHomeomorph_target]
    exact hopen.isOpen_range
  contMDiffOn_toFun := hlocal.contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    intro y hy
    rw [hopen.toOpenPartialHomeomorph_target] at hy
    obtain ⟨x, rfl⟩ := hy
    let L := (hlocal x).localInverse
    have hevent : (hopen.toOpenPartialHomeomorph f).symm =ᶠ[nhds (f x)] L := by
      filter_upwards [L.open_source.mem_nhds
        (hlocal x).localInverse_mem_source] with y hy
      apply hopen.injective
      calc
        f ((hopen.toOpenPartialHomeomorph f).symm y) = y :=
          IsOpenEmbedding.toOpenPartialHomeomorph_right_inv f hopen
            ⟨L y, (hlocal x).localInverse_right_inv hy⟩
        _ = f (L y) := ((hlocal x).localInverse_right_inv hy).symm
    exact (hlocal x).localInverse_contMDiffAt.congr_of_eventuallyEq hevent
      |>.contMDiffWithinAt

@[simp]
public theorem partialDiffeomorphOfOpenEmbedding_source
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) :
    (partialDiffeomorphOfOpenEmbedding hopen hlocal).source = univ :=
  rfl

@[simp]
public theorem partialDiffeomorphOfOpenEmbedding_target
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) :
    (partialDiffeomorphOfOpenEmbedding hopen hlocal).target = range f := by
  exact hopen.toOpenPartialHomeomorph_target

@[simp]
public theorem partialDiffeomorphOfOpenEmbedding_apply
    {f : M → N} [Nonempty M]
    (hopen : IsOpenEmbedding f) (hlocal : IsLocalDiffeomorph I I n f) (x : M) :
    partialDiffeomorphOfOpenEmbedding hopen hlocal x = f x :=
  rfl

/-- Two analytic open embeddings of the same nonempty manifold determine the ambient
partial diffeomorphism between their ranges. -/
public noncomputable def partialDiffeomorphBetweenOpenEmbeddings
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) :
    PartialDiffeomorph I I N P n :=
  (partialDiffeomorphOfOpenEmbedding hfopen hflocal).symm.trans
    (partialDiffeomorphOfOpenEmbedding hgopen hglocal)

@[simp]
public theorem partialDiffeomorphBetweenOpenEmbeddings_source
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) :
    (partialDiffeomorphBetweenOpenEmbeddings hfopen hflocal hgopen hglocal).source =
      range f := by
  simp [partialDiffeomorphBetweenOpenEmbeddings]

@[simp]
public theorem partialDiffeomorphBetweenOpenEmbeddings_target
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) :
    (partialDiffeomorphBetweenOpenEmbeddings hfopen hflocal hgopen hglocal).target =
      range g := by
  simp [partialDiffeomorphBetweenOpenEmbeddings]

@[simp]
public theorem partialDiffeomorphBetweenOpenEmbeddings_apply
    {f : M → N} {g : M → P} [Nonempty M]
    (hfopen : IsOpenEmbedding f) (hflocal : IsLocalDiffeomorph I I n f)
    (hgopen : IsOpenEmbedding g) (hglocal : IsLocalDiffeomorph I I n g) (x : M) :
    partialDiffeomorphBetweenOpenEmbeddings hfopen hflocal hgopen hglocal (f x) =
      g x := by
  change g ((partialDiffeomorphOfOpenEmbedding hfopen hflocal).symm (f x)) = g x
  congr 1
  exact (partialDiffeomorphOfOpenEmbedding hfopen hflocal).left_inv trivial

open ComplexTorus GlobalTorusFamily

private theorem isLocalDiffeomorph_globalDeckComplex
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) N]
    [IsManifold GlobalDeckTotalModel ∞ M]
    [IsManifold GlobalDeckTotalModel ∞ N]
    {f : M → N}
    (h : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞ f) :
    letI := globalDeckComplexCharts (M := M)
    letI := globalDeckComplexCharts (M := N)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f := by
  let cMProduct : ChartedSpace (ℂ × ComplexTwoSpace) M := globalDeckProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) M := cMProduct
  let mM : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ M := by
    simpa only [GlobalDeckTotalModel, GlobalDeckBaseModel, GlobalDeckFiberModel,
      modelWithCornersSelf_prod] using
      (inferInstance : IsManifold GlobalDeckTotalModel ∞ M)
  let _ : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ M := mM
  let cNProduct : ChartedSpace (ℂ × ComplexTwoSpace) N := globalDeckProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) N := cNProduct
  let mN : IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexTwoSpace)) ∞ N := by
    simpa only [GlobalDeckTotalModel, GlobalDeckBaseModel, GlobalDeckFiberModel,
      modelWithCornersSelf_prod] using
      (inferInstance : IsManifold GlobalDeckTotalModel ∞ N)
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
    simpa only [GlobalDeckTotalModel, GlobalDeckBaseModel, GlobalDeckFiberModel,
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

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

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
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (fun q : (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier =>
          restrictedActionMap (orderThreeAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r) g q) := by
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ∞
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
  change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
    (fun q : S => orderThreeAffineFamilyRepresentation A.periods g q)
  exact (orderThreeAffineFamilyRepresentation_contMDiff A.periods
    A.totalSpace_projection_isLocalDiffeomorph g).comp
      (contMDiff_subtype_val (I := GlobalDeckTotalModel))

@[instance_reducible]
public noncomputable def orderThreeAffinePuncturedQuotientCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (A.OrderThreeAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsManifold GlobalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold GlobalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold GlobalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
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
    IsManifold GlobalDeckTotalModel ∞ (A.OrderThreeAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsManifold GlobalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold GlobalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold GlobalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
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
    GlobalDeckTotalModel ∞ (A.orderThreeAffinePuncturedAction_contMDiff r)).1

private theorem orderThreeAffinePuncturedProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.totalSpaceCharts
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsManifold GlobalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold GlobalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold GlobalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
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
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
    (quotientProjection (M := S.carrier) (G := FiniteCyclic 3))
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel ∞ (A.orderThreeAffinePuncturedAction_contMDiff r)).2

private theorem orderThreeFillingProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    letI := A.orderThreeFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (quotientProjection (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel ∞ (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingSource_isManifold r
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
    GlobalDeckTotalModel ∞ (A.orderThreeFillingRestrictedAction_contMDiff r)).2

public theorem orderThreePuncturedCollarToFilling_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    letI := A.orderThreeFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
  let hinc := opensInclusion_isLocalDiffeomorph (I := GlobalDeckTotalModel)
    hUV
  have hcomp : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      ((quotientProjection (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)) ∘
        A.orderThreePuncturedSourceToFillingSource r) := by
    intro q
    exact (hinc q).comp GlobalDeckTotalModel (A.OrderThreeVaryingFilling r)
      (A.orderThreeFillingProjection_isLocalDiffeomorph r
        (TopologicalSpace.Opens.inclusion hUV q))
  convert hcomp using 1
  funext q
  exact A.orderThreePuncturedCollarToFilling_mk r q

public theorem orderFourAffinePuncturedAction_contMDiff (r : ℝ)
    (g : FiniteCyclic 4) :
    letI := A.totalSpaceCharts
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (fun q : (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier =>
          restrictedActionMap (orderFourAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r) g q) := by
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ∞
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
  change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
    (fun q : S => orderFourAffineFamilyRepresentation A.periods g q)
  exact (orderFourAffineFamilyRepresentation_contMDiff A.periods
    A.totalSpace_projection_isLocalDiffeomorph g).comp
      (contMDiff_subtype_val (I := GlobalDeckTotalModel))

@[instance_reducible]
public noncomputable def orderFourAffinePuncturedQuotientCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (A.OrderFourAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsManifold GlobalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold GlobalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold GlobalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
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
    IsManifold GlobalDeckTotalModel ∞ (A.OrderFourAffinePuncturedQuotient r) := by
  let _ := A.totalSpaceCharts
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsManifold GlobalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold GlobalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold GlobalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
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
    GlobalDeckTotalModel ∞ (A.orderFourAffinePuncturedAction_contMDiff r)).1

private theorem orderFourAffinePuncturedProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.totalSpaceCharts
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsManifold GlobalDeckTotalModel ∞ S.carrier := by
    let _ : IsManifold GlobalDeckTotalModel ∞
        (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
    let O : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
      ⟨S.carrier, S.isOpen_carrier⟩
    change IsManifold GlobalDeckTotalModel ∞ O
    infer_instance
  let _ : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
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
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
    (quotientProjection (M := S.carrier) (G := FiniteCyclic 4))
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel ∞ (A.orderFourAffinePuncturedAction_contMDiff r)).2

private theorem orderFourFillingProjection_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    letI := A.orderFourFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (quotientProjection (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel ∞ (A.orderFourFillingOpen r) :=
    A.orderFourFillingSource_isManifold r
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
    GlobalDeckTotalModel ∞ (A.orderFourFillingRestrictedAction_contMDiff r)).2

public theorem orderFourPuncturedCollarToFilling_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts r
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    letI := A.orderFourFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
  let hinc := opensInclusion_isLocalDiffeomorph (I := GlobalDeckTotalModel) hUV
  have hcomp : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      ((quotientProjection (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)) ∘
        A.orderFourPuncturedSourceToFillingSource r) := by
    intro q
    exact (hinc q).comp GlobalDeckTotalModel (A.OrderFourVaryingFilling r)
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
  let _ : IsManifold GlobalDeckBaseModel ∞
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
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
  have hbase : IsLocalDiffeomorph GlobalDeckBaseModel GlobalDeckBaseModel ∞
      (fun z : RegularBase
        (U := A.modular.modularParameter.toTriangleUniformization) => z.1) := by
    change IsLocalDiffeomorph GlobalDeckBaseModel GlobalDeckBaseModel ∞
      (Subtype.val : regularBaseOpen hproper → UpperHalfPlane)
    exact openSubtypeVal_isLocalDiffeomorph
      (I := GlobalDeckBaseModel) (regularBaseOpen hproper)
  have hfiber := (Diffeomorph.refl GlobalDeckFiberModel ComplexTwoSpace ∞).isLocalDiffeomorph
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
  let _ : IsManifold GlobalDeckBaseModel ∞
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
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
  have hcomp : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      ((projection (parameterMap A.periods)) ∘
        regularBundleInclusion
          (U := A.modular.modularParameter.toTriangleUniformization)) := by
    intro q
    exact (regularBundleInclusion_isLocalDiffeomorph (A := A) q).comp GlobalDeckTotalModel
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
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
    (I := GlobalDeckTotalModel) O
  convert hsub using 1
  · rfl
  · funext q
    exact regularFamilyInclusion_orderThreeCollarToRegular A.periods hproper D q

private theorem totalSpace_isManifold_analytic :
    letI := A.totalSpaceCharts
    IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  simpa [PaperAnalyticData.totalSpaceCharts] using
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph A.periods ω).1

private theorem totalSpaceProjection_isLocalDiffeomorph_analytic :
    letI := A.totalSpaceCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  simpa [PaperAnalyticData.totalSpaceCharts] using
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph A.periods ω).2

private theorem centralFamilyProjection_isLocalDiffeomorph :
    letI := regularFamilyDeckAction A.periods
    letI := A.regularTotalSpaceProductCharts
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel ∞
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a ∞).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
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
  let cProduct : ChartedSpace (ℂ × ComplexTwoSpace) A.CentralFamily :=
    A.centralFamilyProductCharts
  let _ : ChartedSpace (ℂ × ComplexTwoSpace) A.CentralFamily := cProduct
  simpa [PaperAnalyticData.centralFamilyProductCharts, RegularSmoothnessOrder] using
    (fuchsianPuncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.modular.modularParameter A.periods).2

public theorem orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts r
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (A.orderThreePuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts r
  let _ := A.regularTotalSpaceProductCharts
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold GlobalDeckTotalModel ω
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
  have hcomp : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      ((quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) ∘
        orderThreeCollarToRegular A.periods hproper D ∘ gauge) := by
    intro q
    exact IsLocalDiffeomorphAt.comp GlobalDeckTotalModel A.CentralFamily
      (IsLocalDiffeomorphAt.comp GlobalDeckTotalModel (RegularTotalSpace A.periods)
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
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
    (I := GlobalDeckTotalModel) O
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
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (A.orderFourPuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts r
  let _ := A.regularTotalSpaceProductCharts
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold GlobalDeckTotalModel ω
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
  have hcomp : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ∞
      ((quotientProjection : RegularTotalSpace A.periods → A.CentralFamily) ∘
        orderFourCollarToRegular A.periods hproper D ∘ gauge) := by
    intro q
    exact IsLocalDiffeomorphAt.comp GlobalDeckTotalModel A.CentralFamily
      (IsLocalDiffeomorphAt.comp GlobalDeckTotalModel (RegularTotalSpace A.periods)
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

public noncomputable def orderThreeFillingCollarPartialDiffeomorphProduct
    (P : A.OrderThreeFillingPiece) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeAffinePuncturedQuotientCharts P.radius
    letI := A.centralFamilyProductCharts
    letI := A.orderThreeFillingSourceCharts P.radius
    letI := A.orderThreeFillingAction P.radius
    letI := A.orderThreeFillingProductCharts P.radius
    PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      A.CentralFamily (A.OrderThreeVaryingFilling P.radius) ∞ := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeAffinePuncturedQuotientCharts P.radius
  let _ := A.centralFamilyProductCharts
  let _ := A.orderThreeFillingSourceCharts P.radius
  let _ := A.orderThreeFillingAction P.radius
  let _ := A.orderThreeFillingProductCharts P.radius
  let _ : Nonempty (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    A.orderThreeAffinePuncturedQuotient_nonempty P
  exact partialDiffeomorphBetweenOpenEmbeddings
    (A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding P.sourceData)
    (A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph P.sourceData)
    (A.orderThreePuncturedCollarToFilling_isOpenEmbedding P.radius)
    (A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph P.radius)

public noncomputable def orderFourFillingCollarPartialDiffeomorphProduct
    (P : A.OrderFourFillingPiece) :
    letI := A.totalSpaceCharts
    letI := A.orderFourAffinePuncturedQuotientCharts P.radius
    letI := A.centralFamilyProductCharts
    letI := A.orderFourFillingSourceCharts P.radius
    letI := A.orderFourFillingAction P.radius
    letI := A.orderFourFillingProductCharts P.radius
    PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      A.CentralFamily (A.OrderFourVaryingFilling P.radius) ∞ := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourAffinePuncturedQuotientCharts P.radius
  let _ := A.centralFamilyProductCharts
  let _ := A.orderFourFillingSourceCharts P.radius
  let _ := A.orderFourFillingAction P.radius
  let _ := A.orderFourFillingProductCharts P.radius
  let _ : Nonempty (A.OrderFourAffinePuncturedQuotient P.radius) :=
    A.orderFourAffinePuncturedQuotient_nonempty P
  exact partialDiffeomorphBetweenOpenEmbeddings
    (A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding P.sourceData)
    (A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph P.sourceData)
    (A.orderFourPuncturedCollarToFilling_isOpenEmbedding P.radius)
    (A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph P.radius)

public theorem centralFamilyProduct_isManifold :
    letI := A.centralFamilyProductCharts
    IsManifold GlobalDeckTotalModel ∞ A.CentralFamily := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel ∞
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
  simpa [PaperAnalyticData.centralFamilyProductCharts, RegularSmoothnessOrder] using
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
  let _ : IsManifold GlobalDeckTotalModel ∞
      (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    A.orderThreeAffinePuncturedQuotient_isManifold P.radius
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold GlobalDeckTotalModel ∞ A.CentralFamily :=
    A.centralFamilyProduct_isManifold
  let h := A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph P.sourceData
  let _ : ChartedSpace ComplexModel (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.centralFamilyComplexCharts
  simpa only [PaperAnalyticData.centralFamilyComplexCharts] using
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
  let _ : IsManifold GlobalDeckTotalModel ∞
      (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    A.orderThreeAffinePuncturedQuotient_isManifold P.radius
  let _ := A.orderThreeFillingSourceCharts P.radius
  let _ := A.orderThreeFillingAction P.radius
  let _ := A.orderThreeFillingProductCharts P.radius
  let _ : IsManifold GlobalDeckTotalModel ∞
      (A.OrderThreeVaryingFilling P.radius) :=
    A.orderThreeFillingProduct_isManifold P.radius
  let h := A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph P.radius
  let _ : ChartedSpace ComplexModel (A.OrderThreeAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.orderThreeFillingComplexCharts P.radius
  simpa only [PaperAnalyticData.orderThreeFillingComplexCharts] using
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
  let _ : IsManifold GlobalDeckTotalModel ∞
      (A.OrderFourAffinePuncturedQuotient P.radius) :=
    A.orderFourAffinePuncturedQuotient_isManifold P.radius
  let _ := A.centralFamilyProductCharts
  let _ : IsManifold GlobalDeckTotalModel ∞ A.CentralFamily :=
    A.centralFamilyProduct_isManifold
  let h := A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph P.sourceData
  let _ : ChartedSpace ComplexModel (A.OrderFourAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.centralFamilyComplexCharts
  simpa only [PaperAnalyticData.centralFamilyComplexCharts] using
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
  let _ : IsManifold GlobalDeckTotalModel ∞
      (A.OrderFourAffinePuncturedQuotient P.radius) :=
    A.orderFourAffinePuncturedQuotient_isManifold P.radius
  let _ := A.orderFourFillingSourceCharts P.radius
  let _ := A.orderFourFillingAction P.radius
  let _ := A.orderFourFillingProductCharts P.radius
  let _ : IsManifold GlobalDeckTotalModel ∞
      (A.OrderFourVaryingFilling P.radius) :=
    A.orderFourFillingProduct_isManifold P.radius
  let h := A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph P.radius
  let _ : ChartedSpace ComplexModel (A.OrderFourAffinePuncturedQuotient P.radius) :=
    globalDeckComplexCharts
  let _ := A.orderFourFillingComplexCharts P.radius
  simpa only [PaperAnalyticData.orderFourFillingComplexCharts] using
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

end PaperAnalyticData

end

end

end SphereSixComplex.Geometry
