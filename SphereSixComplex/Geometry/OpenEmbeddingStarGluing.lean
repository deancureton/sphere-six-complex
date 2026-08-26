module

public import SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Four-piece stars from common collar sources

The analytic construction naturally supplies each attaching collar as one space with open
embeddings into the central family and the corresponding filling.  This module converts those
maps into the open-subspace homeomorphisms required by `FourPieceStarGluingData`.
-/

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- Inclusion of a nonempty open complex submanifold into its ambient manifold, packaged as a
partial diffeomorphism.  Its source is the whole open subtype and its target is the corresponding
open subset of the ambient manifold. -/
public noncomputable def openSubtypePartialDiffeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ComplexModel M]
    (V : TopologicalSpace.Opens M) [Nonempty V] :
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) V M ∞ := by
  let e := V.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty V)
  exact
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff V _ e.target y).mp
        apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hy
        intro z hz
        change e (e.symm z) = z
        exact e.right_inv hz }

/-- The inclusion of an open complex submanifold is locally biholomorphic. -/
public theorem openSubtypeVal_isLocalDiffeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ComplexModel M]
    (V : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (Subtype.val : V → M) := by
  intro x
  let _ : Nonempty V := ⟨x⟩
  let Φ := openSubtypePartialDiffeomorph V
  have hx : x ∈ Φ.source := by
    simp [Φ, openSubtypePartialDiffeomorph]
  have hΦ := Φ.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ComplexModel) (modelWithCornersSelf ℂ ComplexModel) ∞ hx
  have heq : (Φ : V → M) = Subtype.val := by
    funext y
    rfl
  rwa [heq] at hΦ

/-- Local biholomorphicity at a point is unchanged when two maps agree near that point. -/
public theorem isLocalDiffeomorphAt_congr_eventuallyEq
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f x)
    (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ g x := by
  rw [IsLocalDiffeomorphAt.eq_def] at hf ⊢
  obtain ⟨Φ, hx, hfΦ⟩ := hf
  obtain ⟨s, hs, hfgs⟩ := hfg.exists_mem
  obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hs
  let Ψ : PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) M N ∞ :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left }
  refine ⟨Ψ, ?_, ?_⟩
  · exact ⟨hx, hxt⟩
  · intro y hy
    change y ∈ Φ.source ∩ t at hy
    calc
      g y = f y := (hfgs (hts hy.2)).symm
      _ = Φ y := hfΦ hy.1
      _ = Ψ y := rfl

/-- An injective local biholomorphism is a diffeomorphism from its source onto its open image. -/
@[expose] public noncomputable def localDiffeomorphToOpenImage
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    {f : M → N}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f)
    (hinj : Function.Injective f) :
    M ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ hf.image := by
  let toImage : M → hf.image := fun x ↦ ⟨f x, ⟨x, rfl⟩⟩
  have htoImage : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ toImage := by
    intro x
    let y : hf.image := toImage x
    let hval := openSubtypeVal_isLocalDiffeomorph hf.image y
    let loc := hval.localInverse
    have hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞ loc (f x) := by
      change IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞ loc y.1
      exact hval.localInverse_isLocalDiffeomorphAt
    have hcomp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞ (loc ∘ f) x :=
      (hf x).comp (modelWithCornersSelf ℂ ComplexModel) hf.image hloc
    have hmem : f ⁻¹' loc.source ∈ nhds x :=
      (hf x).contMDiffAt.continuousAt
        (loc.open_source.mem_nhds hval.localInverse_mem_source)
    have hevent : (loc ∘ f) =ᶠ[nhds x] toImage := by
      filter_upwards [hmem] with z hz
      apply Subtype.ext
      exact hval.localInverse_right_inv hz
    exact isLocalDiffeomorphAt_congr_eventuallyEq hcomp hevent
  have hbij : Function.Bijective toImage := by
    constructor
    · intro x y hxy
      apply hinj
      exact congrArg Subtype.val hxy
    · intro y
      obtain ⟨x, hx⟩ := y.2
      refine ⟨x, Subtype.ext ?_⟩
      exact hx
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hbij
  exact
    { toFun := toImage
      invFun := g
      left_inv := hgInverse.1
      right_inv := hgInverse.2
      contMDiff_toFun := htoImage.contMDiff
      contMDiff_invFun := by
        intro y
        let x := g y
        have hlocal := htoImage x
        rw [IsLocalDiffeomorphAt.eq_def] at hlocal
        obtain ⟨Φ, hx, hfx⟩ := hlocal
        have haux : Set.EqOn g Φ.symm Φ.target :=
          Set.eqOn_of_leftInvOn_of_rightInvOn (fun x' _ ↦ hgInverse.1 x')
            (Set.LeftInvOn.congr_left Φ.toOpenPartialHomeomorph.rightInvOn
              Φ.toOpenPartialHomeomorph.mapsTo_symm hfx.symm)
            (fun _z hz ↦ Φ.map_target hz)
        apply (Φ.symm.contMDiffOn.congr haux).contMDiffAt (Φ.open_target.mem_nhds ?_)
        have : y = Φ x := ((hgInverse.2 y).congr (hfx hx)).mp rfl
        exact this ▸ Φ.map_source hx }

@[simp]
public theorem localDiffeomorphToOpenImage_apply
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    {f : M → N}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f)
    (hinj : Function.Injective f) (x : M) :
    localDiffeomorphToOpenImage hf hinj x = ⟨f x, ⟨x, rfl⟩⟩ := by
  rfl

/-- A global diffeomorphism, viewed as a partial diffeomorphism with universal source and
target.  This exposed wrapper makes the two domain fields reducible for exact collar-range
computations. -/
@[expose] public def diffeomorphToFullPartialDiffeomorph
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    (e : M ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ N) :
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) M N ∞ where
  toPartialEquiv := e.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := e.contMDiff_toFun x
  contMDiffOn_invFun _ _ := e.symm.contMDiffWithinAt

/-- A diffeomorphism between two nonempty open subtypes determines an ambient partial
diffeomorphism with those opens as its source and target. -/
public noncomputable def openSubtypeDiffeomorphToPartial
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    [Nonempty V] [Nonempty W]
    (e : V ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ W) :
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) M N ∞ :=
  (openSubtypePartialDiffeomorph V).symm.trans
    ((diffeomorphToFullPartialDiffeomorph e).trans (openSubtypePartialDiffeomorph W))

@[simp]
public theorem openSubtypeDiffeomorphToPartial_source
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    [Nonempty V] [Nonempty W]
    (e : V ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ W) :
    (openSubtypeDiffeomorphToPartial V W e).source = V := by
  simp [openSubtypeDiffeomorphToPartial, openSubtypePartialDiffeomorph]
  intro x hx
  trivial

@[simp]
public theorem openSubtypeDiffeomorphToPartial_target
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    [Nonempty V] [Nonempty W]
    (e : V ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ W) :
    (openSubtypeDiffeomorphToPartial V W e).target = W := by
  simp [openSubtypeDiffeomorphToPartial, openSubtypePartialDiffeomorph]
  intro x hx
  trivial

@[simp]
public theorem openSubtypeDiffeomorphToPartial_apply
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ComplexModel M] [ChartedSpace ComplexModel N]
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    [Nonempty V] [Nonempty W]
    (e : V ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ W) (x : V) :
    openSubtypeDiffeomorphToPartial V W e x.1 = (e x).1 := by
  simp [openSubtypeDiffeomorphToPartial, openSubtypePartialDiffeomorph,
    diffeomorphToFullPartialDiffeomorph]
  rw [show x.1 = (V.openPartialHomeomorphSubtypeCoe
      (inferInstance : Nonempty V)) x from rfl]
  rw [(V.openPartialHomeomorphSubtypeCoe
    (inferInstance : Nonempty V)).left_inv]
  trivial

/-- Three common collar sources, each openly embedded in the central piece and one filling. -/
public structure OpenEmbeddingStarData where
  central : TopCat
  filling : Fin 3 → TopCat
  collarSource : Fin 3 → TopCat
  toCentral : ∀ i, collarSource i ⟶ central
  toFilling : ∀ i, collarSource i ⟶ filling i
  toCentral_isOpenEmbedding : ∀ i, IsOpenEmbedding (toCentral i)
  toFilling_isOpenEmbedding : ∀ i, IsOpenEmbedding (toFilling i)
  centralRange_disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (toCentral i)) (Set.range (toCentral j))

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- The image of the `i`th common collar source in the central piece. -/
@[expose] public def centralCollar (i : Fin 3) : Opens A.central :=
  ⟨Set.range (A.toCentral i), (A.toCentral_isOpenEmbedding i).isOpen_range⟩

/-- The image of the `i`th common collar source in its filling piece. -/
@[expose] public def fillingCollar (i : Fin 3) : Opens (A.filling i) :=
  ⟨Set.range (A.toFilling i), (A.toFilling_isOpenEmbedding i).isOpen_range⟩

/-- Two injective common-source local biholomorphisms determine the corresponding ambient
partial diffeomorphism between their open images. -/
public noncomputable def collarPartialDiffeomorphOfLocalDiffeomorph
    (i : Fin 3)
    [ChartedSpace ComplexModel (A.collarSource i)]
    [ChartedSpace ComplexModel A.central]
    [ChartedSpace ComplexModel (A.filling i)]
    [Nonempty (A.collarSource i)]
    (hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toCentral i))
    (hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toFilling i)) :
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.central (A.filling i) ∞ := by
  let x := Classical.arbitrary (A.collarSource i)
  let _ : Nonempty (A.centralCollar i) :=
    ⟨⟨A.toCentral i x, ⟨x, rfl⟩⟩⟩
  let _ : Nonempty (A.fillingCollar i) :=
    ⟨⟨A.toFilling i x, ⟨x, rfl⟩⟩⟩
  let ecentral : A.collarSource i ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ A.centralCollar i :=
    localDiffeomorphToOpenImage hcentral (A.toCentral_isOpenEmbedding i).injective
  let efilling : A.collarSource i ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ A.fillingCollar i :=
    localDiffeomorphToOpenImage hfilling (A.toFilling_isOpenEmbedding i).injective
  exact openSubtypeDiffeomorphToPartial (A.centralCollar i) (A.fillingCollar i)
    (ecentral.symm.trans efilling)

@[simp]
public theorem collarPartialDiffeomorphOfLocalDiffeomorph_source
    (i : Fin 3)
    [ChartedSpace ComplexModel (A.collarSource i)]
    [ChartedSpace ComplexModel A.central]
    [ChartedSpace ComplexModel (A.filling i)]
    [Nonempty (A.collarSource i)]
    (hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toCentral i))
    (hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toFilling i)) :
    (A.collarPartialDiffeomorphOfLocalDiffeomorph i hcentral hfilling).source =
      A.centralCollar i := by
  simp [collarPartialDiffeomorphOfLocalDiffeomorph]

@[simp]
public theorem collarPartialDiffeomorphOfLocalDiffeomorph_target
    (i : Fin 3)
    [ChartedSpace ComplexModel (A.collarSource i)]
    [ChartedSpace ComplexModel A.central]
    [ChartedSpace ComplexModel (A.filling i)]
    [Nonempty (A.collarSource i)]
    (hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toCentral i))
    (hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toFilling i)) :
    (A.collarPartialDiffeomorphOfLocalDiffeomorph i hcentral hfilling).target =
      A.fillingCollar i := by
  simp [collarPartialDiffeomorphOfLocalDiffeomorph]

@[simp]
public theorem collarPartialDiffeomorphOfLocalDiffeomorph_toCentral
    (i : Fin 3)
    [ChartedSpace ComplexModel (A.collarSource i)]
    [ChartedSpace ComplexModel A.central]
    [ChartedSpace ComplexModel (A.filling i)]
    [Nonempty (A.collarSource i)]
    (hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toCentral i))
    (hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.toFilling i))
    (x : A.collarSource i) :
    A.collarPartialDiffeomorphOfLocalDiffeomorph i hcentral hfilling
        (A.toCentral i x) = A.toFilling i x := by
  let x₀ := Classical.arbitrary (A.collarSource i)
  let _ : Nonempty (A.centralCollar i) :=
    ⟨⟨A.toCentral i x₀, ⟨x₀, rfl⟩⟩⟩
  let _ : Nonempty (A.fillingCollar i) :=
    ⟨⟨A.toFilling i x₀, ⟨x₀, rfl⟩⟩⟩
  let ecentral : A.collarSource i ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ A.centralCollar i :=
    localDiffeomorphToOpenImage hcentral (A.toCentral_isOpenEmbedding i).injective
  let efilling : A.collarSource i ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ A.fillingCollar i :=
    localDiffeomorphToOpenImage hfilling (A.toFilling_isOpenEmbedding i).injective
  have hcentralVal : (ecentral x).1 = A.toCentral i x := by
    change ((localDiffeomorphToOpenImage hcentral
      (A.toCentral_isOpenEmbedding i).injective) x).1 = A.toCentral i x
    exact congrArg Subtype.val (localDiffeomorphToOpenImage_apply hcentral
      (A.toCentral_isOpenEmbedding i).injective x)
  have hfillingVal : (efilling x).1 = A.toFilling i x := by
    change ((localDiffeomorphToOpenImage hfilling
      (A.toFilling_isOpenEmbedding i).injective) x).1 = A.toFilling i x
    exact congrArg Subtype.val (localDiffeomorphToOpenImage_apply hfilling
      (A.toFilling_isOpenEmbedding i).injective x)
  change openSubtypeDiffeomorphToPartial (A.centralCollar i) (A.fillingCollar i)
    (ecentral.symm.trans efilling) (A.toCentral i x) = A.toFilling i x
  rw [← hcentralVal, openSubtypeDiffeomorphToPartial_apply]
  simp only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply]
  exact hfillingVal

/-- A point of a common collar source, viewed in its central image. -/
@[expose] public def centralCollarPoint (i : Fin 3) (x : A.collarSource i) : A.centralCollar i :=
  ⟨A.toCentral i x, by
    change ∃ y, A.toCentral i y = A.toCentral i x
    exact ⟨x, rfl⟩⟩

/-- A point of a common collar source, viewed in its filling image. -/
@[expose] public def fillingCollarPoint (i : Fin 3) (x : A.collarSource i) : A.fillingCollar i :=
  ⟨A.toFilling i x, by
    change ∃ y, A.toFilling i y = A.toFilling i x
    exact ⟨x, rfl⟩⟩

/-- The central collar image, identified with its common source. -/
public noncomputable def toCentralCollarHomeomorph (i : Fin 3) :
    A.collarSource i ≃ₜ A.centralCollar i := by
  change A.collarSource i ≃ₜ Set.range (A.toCentral i)
  exact (A.toCentral_isOpenEmbedding i).isEmbedding.toHomeomorph

/-- The filling collar image, identified with its common source. -/
public noncomputable def toFillingCollarHomeomorph (i : Fin 3) :
    A.collarSource i ≃ₜ A.fillingCollar i := by
  change A.collarSource i ≃ₜ Set.range (A.toFilling i)
  exact (A.toFilling_isOpenEmbedding i).isEmbedding.toHomeomorph

@[simp]
public theorem toCentralCollarHomeomorph_apply (i : Fin 3) (x : A.collarSource i) :
    A.toCentralCollarHomeomorph i x = A.centralCollarPoint i x := by
  apply Subtype.ext
  change ↑((A.toCentral_isOpenEmbedding i).isEmbedding.toHomeomorph x) = A.toCentral i x
  exact Topology.IsEmbedding.toHomeomorph_apply_coe
    (A.toCentral_isOpenEmbedding i).isEmbedding x

@[simp]
public theorem toFillingCollarHomeomorph_apply (i : Fin 3) (x : A.collarSource i) :
    A.toFillingCollarHomeomorph i x = A.fillingCollarPoint i x := by
  apply Subtype.ext
  change ↑((A.toFilling_isOpenEmbedding i).isEmbedding.toHomeomorph x) = A.toFilling i x
  exact Topology.IsEmbedding.toHomeomorph_apply_coe
    (A.toFilling_isOpenEmbedding i).isEmbedding x

/-- The collar homeomorphism obtained by identifying both images with their common source. -/
@[expose] public noncomputable def collarEquiv (i : Fin 3) :
    A.centralCollar i ≃ₜ A.fillingCollar i :=
  (A.toCentralCollarHomeomorph i).symm.trans (A.toFillingCollarHomeomorph i)

/-- Common-source open embeddings canonically determine a four-piece star gluing. -/
@[expose] public noncomputable def toFourPieceStarGluingData : FourPieceStarGluingData where
  central := A.central
  filling := A.filling
  centralCollar := A.centralCollar
  fillingCollar := A.fillingCollar
  collarEquiv := A.collarEquiv
  centralCollar_disjoint := by
    intro i j hij
    exact Opens.coe_disjoint.mp (A.centralRange_disjoint hij)

/-- A nonempty common collar source has nonempty images in both pieces. -/
public theorem centralCollar_nonempty (i : Fin 3) [Nonempty (A.collarSource i)] :
    Nonempty (A.centralCollar i) :=
  ⟨A.centralCollarPoint i (Classical.arbitrary (A.collarSource i))⟩

/-- A nonempty common collar source has a nonempty filling image. -/
public theorem fillingCollar_nonempty (i : Fin 3) [Nonempty (A.collarSource i)] :
    Nonempty (A.fillingCollar i) :=
  ⟨A.fillingCollarPoint i (Classical.arbitrary (A.collarSource i))⟩

/-- Nonempty common sources supply the nonempty-collar field used by `PaperGluingData`. -/
public theorem toFourPieceStarGluingData_nonemptyCentralCollar
    [∀ i, Nonempty (A.collarSource i)] :
    ∀ i, Nonempty (A.toFourPieceStarGluingData.centralCollar i) :=
  fun i ↦ by
    change Nonempty (A.centralCollar i)
    exact A.centralCollar_nonempty i

@[simp]
public theorem collarEquiv_toCentral (i : Fin 3) (x : A.collarSource i) :
    A.collarEquiv i (A.centralCollarPoint i x) = A.fillingCollarPoint i x := by
  change A.toFillingCollarHomeomorph i
      ((A.toCentralCollarHomeomorph i).symm (A.centralCollarPoint i x)) = _
  have hx : (A.toCentralCollarHomeomorph i).symm (A.centralCollarPoint i x) = x := by
    rw [← A.toCentralCollarHomeomorph_apply i x]
    exact (A.toCentralCollarHomeomorph i).symm_apply_apply x
  rw [hx]
  exact A.toFillingCollarHomeomorph_apply i x

@[simp]
public theorem collarEquiv_symm_toFilling (i : Fin 3) (x : A.collarSource i) :
    (A.collarEquiv i).symm (A.fillingCollarPoint i x) = A.centralCollarPoint i x := by
  change A.toCentralCollarHomeomorph i
      ((A.toFillingCollarHomeomorph i).symm (A.fillingCollarPoint i x)) = _
  have hx : (A.toFillingCollarHomeomorph i).symm (A.fillingCollarPoint i x) = x := by
    rw [← A.toFillingCollarHomeomorph_apply i x]
    exact (A.toFillingCollarHomeomorph i).symm_apply_apply x
  rw [hx]
  exact A.toCentralCollarHomeomorph_apply i x

/-- The ambient collar graph of the induced four-piece star is the paired range of the two
common-source embeddings. -/
public theorem collarPairRange_toFourPieceStarGluingData (i : Fin 3) :
    A.toFourPieceStarGluingData.collarPairRange i =
      Set.range (fun x : A.collarSource i => (A.toCentral i x, A.toFilling i x)) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    let x := (A.toCentralCollarHomeomorph i).symm z
    refine ⟨x, ?_⟩
    apply Prod.ext
    · have hx := congrArg Subtype.val
        ((A.toCentralCollarHomeomorph i).apply_symm_apply z)
      rw [A.toCentralCollarHomeomorph_apply] at hx
      exact hx
    · have hx : (A.collarEquiv i z).1 = A.toFilling i x := by
        change (A.toFillingCollarHomeomorph i
          ((A.toCentralCollarHomeomorph i).symm z)).1 = A.toFilling i x
        rw [A.toFillingCollarHomeomorph_apply]
        rfl
      exact hx.symm
  · rintro ⟨x, rfl⟩
    refine ⟨A.centralCollarPoint i x, ?_⟩
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val (A.collarEquiv_toCentral i x)

/-- The two images of a common collar-source point define the same point of the induced glued
space. -/
public theorem toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
    (i : Fin 3) (x : A.collarSource i) :
    A.toFourPieceStarGluingData.glueData.toGlueData.ι none (A.toCentral i x) =
      A.toFourPieceStarGluingData.glueData.toGlueData.ι (some i) (A.toFilling i x) := by
  apply (A.toFourPieceStarGluingData.ι_none_eq_ι_some_iff_mem_collarPairRange
    i (A.toCentral i x) (A.toFilling i x)).2
  rw [A.collarPairRange_toFourPieceStarGluingData]
  exact ⟨x, rfl⟩

/-- Complex atlases and common-source partial diffeomorphisms refining an open-embedding star. -/
public structure BiholomorphicData where
  centralCharts : ChartedSpace ComplexModel A.central
  fillingCharts : ∀ i, ChartedSpace ComplexModel (A.filling i)
  centralManifold :
    letI := centralCharts
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ A.central
  fillingManifold :
    letI (i : Fin 3) := fillingCharts i
    ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (A.filling i)
  collar :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.central (A.filling i) ∞
  collar_source :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, (collar i).source = A.centralCollar i
  collar_target :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, (collar i).target = A.fillingCollar i
  collar_toCentral :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i (x : A.collarSource i), collar i (A.toCentral i x) = A.toFilling i x

namespace BiholomorphicData

variable (B : A.BiholomorphicData)

/-- Common-source biholomorphic collars supply the analytic data for the canonical star gluing. -/
public noncomputable def toBiholomorphicFourPieceStarData :
    Geometry.EstablishedBiholomorphicStarGluing.BiholomorphicFourPieceStarData
      A.toFourPieceStarGluingData where
  centralCharts := B.centralCharts
  fillingCharts := B.fillingCharts
  centralManifold := B.centralManifold
  fillingManifold := B.fillingManifold
  collar := B.collar
  collar_source := B.collar_source
  collar_target := B.collar_target
  collar_apply := by
    intro i x
    rcases x with ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hx
    rw [B.collar_toCentral]
    exact congrArg Subtype.val (A.collarEquiv_toCentral i y).symm

end BiholomorphicData

end OpenEmbeddingStarData

end

end SphereSixComplex
