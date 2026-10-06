module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallHomology
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainHomotopy
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Homology.Opposite
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallRelative
public import Mathlib.CategoryTheory.Limits.Yoneda
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeFunctoriality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalHomology
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeComparison
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Module Set

universe u v

namespace DifferentialGeometry.Topology

private theorem integralSingularSmallChains_projective
    {X : Type u} [TopologicalSpace X] {ι : Type v} (n : ℕ) (U : ι → Set X) :
    Projective (ModuleCat.of ℤ (integralSingularSmallChains n U)) := by
  classical
  let s : Set (integralSingularSimplex n X) :=
    {σ | ∃ i, Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i}
  let S := Submodule.span ℤ (Set.range (fun σ : s => integralSingularChainBasis n X σ.val))
  let : Module ℤ S := S.module
  let b : Basis s ℤ S := Basis.span ((integralSingularChainBasis n X).linearIndependent.comp
    (fun σ : s => σ.val) Subtype.val_injective)
  have hS : S = integralSingularSmallChains n U := by
    rw [integralSingularSmallChains_eq_span_basis, Set.image_eq_range]
  exact ModuleCat.projective_of_free (b.map (LinearEquiv.ofEq S _ hS))

private theorem exists_integralSingularSmallHomotopyEquiv
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ e : HomotopyEquiv (integralSingularSmallComplex U) (integralSingularChains X),
      e.hom = integralSingularSmallInclusion U := by
  let (n : ℕ) : Projective ((integralSingularSmallComplex U).X n) :=
    integralSingularSmallChains_projective n U
  exact (ChainComplex.quasiIso_iff_of_projective (integralSingularSmallInclusion U)).mp
    (integralSingularSmallInclusion_quasiIso U hU hcover)

private abbrev integralChainDual (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
    (.up ℕ)).obj K.op

private def integralChainDualMap {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) :
    integralChainDual L ⟶ integralChainDual K :=
  (((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
    (.up ℕ)).map ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).map f.op)

private def integralChainDualHomotopyEquiv
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (integralChainDual L) (integralChainDual K) where
  hom := integralChainDualMap e.hom
  inv := integralChainDualMap e.inv
  homotopyHomInvId := by
    let F := (linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
    let G := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)
    change Homotopy
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.hom.op) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.inv.op)) (𝟙 _)
    rw [← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_comp,
      ← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_id]
    apply F.mapHomotopy
    rw [← G.map_comp, ← G.map_id]
    simpa only [op_comp, op_id] using e.homotopyInvHomId.op
  homotopyInvHomId := by
    let F := (linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
    let G := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)
    change Homotopy
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.inv.op) ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map (G.map e.hom.op)) (𝟙 _)
    rw [← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_comp,
      ← (F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map_id]
    apply F.mapHomotopy
    rw [← G.map_comp, ← G.map_id]
    simpa only [op_comp, op_id] using e.homotopyHomInvId.op

private def integralDualShortSequence
    (S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} ℤ) (ComplexShape.down ℕ).symm) :=
  (S.op.map (HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ))).map
    (((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (ComplexShape.down ℕ).symm)

private theorem integralDualShortSequence_shortExact_of_surjective
    (S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)) (hS : S.ShortExact)
    (hsurj : ∀ n, Function.Surjective ((integralDualShortSequence S).g.f n)) :
    (integralDualShortSequence S).ShortExact := by
  let F := (linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients
  have : PreservesLimits (F ⋙ forget (ModuleCat.{u} ℤ)) :=
    inferInstanceAs (PreservesLimits (yoneda.obj integralSingularCoefficients))
  have : PreservesLimits F := preservesLimits_of_reflects_of_preserves F (forget _)
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let T := (S.map (HomologicalComplex.eval (ModuleCat.{u} ℤ) (.down ℕ) n)).op
  have hT : T.ShortExact :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n).op
  have := hT.mono_f
  change (T.map F).ShortExact
  exact
    { exact := hT.exact.map_of_mono_of_preservesKernel F hT.mono_f inferInstance
      mono_f := inferInstanceAs (Mono (F.map T.f))
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (hsurj n) }

private theorem integralRelativeDualSequence_shortExact
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    (integralDualShortSequence (integralRelativeChainSequence A)).ShortExact := by
  apply integralDualShortSequence_shortExact_of_surjective _
    (integralRelativeChainSequence_shortExact A)
  intro n φ
  obtain ⟨ψ, hψ⟩ := integralSingularCochainPullback_subspace_surjective n A φ.hom
  refine ⟨ModuleCat.ofHom ψ, ?_⟩
  exact ModuleCat.hom_ext hψ

private theorem integralSmallRelativeDualSequence_shortExact
    {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X) (i : ι) :
    (integralDualShortSequence (integralSmallRelativeSequence U i)).ShortExact := by
  apply integralDualShortSequence_shortExact_of_surjective _
    (integralSmallRelativeSequence_shortExact U i)
  intro n φ
  obtain ⟨ψ, hψ⟩ := integralSingularCochainPullback_subspace_surjective n (U i) φ.hom
  refine ⟨ModuleCat.ofHom (ψ.comp (integralSingularSmallChains n U).subtype), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact LinearMap.congr_fun hψ c

private theorem quasiIso_first_of_shortExact
    {c : ComplexShape ℕ} {S T : ShortComplex (HomologicalComplex (ModuleCat.{u} ℤ) c)}
    (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₁ := by
  let F := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) c
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (F.mapShortComplex.map (ShortComplex.opMap φ))
    (hT.op.map_of_exact F) (hS.op.map_of_exact F)
    (inferInstanceAs (QuasiIso (F.map φ.τ₃.op)))
    (inferInstanceAs (QuasiIso (F.map φ.τ₂.op)))
  exact (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₁).mp h

private def integralSmallRelativeDualSequenceComparison
    {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X) (i : ι) :
    integralDualShortSequence (integralRelativeChainSequence (U i)) ⟶
      integralDualShortSequence (integralSmallRelativeSequence U i) :=
  ((((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).mapShortComplex).map
    ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).mapShortComplex.map
      (ShortComplex.opMap (integralSmallRelativeSequenceComparison U i)))

private theorem integralSmallRelativeDualComparison_quasiIso
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (i : ι) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, x ∈ U j) :
    QuasiIso (integralChainDualMap (integralSmallRelativeComparison U i)) := by
  change QuasiIso (integralSmallRelativeDualSequenceComparison U i).τ₁
  apply quasiIso_first_of_shortExact (integralSmallRelativeDualSequenceComparison U i)
    (integralRelativeDualSequence_shortExact (U i))
    (integralSmallRelativeDualSequence_shortExact U i)
  · obtain ⟨e, he⟩ := exists_integralSingularSmallHomotopyEquiv U hU hcover
    change QuasiIso (integralChainDualMap (integralSingularSmallInclusion U))
    rw [← he]
    exact inferInstanceAs (QuasiIso (integralChainDualHomotopyEquiv e).hom)
  · exact inferInstanceAs (QuasiIso
      (integralChainDualHomotopyEquiv (HomotopyEquiv.refl (integralSingularChains (U i)))).hom)

private theorem integralChainDualMap_comp
    {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    integralChainDualMap (f ≫ g) = integralChainDualMap g ≫ integralChainDualMap f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

private theorem integralRelativeDualMap_openExcision
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    QuasiIso (integralChainDualMap
      (integralRelativeChainMap (singularSubspaceInclusion B)
        (subspaceIntersection_mapsTo A B))) := by
  have hU : ∀ i, IsOpen (twoSetCover A B i) := by
    intro i
    cases i with
    | false => exact hA
    | true => exact hB
  have hc : ∀ x, ∃ i, x ∈ twoSetCover A B i := by
    intro x
    have hx : x ∈ A ∪ B := hcover.symm ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  have := integralSmallRelativeDualComparison_quasiIso (twoSetCover A B) false hU hc
  have : IsIso (integralChainDualMap (integralExcisionSmallMap A B)) := by
    change IsIso
      ((((linearYoneda ℤ (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).mapHomologicalComplex
        (ComplexShape.down ℕ).symm).map
          ((HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.down ℕ)).map
            (integralExcisionSmallMap A B).op))
    infer_instance
  rw [← integralExcisionSmallMap_comparison, integralChainDualMap_comp]
  infer_instance

private def integralRelativeCochainsDualIso {X : Type u} [TopologicalSpace X] (A : Set X) :
    integralChainDual (integralRelativeChains A) ≅ integralRelativeCochains A := by
  have hS := integralRelativeDualSequence_shortExact A
  exact KernelFork.mapIsoOfIsLimit
    (kf' := KernelFork.ofι (integralRelativeCochainSequence A).f
      (integralRelativeCochainSequence A).zero)
    hS.fIsKernel (integralRelativeCochainSequence_shortExact A).fIsKernel
    (Arrow.isoMk (integralSingularCochainsDualIso X) (integralSingularCochainsDualIso A)
      (integralSingularCochainsDualIso_natural (singularSubspaceInclusion A)).symm)

private theorem integralRelativeCochainsDualIso_hom_inclusion
    {X : Type u} [TopologicalSpace X] (A : Set X) :
    (integralRelativeCochainsDualIso A).hom ≫ integralRelativeCochainInclusion A =
      integralChainDualMap (integralRelativeChainSequence A).g ≫
        (integralSingularCochainsDualIso X).hom := by
  let S := integralDualShortSequence (integralRelativeChainSequence A)
  let T := integralRelativeCochainSequence A
  let φ : Arrow.mk S.g ≅ Arrow.mk T.g :=
    Arrow.isoMk (integralSingularCochainsDualIso X) (integralSingularCochainsDualIso A)
      (integralSingularCochainsDualIso_natural (singularSubspaceInclusion A)).symm
  change (KernelFork.ofι S.f S.zero).mapOfIsLimit
      (integralRelativeCochainSequence_shortExact A).fIsKernel φ.hom ≫
      (KernelFork.ofι T.f T.zero).ι = _
  erw [KernelFork.mapOfIsLimit_ι]
  rfl

private theorem integralRelativeCochainsDualIso_natural
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralChainDualMap (integralRelativeChainMap f hf) ≫
        (integralRelativeCochainsDualIso A).hom =
      (integralRelativeCochainsDualIso B).hom ≫ integralRelativeCochainMap f hf := by
  have : Mono (integralRelativeCochainInclusion A) :=
    (integralRelativeCochainSequence_shortExact A).mono_f
  have hπ : (integralRelativeChainSequence A).g ≫ integralRelativeChainMap f hf =
      integralSingularChainMap f ≫ (integralRelativeChainSequence B).g :=
    integralRelativeChainMap_π f hf
  apply (cancel_mono (integralRelativeCochainInclusion A)).mp
  rw [Category.assoc, integralRelativeCochainsDualIso_hom_inclusion]
  rw [Category.assoc, integralRelativeCochainMap_inclusion]
  rw [← Category.assoc (integralRelativeCochainsDualIso B).hom
    (integralRelativeCochainInclusion B) (integralSingularCochainMap f),
    integralRelativeCochainsDualIso_hom_inclusion]
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  exact congrArg (fun k : integralSingularChains X ⟶ integralRelativeChains B =>
    φ.hom (k.f n c)) hπ


theorem integralRelativeCochainMap_openExcision
    {X : Type u} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    QuasiIso (integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) := by
  have := integralRelativeDualMap_openExcision A B hA hB hcover
  have heq : integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B) =
      (integralRelativeCochainsDualIso A).inv ≫
        integralChainDualMap (integralRelativeChainMap (singularSubspaceInclusion B)
          (subspaceIntersection_mapsTo A B)) ≫
        (integralRelativeCochainsDualIso (subspaceIntersection A B)).hom := by
    apply (cancel_epi (integralRelativeCochainsDualIso A).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (integralRelativeCochainsDualIso_natural (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)).symm
  rw [heq]
  infer_instance

theorem integralRelativeCohomologyMap_openExcision
    {X : Type u} [TopologicalSpace X] (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    Function.Bijective (integralRelativeCohomologyMap n (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) := by
  have := integralRelativeCochainMap_openExcision A B hA hB hcover
  exact (ConcreteCategory.isIso_iff_bijective _).mp (inferInstanceAs (IsIso
    (HomologicalComplex.homologyMap (integralRelativeCochainMap (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) n)))

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Module Set

universe u v

namespace DifferentialGeometry.Topology

theorem integralRelativeCohomologyMap_point_neighborhood_bijective
    {X : Type u} [TopologicalSpace X] [T1Space X] (n : ℕ) (x : X)
    (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    Function.Bijective (integralRelativeCohomologyMap n (singularSubspaceInclusion U)
      (neighborhoodPointComplement_mapsTo x U hx)) := by
  have hcover : ({x}ᶜ : Set X) ∪ U = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · exact Or.inr (hy.symm ▸ hx)
    · exact Or.inl hy
  have h := integralRelativeCohomologyMap_openExcision n ({x}ᶜ : Set X) U
    isClosed_singleton.isOpen_compl hU hcover
  have H : ∀ hf : MapsTo (singularSubspaceInclusion U)
      (subspaceIntersection ({x}ᶜ : Set X) U) ({x}ᶜ : Set X),
      Function.Bijective (integralRelativeCohomologyMap n (singularSubspaceInclusion U) hf) :=
    fun _ => h
  rw [subspaceIntersection_point_complement x U hx] at H
  exact H _

theorem integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Set X) (hK : IsClosed (f '' K)) :
    Function.Bijective (integralRelativeCohomologyMap n f
      (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective) :
        MapsTo f Kᶜ (f '' K)ᶜ)) := by
  let A : Set Y := (f '' K)ᶜ
  let B : Set Y := range f
  let e : X ≃ₜ B := hf.isEmbedding.toHomeomorph
  let g : ContinuousMap X B := ⟨e, e.continuous⟩
  have hg : MapsTo g Kᶜ (subspaceIntersection A B) := by
    intro x hx
    exact image_compl_subset hf.injective ⟨x, hx, rfl⟩
  let es : ↥(Kᶜ) ≃ₜ subspaceIntersection A B := e.subtype (fun x => by
    constructor
    · exact fun hx => hg hx
    · intro hx hxK
      exact hx ⟨x, hxK, rfl⟩)
  have hgbij : Function.Bijective (integralRelativeCohomologyMap n g hg) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv e.toHomotopyEquiv k
    · intro k
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv es.toHomotopyEquiv k
  have hcover : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ f '' K
    · obtain ⟨x, hx, rfl⟩ := hy
      exact Or.inr ⟨x, rfl⟩
    · exact Or.inl hy
  have hibij := integralRelativeCohomologyMap_openExcision n A B
    hK.isOpen_compl hf.isOpen_range hcover
  have heq := integralRelativeCohomologyMap_comp n g (singularSubspaceInclusion B)
    hg (subspaceIntersection_mapsTo A B)
  change integralRelativeCohomologyMap n f _ = _ at heq
  rw [heq]
  exact hgbij.comp hibij

theorem integralRelativeCohomologyMap_bijective_of_isOpenEmbedding
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : TopologicalSpace.Compacts X) :
    Function.Bijective (integralRelativeCohomologyMap n f
      (mapsTo_iff_image_subset.mpr (image_compl_subset hf.injective) :
        MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ)) :=
  integralRelativeCohomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image n f hf
    (K : Set X) (K.isCompact.image f.continuous).isClosed

end DifferentialGeometry.Topology

end
