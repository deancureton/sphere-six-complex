module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe u v w

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)


def smallSingularSimplices : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ h := by
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨Convexity.StdSimplex.map f.unop z, rfl⟩


theorem mem_smallSingularSimplices_iff {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingularSimplices X U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i := Iff.rfl

theorem smallSingularSimplices_eq_iSup_range :
    smallSingularSimplices X U =
      ⨆ i, SSet.Subcomplex.range
        (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
          C(U i, X)))) := by
  ext n σ
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj,
    Set.mem_range, mem_smallSingularSimplices_iff]
  constructor
  · rintro ⟨i, hi⟩
    let τ : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), U i) :=
      ⟨fun z ↦ ⟨X.toSSetObjEquiv n σ z, hi ⟨z, rfl⟩⟩,
        (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨i, ((TopCat.of (U i)).toSSetObjEquiv n).symm τ, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl
  · rintro ⟨i, τ, rfl⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (((TopCat.of (U i)).toSSetObjEquiv n) τ z).property


theorem smallSingularSimplices_le {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularSimplices X U ≤ smallSingularSimplices X V := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨j, hj⟩ := hUV i
  exact ⟨j, hi.trans hj⟩


theorem smallSingularSimplices_eq_top (hU : ∃ i, U i = Set.univ) :
    smallSingularSimplices X U = ⊤ := by
  obtain ⟨i, hi⟩ := hU
  apply top_unique
  intro n σ _
  exact ⟨i, hi ▸ Set.subset_univ _⟩


theorem smallSingularSimplices_obj_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    (smallSingularSimplices X U).obj (op ⦋0⦌) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro σ
  obtain ⟨i, hi⟩ := hU (X.toSSetObjEquiv _ σ default)
  refine ⟨i, ?_⟩
  rintro _ ⟨z, rfl⟩
  simpa only [Subsingleton.elim z default] using hi

variable {X U} {Y : TopCat.{u}} {κ : Type w} {V : κ → Set Y}


def smallSingularSimplicesMap (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    (smallSingularSimplices X U : SSet) ⟶ smallSingularSimplices Y V where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map f).app n σ.val, by
    obtain ⟨i, hi⟩ := σ.property
    obtain ⟨j, hj⟩ := hf i
    refine ⟨j, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hj (hi ⟨z, rfl⟩)⟩
  naturality _ _ _ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality _) σ.val


@[reassoc (attr := simp)]
theorem smallSingularSimplicesMap_ι (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    smallSingularSimplicesMap f hf ≫ (smallSingularSimplices Y V).ι =
      (smallSingularSimplices X U).ι ≫ TopCat.toSSet.map f := rfl

variable (X U) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def smallChainMap :
    (smallSingularSimplices X U : SSet).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X :=
  SSet.chainComplexMap (smallSingularSimplices X U).ι R


@[reassoc (attr := simp)]
theorem ι_smallChainMap_f {n : ℕ}
    (σ : (smallSingularSimplices X U : SSet) _⦋n⦌) :
    (smallSingularSimplices X U : SSet).ιChainComplex σ ≫ (smallChainMap X U R).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ.val :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

private def smallChainProjection (n : ℕ) :
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X).X n ⟶
      ((smallSingularSimplices X U : SSet).chainComplex R).X n := by
  classical
  exact Sigma.desc (fun σ ↦ if hσ : σ ∈ (smallSingularSimplices X U).obj (op ⦋n⦌)
    then (smallSingularSimplices X U : SSet).ιChainComplex ⟨σ, hσ⟩ else 0)

private theorem smallChainMap_projection (n : ℕ) :
    (smallChainMap X U R).f n ≫ smallChainProjection X U R n = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallChainMap_f]
  change Sigma.ι _ σ.val ≫ Sigma.desc _ = _
  rw [Sigma.ι_comp_desc]
  simp only [dite_eq_left σ.property, Category.comp_id]
  rfl


theorem mono_smallChainMap_f (n : ℕ) : Mono ((smallChainMap X U R).f n) := by
  have : IsSplitMono ((smallChainMap X U R).f n) :=
    IsSplitMono.mk' ⟨smallChainProjection X U R n, smallChainMap_projection X U R n⟩
  infer_instance


theorem mono_smallChainMap : Mono (smallChainMap X U R) :=
  HomologicalComplex.mono_of_mono_f _ (mono_smallChainMap_f X U R)


theorem isIso_smallChainMap_f_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    IsIso ((smallChainMap X U R).f 0) := by
  refine ⟨⟨smallChainProjection X U R 0, smallChainMap_projection X U R 0, ?_⟩⟩
  apply SSet.chainComplex_hom_ext
  intro σ
  have hσ : σ ∈ (smallSingularSimplices X U).obj (op ⦋0⦌) := by
    rw [smallSingularSimplices_obj_zero X U hU]
    exact Set.mem_univ _
  change Sigma.ι _ σ ≫ (Sigma.desc _ ≫ _) = _
  rw [← Category.assoc, Sigma.ι_comp_desc]
  simp only [dite_eq_left hσ]
  exact (ι_smallChainMap_f X U R ⟨σ, hσ⟩).trans (Category.comp_id _).symm


theorem smallChainMap_naturality (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    SSet.chainComplexMap (smallSingularSimplicesMap f hf) R ≫ smallChainMap Y V R =
      smallChainMap X U R ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map f := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallSingularSimplicesMap_ι]


def smallChainRefinement {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    (smallSingularSimplices X U : SSet).chainComplex R ⟶
      (smallSingularSimplices X V : SSet).chainComplex R :=
  SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (smallSingularSimplices_le X U V hUV)) R


@[reassoc (attr := simp)]
theorem smallChainRefinement_smallChainMap {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallChainRefinement X U R V hUV ≫ smallChainMap X V R = smallChainMap X U R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ = _
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  rfl

end DifferentialGeometry.Homology
