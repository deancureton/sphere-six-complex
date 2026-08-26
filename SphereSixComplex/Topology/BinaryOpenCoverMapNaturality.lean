module

public import SphereSixComplex.Topology.BinaryOpenCoverNaturality

/-!
# Naturality of binary open-cover chains under continuous maps

A continuous map carries the singular subcomplex of a pulled-back open set into the original
open subcomplex.  This file packages the resulting morphism of binary-cover short complexes.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-- The restriction of a continuous map to the preimage of an open set. -/
public def openPreimageMap {X Y : TopCat} (f : X ⟶ Y) (U : Opens Y) :
    (Opens.toTopCat X).obj ((Opens.map f).obj U) ⟶ (Opens.toTopCat Y).obj U :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨f x, x.2⟩
      continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

@[reassoc]
public theorem openPreimageMap_comp_inclusion {X Y : TopCat} (f : X ⟶ Y) (U : Opens Y) :
    openPreimageMap f U ≫ Opens.inclusion' U =
      Opens.inclusion' ((Opens.map f).obj U) ≫ f := by
  rfl

/-- The map of open-image singular subcomplexes induced by a continuous map. -/
public noncomputable def pullbackOpenSubcomplexMap {X Y : TopCat}
    (f : X ⟶ Y) (U : Opens Y) :
    (singularOpenSubcomplex ((Opens.map f).obj U)).toSSet ⟶
      (singularOpenSubcomplex U).toSSet :=
  inv (singularOpenCorestriction ((Opens.map f).obj U)) ≫
    TopCat.toSSet.map (openPreimageMap f U) ≫ singularOpenCorestriction U

@[reassoc (attr := simp)]
public theorem pullbackOpenSubcomplexMap_comp_inclusion {X Y : TopCat}
    (f : X ⟶ Y) (U : Opens Y) :
    pullbackOpenSubcomplexMap f U ≫ (singularOpenSubcomplex U).ι =
      (singularOpenSubcomplex ((Opens.map f).obj U)).ι ≫ TopCat.toSSet.map f := by
  simp [pullbackOpenSubcomplexMap, ← Functor.map_comp, openPreimageMap_comp_inclusion]

@[simp]
public theorem pullbackOpenSubcomplexMap_app_val {X Y : TopCat}
    (f : X ⟶ Y) (U : Opens Y) (n) (x) :
    ((pullbackOpenSubcomplexMap f U).app n x).val =
      (TopCat.toSSet.map f).app n x.val := by
  have h := congrArg (fun q ↦ q.app n x)
    (pullbackOpenSubcomplexMap_comp_inclusion f U)
  exact h

@[reassoc]
public theorem openPreimageMap_comp_corestriction {X Y : TopCat}
    (f : X ⟶ Y) (U : Opens Y) :
    TopCat.toSSet.map (openPreimageMap f U) ≫ singularOpenCorestriction U =
      singularOpenCorestriction ((Opens.map f).obj U) ≫ pullbackOpenSubcomplexMap f U := by
  rw [← cancel_mono (singularOpenSubcomplex U).ι]
  simp [← Functor.map_comp, openPreimageMap_comp_inclusion]

/-- The map on the intersection subcomplex of a pulled-back binary cover. -/
public noncomputable def coverIntersectionPullbackMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    (coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)).toSSet ⟶
      (coverIntersection U V).toSSet :=
  SSet.Subcomplex.lift
    ((coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)).ι ≫
      TopCat.toSSet.map f)
    (by
      apply le_inf
      · have hfac :
          (coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)).ι ≫
              TopCat.toSSet.map f =
            (SSet.Subcomplex.homOfLE inf_le_left ≫ pullbackOpenSubcomplexMap f U) ≫
              (singularOpenSubcomplex U).ι := by
            simp
        rw [hfac]
        simpa only [Subfunctor.range_ι] using
          (Subfunctor.range_comp_le
            (SSet.Subcomplex.homOfLE inf_le_left ≫ pullbackOpenSubcomplexMap f U)
            (singularOpenSubcomplex U).ι)
      · have hfac :
          (coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)).ι ≫
              TopCat.toSSet.map f =
            (SSet.Subcomplex.homOfLE inf_le_right ≫ pullbackOpenSubcomplexMap f V) ≫
              (singularOpenSubcomplex V).ι := by
            simp
        rw [hfac]
        simpa only [Subfunctor.range_ι] using
          (Subfunctor.range_comp_le
            (SSet.Subcomplex.homOfLE inf_le_right ≫ pullbackOpenSubcomplexMap f V)
            (singularOpenSubcomplex V).ι))

@[reassoc (attr := simp)]
public theorem coverIntersectionPullbackMap_comp_inclusion {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    coverIntersectionPullbackMap f U V ≫ (coverIntersection U V).ι =
      (coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)).ι ≫
        TopCat.toSSet.map f :=
  SSet.Subcomplex.lift_ι _ _

@[reassoc (attr := simp)]
public theorem openIntersectionComparison_comp_inclusion {X : TopCat}
    (U V : Opens X) :
    openIntersectionComparison U V ≫ (coverIntersection U V).ι =
      (singularOpenSubcomplex (U ⊓ V)).ι := by
  rfl

/-- The map on the union subcomplex of a pulled-back binary cover. -/
public noncomputable def coverUnionPullbackMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    (coverUnion ((Opens.map f).obj U) ((Opens.map f).obj V)).toSSet ⟶
      (coverUnion U V).toSSet :=
  SSet.Subcomplex.lift
    ((coverUnion ((Opens.map f).obj U) ((Opens.map f).obj V)).ι ≫
      TopCat.toSSet.map f)
    (by
      rintro n y ⟨x, rfl⟩
      rcases x.2 with hx | hx
      · apply Or.inl
        change (TopCat.toSSet.map f).app n x.1 ∈ (singularOpenSubcomplex U).obj n
        rw [← pullbackOpenSubcomplexMap_app_val f U n ⟨x.1, hx⟩]
        exact ((pullbackOpenSubcomplexMap f U).app n ⟨x.1, hx⟩).2
      · apply Or.inr
        change (TopCat.toSSet.map f).app n x.1 ∈ (singularOpenSubcomplex V).obj n
        rw [← pullbackOpenSubcomplexMap_app_val f V n ⟨x.1, hx⟩]
        exact ((pullbackOpenSubcomplexMap f V).app n ⟨x.1, hx⟩).2)

@[reassoc (attr := simp)]
public theorem coverUnionPullbackMap_comp_inclusion {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    coverUnionPullbackMap f U V ≫ (coverUnion U V).ι =
      (coverUnion ((Opens.map f).obj U) ((Opens.map f).obj V)).ι ≫
        TopCat.toSSet.map f :=
  SSet.Subcomplex.lift_ι _ _

@[reassoc]
public theorem coverIntersectionPullbackMap_fst {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    coverIntersectionPullbackMap f U V ≫ SSet.Subcomplex.homOfLE inf_le_left =
      SSet.Subcomplex.homOfLE inf_le_left ≫ pullbackOpenSubcomplexMap f U := by
  rw [← cancel_mono (singularOpenSubcomplex U).ι]
  simp

@[reassoc]
public theorem coverIntersectionPullbackMap_snd {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    coverIntersectionPullbackMap f U V ≫ SSet.Subcomplex.homOfLE inf_le_right =
      SSet.Subcomplex.homOfLE inf_le_right ≫ pullbackOpenSubcomplexMap f V := by
  rw [← cancel_mono (singularOpenSubcomplex V).ι]
  simp

@[reassoc]
public theorem pullbackOpenSubcomplexMap_inl {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    pullbackOpenSubcomplexMap f U ≫ SSet.Subcomplex.homOfLE le_sup_left =
      SSet.Subcomplex.homOfLE le_sup_left ≫ coverUnionPullbackMap f U V := by
  rw [← cancel_mono (coverUnion U V).ι]
  simp

@[reassoc]
public theorem pullbackOpenSubcomplexMap_inr {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    pullbackOpenSubcomplexMap f V ≫ SSet.Subcomplex.homOfLE le_sup_right =
      SSet.Subcomplex.homOfLE le_sup_right ≫ coverUnionPullbackMap f U V := by
  rw [← cancel_mono (coverUnion U V).ι]
  simp

/-- The induced chain map on one member of a pulled-back open cover. -/
public noncomputable def pullbackOpenChainMap {X Y : TopCat}
    (f : X ⟶ Y) (U : Opens Y) :
    integralSimplicialChains.obj (singularOpenSubcomplex ((Opens.map f).obj U)) ⟶
      integralSimplicialChains.obj (singularOpenSubcomplex U) :=
  integralSimplicialChains.map (pullbackOpenSubcomplexMap f U)

/-- The induced chain map on the intersection term. -/
public noncomputable def coverIntersectionPullbackChainMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    (coverChainShortComplex ((Opens.map f).obj U) ((Opens.map f).obj V)).X₁ ⟶
      (coverChainShortComplex U V).X₁ := by
  change integralSimplicialChains.obj
      (coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)) ⟶
    integralSimplicialChains.obj (coverIntersection U V)
  exact integralSimplicialChains.map (coverIntersectionPullbackMap f U V)

/-- The induced chain map on the biproduct of the two cover members. -/
public noncomputable def coverBiprodPullbackChainMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    (integralSimplicialChains.obj (singularOpenSubcomplex ((Opens.map f).obj U)) ⊞
        integralSimplicialChains.obj (singularOpenSubcomplex ((Opens.map f).obj V))) ⟶
      (integralSimplicialChains.obj (singularOpenSubcomplex U) ⊞
        integralSimplicialChains.obj (singularOpenSubcomplex V)) :=
  biprod.map (pullbackOpenChainMap f U) (pullbackOpenChainMap f V)

/-- The induced chain map on the generated union term. -/
public noncomputable def coverUnionPullbackChainMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    integralSimplicialChains.obj
        (coverUnion ((Opens.map f).obj U) ((Opens.map f).obj V)) ⟶
      integralSimplicialChains.obj (coverUnion U V) :=
  integralSimplicialChains.map (coverUnionPullbackMap f U V)

/-- Pulling back both members of a binary cover along a continuous map gives a morphism of the
generated-chain short exact sequences. -/
public noncomputable def coverChainShortComplexPullback {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    coverChainShortComplex ((Opens.map f).obj U) ((Opens.map f).obj V) ⟶
      coverChainShortComplex U V where
  τ₁ := coverIntersectionPullbackChainMap f U V
  τ₂ := coverBiprodPullbackChainMap f U V
  τ₃ := coverUnionPullbackChainMap f U V
  comm₁₂ := by
    dsimp [coverIntersectionPullbackChainMap, coverBiprodPullbackChainMap,
      pullbackOpenChainMap, coverChainShortComplex]
    simp only [CommSq.shortComplex]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst]
      rw [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
      change integralSimplicialChains.map (coverIntersectionPullbackMap f U V) ≫ _ = _
      rw [← Functor.map_comp, ← Functor.map_comp, coverIntersectionPullbackMap_fst]
    · rw [Category.assoc, biprod.lift_snd]
      rw [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      change -integralSimplicialChains.map (coverIntersectionPullbackMap f U V) ≫ _ = _
      rw [Preadditive.neg_comp,
        ← Functor.map_comp, ← Functor.map_comp, coverIntersectionPullbackMap_snd]
  comm₂₃ := by
    dsimp [coverUnionPullbackChainMap, coverBiprodPullbackChainMap,
      pullbackOpenChainMap, coverChainShortComplex]
    simp only [CommSq.shortComplex]
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp, pullbackOpenSubcomplexMap_inl]
    · rw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp, pullbackOpenSubcomplexMap_inr]

/-- The induced map between generated intersection homology groups. -/
public noncomputable def generatedIntersectionPullbackHomologyMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    generatedIntersectionHomology ((Opens.map f).obj U) ((Opens.map f).obj V) n ⟶
      generatedIntersectionHomology U V n :=
  HomologicalComplex.homologyMap (coverIntersectionPullbackChainMap f U V) n

/-- The induced map between generated union homology groups. -/
public noncomputable def generatedUnionPullbackHomologyMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    generatedUnionHomology ((Opens.map f).obj U) ((Opens.map f).obj V) n ⟶
      generatedUnionHomology U V n :=
  HomologicalComplex.homologyMap (coverUnionPullbackChainMap f U V) n

/-- The generated Mayer--Vietoris boundary is natural for a continuous map and a pulled-back
binary open cover. -/
@[reassoc]
public theorem generatedBoundary_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    generatedBoundary ((Opens.map f).obj U) ((Opens.map f).obj V) n ≫
        generatedIntersectionPullbackHomologyMap f U V n =
      generatedUnionPullbackHomologyMap f U V (n + 1) ≫
        generatedBoundary U V n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (coverChainShortComplexPullback f U V)
    (coverChainShortComplex_shortExact ((Opens.map f).obj U) ((Opens.map f).obj V))
    (coverChainShortComplex_shortExact U V) (n + 1) n rfl

/-- The restriction map between the intersections of a binary cover and its pullback. -/
public def openIntersectionPreimageMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    (Opens.toTopCat X).obj ((Opens.map f).obj U ⊓ (Opens.map f).obj V) ⟶
      (Opens.toTopCat Y).obj (U ⊓ V) :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨f x, ⟨x.2.1, x.2.2⟩⟩
      continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

@[reassoc]
public theorem openIntersectionPreimageMap_comp_inclusion {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) :
    openIntersectionPreimageMap f U V ≫ Opens.inclusion' (U ⊓ V) =
      Opens.inclusion' ((Opens.map f).obj U ⊓ (Opens.map f).obj V) ≫ f := by
  rfl

/-- The ordinary homology map between the intersections of a binary cover and its pullback. -/
public noncomputable def openIntersectionPullbackHomologyMap {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    (integralHomologyFunctor n).obj
        ((Opens.toTopCat X).obj ((Opens.map f).obj U ⊓ (Opens.map f).obj V)) ⟶
      (integralHomologyFunctor n).obj ((Opens.toTopCat Y).obj (U ⊓ V)) :=
  (integralHomologyFunctor n).map (openIntersectionPreimageMap f U V)

/-- Compatibility of the generated-cover comparisons with a continuous map. -/
public structure OpenCoverHomologyComparison.PullbackNaturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y)
    (source : OpenCoverHomologyComparison ((Opens.map f).obj U) ((Opens.map f).obj V))
    (target : OpenCoverHomologyComparison U V) : Prop where
  intersection (n : ℕ) :
    generatedIntersectionPullbackHomologyMap f U V n ≫ (target.intersectionIso n).hom =
      (source.intersectionIso n).hom ≫ openIntersectionPullbackHomologyMap f U V n
  union (n : ℕ) :
    generatedUnionPullbackHomologyMap f U V n ≫ (target.unionIso n).hom =
      (source.unionIso n).hom ≫ (integralHomologyFunctor n).map f

/-- Naturality of the ordinary singular Mayer--Vietoris boundary follows from compatibility of
the generated-cover comparison isomorphisms. -/
public theorem OpenCoverHomologyComparison.boundary_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y)
    (source : OpenCoverHomologyComparison ((Opens.map f).obj U) ((Opens.map f).obj V))
    (target : OpenCoverHomologyComparison U V)
    (h : source.PullbackNaturality f U V target) (n : ℕ) :
    source.boundary n ≫ openIntersectionPullbackHomologyMap f U V n =
      (integralHomologyFunctor (n + 1)).map f ≫ target.boundary n := by
  rw [← cancel_epi (source.unionIso (n + 1)).hom]
  conv_lhs => rw [← Category.assoc]
  rw [source.unionIso_hom_comp_boundary, Category.assoc, ← h.intersection]
  have hn := congrArg (fun q ↦ q ≫ (target.intersectionIso n).hom)
    (generatedBoundary_pullback_naturality f U V n)
  calc
    generatedBoundary ((Opens.map f).obj U) ((Opens.map f).obj V) n ≫
        (generatedIntersectionPullbackHomologyMap f U V n ≫
          (target.intersectionIso n).hom) =
      (generatedBoundary ((Opens.map f).obj U) ((Opens.map f).obj V) n ≫
        generatedIntersectionPullbackHomologyMap f U V n) ≫
          (target.intersectionIso n).hom := (Category.assoc _ _ _).symm
    _ = (generatedUnionPullbackHomologyMap f U V (n + 1) ≫
        generatedBoundary U V n) ≫ (target.intersectionIso n).hom := by
      simpa only [generatedIntersectionHomology, generatedUnionHomology] using hn
    _ = generatedUnionPullbackHomologyMap f U V (n + 1) ≫
        (generatedBoundary U V n ≫ (target.intersectionIso n).hom) :=
      Category.assoc _ _ _
    _ = generatedUnionPullbackHomologyMap f U V (n + 1) ≫
        ((target.unionIso (n + 1)).hom ≫ target.boundary n) := by
      rw [target.unionIso_hom_comp_boundary]
    _ = (generatedUnionPullbackHomologyMap f U V (n + 1) ≫
        (target.unionIso (n + 1)).hom) ≫ target.boundary n :=
      (Category.assoc _ _ _).symm
    _ = ((source.unionIso (n + 1)).hom ≫
        (integralHomologyFunctor (n + 1)).map f) ≫ target.boundary n := by
      rw [h.union]

end SphereSixComplex.BinaryOpenCover
