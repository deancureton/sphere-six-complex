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
    integralSimplicialChains.obj
        (coverIntersection ((Opens.map f).obj U) ((Opens.map f).obj V)) ⟶
      integralSimplicialChains.obj (coverIntersection U V) :=
  integralSimplicialChains.map (coverIntersectionPullbackMap f U V)

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
      rw [← Functor.map_comp, ← Functor.map_comp, coverIntersectionPullbackMap_fst]
    · rw [Category.assoc, biprod.lift_snd]
      rw [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
      rw [Preadditive.comp_neg, Preadditive.neg_comp,
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

/-- The generated Mayer--Vietoris boundary is natural for a continuous map and a pulled-back
binary open cover. -/
public theorem generatedBoundary_pullback_naturality {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    generatedBoundary ((Opens.map f).obj U) ((Opens.map f).obj V) n ≫
        HomologicalComplex.homologyMap (coverIntersectionPullbackChainMap f U V) n =
      HomologicalComplex.homologyMap (coverUnionPullbackChainMap f U V) (n + 1) ≫
        generatedBoundary U V n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (coverChainShortComplexPullback f U V)
    (coverChainShortComplex_shortExact ((Opens.map f).obj U) ((Opens.map f).obj V))
    (coverChainShortComplex_shortExact U V) (n + 1) n rfl

end SphereSixComplex.BinaryOpenCover
