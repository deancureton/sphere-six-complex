module

public import SphereSixComplex.Topology.BinaryOpenCoverAssembly

/-!
# Swapping a binary open cover

Swapping the two members of a binary open cover negates its canonical Mayer--Vietoris
connecting morphism.  The sign comes from the negative identity on the intersection term of
the swapped short complex.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits TopologicalSpace

namespace SphereSixComplex.BinaryOpenCover

/-- The identity on underlying points swaps the two open-intersection realizations. -/
public def opensIntersectionSwapHomeomorph {X : TopCat} (U V : Opens X) :
    (Opens.toTopCat X).obj (U ⊓ V) ≃ₜ (Opens.toTopCat X).obj (V ⊓ U) where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The identity on underlying points swaps the two open-union realizations. -/
public def opensUnionSwapHomeomorph {X : TopCat} (U V : Opens X) :
    (Opens.toTopCat X).obj (U ⊔ V) ≃ₜ (Opens.toTopCat X).obj (V ⊔ U) where
  toFun x := ⟨x.1, Opens.mem_sup.mpr (x.2.elim Or.inr Or.inl)⟩
  invFun x := ⟨x.1, Opens.mem_sup.mpr (x.2.elim Or.inr Or.inl)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The continuous map between open intersections induced by swapping the opens. -/
public def openIntersectionSwapMap {X : TopCat} (U V : Opens X) :
    (Opens.toTopCat X).obj (U ⊓ V) ⟶ (Opens.toTopCat X).obj (V ⊓ U) :=
  (TopCat.isoOfHomeo (opensIntersectionSwapHomeomorph U V)).hom

/-- The homology map between open intersections induced by swapping the opens. -/
public noncomputable def openIntersectionSwapHomologyMap {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (U ⊓ V)) ⟶
      (integralHomologyFunctor n).obj ((Opens.toTopCat X).obj (V ⊓ U)) :=
  (integralHomologyFunctor n).map (openIntersectionSwapMap U V)

/-- Swapping the factors of the generated intersection subcomplex. -/
public noncomputable def coverIntersectionSwapMap {X : TopCat} (U V : Opens X) :
    (coverIntersection U V).toSSet ⟶ (coverIntersection V U).toSSet :=
  SSet.Subcomplex.homOfLE (by
    change singularOpenSubcomplex U ⊓ singularOpenSubcomplex V ≤
      singularOpenSubcomplex V ⊓ singularOpenSubcomplex U
    rw [inf_comm])

/-- Swapping the factors of the generated union subcomplex. -/
public noncomputable def coverUnionSwapMap {X : TopCat} (U V : Opens X) :
    (coverUnion U V).toSSet ⟶ (coverUnion V U).toSSet :=
  SSet.Subcomplex.homOfLE (by
    change singularOpenSubcomplex U ⊔ singularOpenSubcomplex V ≤
      singularOpenSubcomplex V ⊔ singularOpenSubcomplex U
    rw [sup_comm])

/-- Integral chains induced by swapping the generated intersection. -/
public noncomputable def coverIntersectionSwapChainMap {X : TopCat} (U V : Opens X) :
    integralSimplicialChains.obj (coverIntersection U V) ⟶
      integralSimplicialChains.obj (coverIntersection V U) :=
  integralSimplicialChains.map (coverIntersectionSwapMap U V)

/-- Integral chains induced by swapping the generated union. -/
public noncomputable def coverUnionSwapChainMap {X : TopCat} (U V : Opens X) :
    integralSimplicialChains.obj (coverUnion U V) ⟶
      integralSimplicialChains.obj (coverUnion V U) :=
  integralSimplicialChains.map (coverUnionSwapMap U V)

private theorem intersectionSwapSSetNaturality {X : TopCat} (U V : Opens X) :
    singularOpenCorestriction (U ⊓ V) ≫ openIntersectionComparison U V ≫
        coverIntersectionSwapMap U V =
      TopCat.toSSet.map (openIntersectionSwapMap U V) ≫
        singularOpenCorestriction (V ⊓ U) ≫ openIntersectionComparison V U := by
  rw [← cancel_mono (coverIntersection V U).ι]
  simp [← Functor.map_comp, openIntersectionSwapMap, coverIntersectionSwapMap]
  congr 1

private theorem intersectionSwapChainNaturality {X : TopCat} (U V : Opens X) :
    (singularOpenCorestrictionChainMap (U ⊓ V) ≫
        openIntersectionChainComparison U V) ≫ coverIntersectionSwapChainMap U V =
      integralSimplicialChains.map (TopCat.toSSet.map (openIntersectionSwapMap U V)) ≫
        (singularOpenCorestrictionChainMap (V ⊓ U) ≫
          openIntersectionChainComparison V U) := by
  simpa only [singularOpenCorestrictionChainMap, openIntersectionChainComparison,
    coverIntersectionSwapChainMap, Functor.map_comp, Category.assoc] using
    congrArg integralSimplicialChains.map (intersectionSwapSSetNaturality U V)

private theorem unionSwapChainNaturality {X : TopCat} (U V : Opens X) :
    coverUnionSwapChainMap U V ≫ coverChainInclusion V U =
      coverChainInclusion U V := by
  dsimp [coverUnionSwapChainMap, coverUnionSwapMap, coverChainInclusion]
  rw [← Functor.map_comp]
  rfl

/-- The morphism of cover-chain short complexes induced by swapping the two opens. -/
public noncomputable def coverChainShortComplexSwap {X : TopCat} (U V : Opens X) :
    coverChainShortComplex U V ⟶ coverChainShortComplex V U where
  τ₁ := by
    change integralSimplicialChains.obj (coverIntersection U V) ⟶
      integralSimplicialChains.obj (coverIntersection V U)
    exact -coverIntersectionSwapChainMap U V
  τ₂ := by
    change (integralSimplicialChains.obj (singularOpenSubcomplex U) ⊞
        integralSimplicialChains.obj (singularOpenSubcomplex V)) ⟶
      (integralSimplicialChains.obj (singularOpenSubcomplex V) ⊞
        integralSimplicialChains.obj (singularOpenSubcomplex U))
    exact (biprod.braiding _ _).hom
  τ₃ := by
    change integralSimplicialChains.obj (coverUnion U V) ⟶
      integralSimplicialChains.obj (coverUnion V U)
    exact coverUnionSwapChainMap U V
  comm₁₂ := by
    dsimp [coverChainShortComplex, coverIntersectionSwapChainMap,
      coverIntersectionSwapMap]
    simp only [CommSq.shortComplex]
    apply biprod.hom_ext
    · simp only [id_eq, Preadditive.neg_comp, Category.assoc, biprod.lift_fst,
        biprod.lift_snd, biprod.braiding_hom]
      rw [← Functor.map_comp]
      rfl
    · simp only [id_eq, Preadditive.neg_comp, Category.assoc, biprod.lift_fst,
        biprod.lift_snd, biprod.braiding_hom, Preadditive.comp_neg, neg_neg]
      rw [← Functor.map_comp]
      rfl
  comm₂₃ := by
    dsimp [coverChainShortComplex, coverUnionSwapChainMap, coverUnionSwapMap]
    simp only [CommSq.shortComplex]
    apply biprod.hom_ext'
    · rw [← biprod.braiding'_eq_braiding]
      simp only [id_eq, biprod.braiding'_hom, biprod.inl_desc_assoc]
      rw [biprod.inr_desc]
      rw [← Functor.map_comp]
      rfl
    · rw [← biprod.braiding'_eq_braiding]
      simp only [id_eq, biprod.braiding'_hom, biprod.inr_desc_assoc]
      rw [biprod.inl_desc]
      rw [← Functor.map_comp]
      rfl

/-- The homology map induced by swapping the generated intersection. -/
public noncomputable abbrev generatedIntersectionSwapHomologyMap {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    generatedIntersectionHomology U V n ⟶ generatedIntersectionHomology V U n :=
  HomologicalComplex.homologyMap (coverIntersectionSwapChainMap U V) n

/-- The homology map induced by swapping the generated union. -/
public noncomputable abbrev generatedUnionSwapHomologyMap {X : TopCat}
    (U V : Opens X) (n : ℕ) :
    generatedUnionHomology U V n ⟶ generatedUnionHomology V U n :=
  HomologicalComplex.homologyMap (coverUnionSwapChainMap U V) n

/-- On generated-cover homology, swapping the opens negates the connecting morphism. -/
public theorem generatedBoundary_swap {X : TopCat} (U V : Opens X) (n : ℕ) :
    generatedBoundary U V n ≫ generatedIntersectionSwapHomologyMap U V n =
      -(generatedUnionSwapHomologyMap U V (n + 1) ≫ generatedBoundary V U n) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (coverChainShortComplexSwap U V)
    (coverChainShortComplex_shortExact U V)
    (coverChainShortComplex_shortExact V U) (n + 1) n rfl
  have h₁ : HomologicalComplex.homologyMap (coverChainShortComplexSwap U V).τ₁ n =
      -generatedIntersectionSwapHomologyMap U V n := by
    change HomologicalComplex.homologyMap (-coverIntersectionSwapChainMap U V) n =
      -HomologicalComplex.homologyMap (coverIntersectionSwapChainMap U V) n
    exact HomologicalComplex.homologyMap_neg _ _
  have h₃ : HomologicalComplex.homologyMap
      (coverChainShortComplexSwap U V).τ₃ (n + 1) =
      generatedUnionSwapHomologyMap U V (n + 1) := by
    rfl
  rw [h₁, h₃, Preadditive.comp_neg] at h
  exact neg_eq_iff_eq_neg.mp h

end SphereSixComplex.BinaryOpenCover

end

end
