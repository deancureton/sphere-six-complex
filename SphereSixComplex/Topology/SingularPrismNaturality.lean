module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology SimplexCategory Simplicial
namespace SphereSixComplex

public theorem simplicialPrism_naturality
    {C : Type*} [Category C] [Preadditive C]
    {A B X Y : SimplicialObject C} {f g : A ⟶ B} {f' g' : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) (K : SimplicialObject.Homotopy f' g')
    (i : A ⟶ X) (j : B ⟶ Y)
    (h : ∀ n (k : Fin (n + 1)), i.app (op ⦋n⦌) ≫ K.h k = H.h k ≫ j.app (op ⦋n + 1⦌))
    (p q : ℕ) :
    ((alternatingFaceMapComplex C).map i).f p ≫ K.toChainHomotopy.hom p q =
      H.toChainHomotopy.hom p q ≫ ((alternatingFaceMapComplex C).map j).f q := by
  change i.app _ ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom K p q =
    SimplicialObject.Homotopy.ToChainHomotopy.hom H p q ≫ j.app _
  by_cases hpq : p + 1 = q
  · subst q
    simp only [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, h]
  · simp [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hpq]

open MonoidalCategory SSet in
public theorem sSetHomotopy_components_naturality
    {A B X Y : SSet} {f g : A ⟶ B} {f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy f' g')
    (i : A ⟶ X) (j : B ⟶ Y)
    (h : i ▷ Δ[1] ≫ K.h = H.h ≫ j) (n : ℕ) (k : Fin (n + 1)) :
    i.app (op ⦋n⦌) ≫ K.toSimplicialObjectHomotopy.h k =
      H.toSimplicialObjectHomotopy.h k ≫ j.app (op ⦋n + 1⦌) := by
  ext x
  dsimp [SSet.Homotopy.toSimplicialObjectHomotopy]
  have hx := congrArg (fun z ↦ ((yonedaEquiv.symm x : Δ[n] ⟶ A) ▷ Δ[1] ≫ z).app (op ⦋n + 1⦌)
    (SSet.prodStdSimplex.nonDegenerateEquiv₁ k).1) h
  simp only [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    SSet.yonedaEquiv_symm_comp] at hx
  exact hx

open MonoidalCategory SSet in
public theorem sSetPrism_naturality
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts C]
    {A B X Y : SSet} {f g : A ⟶ B} {f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy f' g')
    (i : A ⟶ X) (j : B ⟶ Y) (h : i ▷ Δ[1] ≫ K.h = H.h ≫ j)
    (R : C) (p q : ℕ) :
    (SSet.chainComplexMap i R).f p ≫ (K.chainComplexMap R).hom p q =
      (H.chainComplexMap R).hom p q ≫ (SSet.chainComplexMap j R).f q := by
  apply simplicialPrism_naturality
  intro n k
  change (sigmaConst.obj R).map _ ≫ (sigmaConst.obj R).map _ =
    (sigmaConst.obj R).map _ ≫ (sigmaConst.obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, sSetHomotopy_components_naturality H K i j h]

open MonoidalCategory Functor.LaxMonoidal in
public theorem topologicalPrism_naturality
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts C]
    {A B X Y : TopCat} {f g : A ⟶ B} {f' g' : X ⟶ Y}
    (H : TopCat.Homotopy f g) (K : TopCat.Homotopy f' g')
    (i : A ⟶ X) (j : B ⟶ Y) (h : i ▷ TopCat.I ≫ K.h = H.h ≫ j)
    (R : C) (p q : ℕ) :
    (((singularChainComplexFunctor C).obj R).map i).f p ≫
        (K.singularChainComplexFunctorObjMap R).hom p q =
      (H.singularChainComplexFunctorObjMap R).hom p q ≫
        (((singularChainComplexFunctor C).obj R).map j).f q := by
  apply sSetPrism_naturality
  dsimp [TopCat.Homotopy.toSSet]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  simp only [Category.assoc, μ_natural_left_assoc, ← Functor.map_comp, h]

end SphereSixComplex
