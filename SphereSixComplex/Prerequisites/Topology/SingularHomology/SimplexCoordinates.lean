module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex

/-! # Coordinate descriptions of singular simplices -/

@[expose] public section
noncomputable section
open CategoryTheory

namespace SphereSixComplex

/-- Finite probability weights expressed as coordinates in the standard simplex. -/
public noncomputable def finiteSimplexHomeomorph (ι : Type) [Fintype ι] :
    Convexity.StdSimplex ℝ ι ≃ₜ stdSimplex ℝ ι where
  toFun w := ⟨w.weights, w.weights_nonneg, w.total_of_fintype⟩
  invFun w := ⟨Finsupp.equivFunOnFinite.symm w.val, by intro i; exact w.property.1 i,
    by simpa [Finsupp.sum_fintype] using w.property.2⟩
  left_inv w := by ext i; rfl
  right_inv w := by rfl
  continuous_toFun := ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous).subtype_mk _
  continuous_invFun := (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.mpr
    continuous_subtype_val

/-- A singular simplex expressed as a continuous map on the coordinate simplex. -/
public noncomputable def singularSimplexContinuousMapEquiv (X : TopCat) (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) where
  toFun x := (X.toSSetObjEquiv n x).comp
    ⟨(finiteSimplexHomeomorph _).symm, (finiteSimplexHomeomorph _).symm.continuous⟩
  invFun f := (X.toSSetObjEquiv n).symm
    (f.comp ⟨finiteSimplexHomeomorph _, (finiteSimplexHomeomorph _).continuous⟩)
  left_inv x := by apply (X.toSSetObjEquiv n).injective; ext w; simp
  right_inv f := by ext w; simp

/-- The continuous affine inclusion of a codimension-one face of a standard simplex. -/
public noncomputable def standardSimplexFaceContinuousMap
    (n : ℕ) (p : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map p.succAbove, stdSimplex.continuous_map p.succAbove⟩

/-- The face inclusion as a morphism of topological spaces. -/
public noncomputable def standardSimplexFaceTopCatMap
    (n : ℕ) (p : Fin (n + 2)) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶
      TopCat.of (stdSimplex ℝ (Fin (n + 2))) :=
  TopCat.ofHom (standardSimplexFaceContinuousMap n p)

/-- The topological map represented by a singular simplex. -/
public noncomputable def singularSimplexTopCatMap
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ X :=
  TopCat.ofHom (singularSimplexContinuousMapEquiv X _ x)

/-- The map represented by a face of a singular simplex is obtained by precomposing with the
standard topological coface inclusion. -/
public theorem singularSimplexTopCatMap_delta
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))))
    (p : Fin (n + 2)) :
    standardSimplexFaceTopCatMap n p ≫
        singularSimplexTopCatMap X (n + 1) x =
      singularSimplexTopCatMap X n ((TopCat.toSSet.obj X).δ p x) := by
  ext w
  change X.toSSetObjEquiv _ x ((finiteSimplexHomeomorph _).symm (stdSimplex.map p.succAbove w)) =
    X.toSSetObjEquiv _ x (Convexity.StdSimplex.map p.succAbove ((finiteSimplexHomeomorph _).symm w))
  congr 1
  ext i
  rfl

end SphereSixComplex
