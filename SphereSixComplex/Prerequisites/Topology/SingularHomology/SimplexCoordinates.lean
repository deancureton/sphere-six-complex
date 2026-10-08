module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! # Coordinate descriptions of singular simplices -/

@[expose] public section
noncomputable section
open CategoryTheory

namespace SphereSixComplex

/-- A singular simplex expressed as a continuous map on the coordinate simplex. -/
public noncomputable def singularSimplexContinuousMapEquiv (X : TopCat) (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj X).obj n ≃ C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
  X.toSSetObjEquiv n

/-- The continuous affine inclusion of a codimension-one face of a standard simplex. -/
public noncomputable def standardSimplexFaceContinuousMap
    (n : ℕ) (p : Fin (n + 2)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  ⟨Convexity.StdSimplex.map p.succAbove, Convexity.StdSimplex.continuous_map ℝ p.succAbove⟩

/-- The face inclusion as a morphism of topological spaces. -/
public noncomputable def standardSimplexFaceTopCatMap
    (n : ℕ) (p : Fin (n + 2)) :
    TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  TopCat.ofHom (standardSimplexFaceContinuousMap n p)

/-- The topological map represented by a singular simplex. -/
public noncomputable def singularSimplexTopCatMap
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ X :=
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
  rfl

end SphereSixComplex
