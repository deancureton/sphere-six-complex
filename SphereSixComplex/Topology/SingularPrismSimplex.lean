module

public import SphereSixComplex.Topology.SingularPrismNaturality
public import SphereSixComplex.Topology.StandardCircleHomologyLiftDegree

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open SimplexCategory Simplicial
namespace SphereSixComplex

open MonoidalCategory CartesianMonoidalCategory Functor.LaxMonoidal in
public theorem toSSet_product_simplex (X Y : TopCat) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) (y : (TopCat.toSSet.obj Y).obj n)
    (s : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    (X ⊗ Y).toSSetObjEquiv n ((μ TopCat.toSSet X Y).app n (x, y)) s =
      (X.toSSetObjEquiv n x s, Y.toSSetObjEquiv n y s) := by
  apply Prod.ext
  · have h := congrArg (fun f => f.app n) (Functor.Monoidal.μ_fst TopCat.toSSet X Y)
    have h' := congrArg (fun f => f (x, y)) h
    exact congrArg (fun z => X.toSSetObjEquiv n z s) h'
  · have h := congrArg (fun f => f.app n) (Functor.Monoidal.μ_snd TopCat.toSSet X Y)
    have h' := congrArg (fun f => f (x, y)) h
    exact congrArg (fun z => Y.toSSetObjEquiv n z s) h'

public theorem sSetPrism_one_simplex {X Y : SSet} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : X.obj (Opposite.op ⦋1⦌)) :
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫ (H.chainComplexMap _).hom 1 2 =
      Y.ιChainComplex (H.toSimplicialObjectHomotopy.h 1 x) -
        Y.ιChainComplex (H.toSimplicialObjectHomotopy.h 0 x) := by
  change _ ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom
    (H.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj (AddCommGrpCat.of ℤ))) 1 (1 + 1) = _
  simp [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    Fin.sum_univ_two, Preadditive.comp_neg, Preadditive.comp_add,
    SSet.ιChainComplex, sub_eq_add_neg, SimplicialObject.Homotopy.whiskerRight, sigmaConst]

end SphereSixComplex
