module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.MonoCoprod

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
noncomputable section
universe u
namespace DifferentialGeometry.SSet
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


instance chainComplexFunctor_preservesColimits :
    PreservesColimitsOfSize.{u, u} ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R) where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌) ⋙ sigmaConst.obj R)
    infer_instance


instance chainComplexFunctor_preservesMonomorphisms :
    ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [_root_.SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono

end DifferentialGeometry.SSet
