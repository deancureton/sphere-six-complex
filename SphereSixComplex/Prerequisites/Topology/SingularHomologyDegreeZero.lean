/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Naturality of the degree-zero singular-homology augmentation

Mathlib identifies degree-zero simplicial homology with the coproduct indexed by path
components and defines its augmentation, but does not expose the augmentation as a natural
transformation. This file proves the required naturality directly on simplex generators.

The proof cancels the epimorphism from cycles to homology, applies naturality of `homologyπ`,
and uses the canonical isomorphism from degree-zero cycles to degree-zero chains. Naturality is
then exactly `SSet.ι_chainComplexMap_f` on each zero-simplex.
-/

@[expose] public section

open AlgebraicTopology CategoryTheory Limits Simplicial

namespace SphereSixComplex

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C] [CategoryWithHomology C]

/-- On a zero-simplex, the inverse of the degree-zero cycles isomorphism is the canonical lift
to cycles. -/
@[reassoc (attr := simp)]
public lemma sSetιChainComplex_cycles₀Iso_inv {X : SSet.{w}} (R : C) (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ ((X.chainComplex R).cycles₀Iso).inv =
      (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
  rw [← cancel_mono ((X.chainComplex R).iCycles 0)]
  simp

/-- The degree-zero simplicial-homology augmentation is natural in the simplicial set. -/
@[reassoc]
public theorem sSetHomologyMap_comp_homology₀ε {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  rw [← cancel_epi ((X.chainComplex R).homologyπ 0),
    HomologicalComplex.homologyπ_naturality_assoc]
  rw [← cancel_epi ((X.chainComplex R).cycles₀Iso).inv]
  apply X.chainComplex_hom_ext
  intro x
  simp

/-- The degree-zero singular-homology augmentation is natural in the topological space. -/
@[reassoc]
public theorem singularHomologyMap_comp_singularHomology₀ε
    {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    ((singularHomologyFunctor C 0).obj R).map f ≫ Y.singularHomology₀ε R =
      X.singularHomology₀ε R := by
  change
    SSet.homologyMap (TopCat.toSSet.map f) R 0 ≫
        (TopCat.toSSet.obj Y).homology₀ε R =
      (TopCat.toSSet.obj X).homology₀ε R
  exact sSetHomologyMap_comp_homology₀ε (TopCat.toSSet.map f) R

/-- Every map between path-connected spaces is an isomorphism on degree-zero integral singular
homology. -/
public theorem integralSingularHomologyMap_zero_isIso
    {X Y : TopCat} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) :
    IsIso (((singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).map f) := by
  exact IsIso.of_isIso_fac_right
    (singularHomologyMap_comp_singularHomology₀ε f (AddCommGrpCat.of ℤ))

end SphereSixComplex
