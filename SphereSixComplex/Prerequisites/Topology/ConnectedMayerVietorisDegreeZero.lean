module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Degree-zero Mayer--Vietoris maps for connected spaces

Naturality of the singular-homology augmentation implies that every map from a path-connected
space induces an injection on degree-zero homology. In particular, the Mayer--Vietoris
difference map is injective whenever the overlap is path-connected.
-/

@[expose] public section

noncomputable section

universe w v u

open AlgebraicTopology CategoryTheory Limits Simplicial
open scoped ContinuousMap

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

/-- Naturality of the degree-zero singular-homology augmentation. -/
@[reassoc]
public theorem singularHomology₀ε_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    ((singularHomologyFunctor C 0).obj R).map f ≫ Y.singularHomology₀ε R =
      X.singularHomology₀ε R := by
  change SSet.homologyMap (TopCat.toSSet.map f) R 0 ≫
      (TopCat.toSSet.obj Y).homology₀ε R =
    (TopCat.toSSet.obj X).homology₀ε R
  rw [← cancel_epi (((TopCat.toSSet.obj X).chainComplex R).homologyπ 0),
    HomologicalComplex.homologyπ_naturality_assoc]
  rw [← cancel_epi (((TopCat.toSSet.obj X).chainComplex R).cycles₀Iso.inv)]
  apply SSet.chainComplex_hom_ext
  intro x
  simp only [← Category.assoc]
  rw [show (TopCat.toSSet.obj X).ιChainComplex x ≫
      ((TopCat.toSSet.obj X).chainComplex R).cycles₀Iso.inv =
      ((TopCat.toSSet.obj X).chainComplex R).liftCycles
        ((TopCat.toSSet.obj X).ιChainComplex x) 0 (by simp) (by simp) by
      rw [← cancel_mono (((TopCat.toSSet.obj X).chainComplex R).cycles₀Iso.hom)]
      simp]
  simp [SSet.homology₀ε]

end TopCat

namespace SphereSixComplex

/-- The canonical augmentation basis for degree-zero integral homology of a path-connected
space. -/
public noncomputable def pathConnectedIntegralHomologyZeroEquivInteger
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    IntegralSingularHomology 0 X ≃+ ℤ :=
  (asIso ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv

/-- Naturality of the canonical path-connected `H₀ ≃ ℤ` basis under a continuous map. -/
public theorem pathConnectedIntegralHomologyZeroEquivInteger_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y))
    (x : IntegralSingularHomology 0 X) :
    pathConnectedIntegralHomologyZeroEquivInteger Y
        (integralSingularHomologyMap 0 f x) =
      pathConnectedIntegralHomologyZeroEquivInteger X x :=
  ConcreteCategory.congr_hom
    (TopCat.singularHomology₀ε_naturality (TopCat.ofHom f) (AddCommGrpCat.of ℤ)) x

/-- A map from a path-connected space induces an injective map on degree-zero homology. -/
public theorem integralSingularHomologyMap_zero_injective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (f : C(X, Y)) :
    Function.Injective (integralSingularHomologyMap 0 f) := by
  intro x y h
  apply (pathConnectedIntegralHomologyZeroEquivInteger X).injective
  have hn := TopCat.singularHomology₀ε_naturality (TopCat.ofHom f) (AddCommGrpCat.of ℤ)
  have hx := ConcreteCategory.congr_hom hn x
  have hy := ConcreteCategory.congr_hom hn y
  exact hx.symm.trans ((congrArg ((TopCat.of Y).singularHomology₀ε
    (AddCommGrpCat.of ℤ)) h).trans hy)

namespace IntegralMayerVietoris

variable {X : Type} [TopologicalSpace X] (A B : Set X)
  [PathConnectedSpace (A ∩ B : Set X)]

/-- A connected overlap makes the degree-zero difference map injective. -/
public theorem differenceMap_zero_injective : Function.Injective (differenceMap A B 0) := by
  intro x y h
  exact integralSingularHomologyMap_zero_injective (interToLeft A B) (congrArg Prod.fst h)

end IntegralMayerVietoris

end SphereSixComplex
