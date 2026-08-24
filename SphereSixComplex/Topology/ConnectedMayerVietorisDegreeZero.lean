module

public import SphereSixComplex.Topology.MayerVietoris
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Degree-zero Mayer--Vietoris maps for connected spaces

The singular-homology augmentation in degree zero is natural.  Consequently, in the canonical
augmentation bases `H₀ ≃ ℤ`, the signed Mayer--Vietoris map of three path-connected spaces is the
integer antidiagonal `x ↦ (x, -x)`.
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

/-- The signed integer antidiagonal. -/
public def integerAntidiagonal : ℤ →+ ℤ × ℤ :=
  (AddMonoidHom.id ℤ).prod (-(AddMonoidHom.id ℤ))

public theorem integerAntidiagonal_injective : Function.Injective integerAntidiagonal := by
  intro x y h
  exact congrArg Prod.fst h

namespace IntegralMayerVietoris

variable {X : Type} [TopologicalSpace X] (A B : Set X)
  [PathConnectedSpace A] [PathConnectedSpace B]
  [PathConnectedSpace (A ∩ B : Set X)]

/-- Pointwise degree-zero normal form: the actual inclusion-induced difference map is
`x ↦ (x, -x)` in the canonical augmentation bases. -/
public theorem differenceMap_zero_apply_normalForm
    (x : IntegralSingularHomology 0 (A ∩ B : Set X)) :
    ((pathConnectedIntegralHomologyZeroEquivInteger A).prodCongr
      (pathConnectedIntegralHomologyZeroEquivInteger B))
        (differenceMap A B 0 x) =
      (pathConnectedIntegralHomologyZeroEquivInteger (A ∩ B : Set X) x,
        -pathConnectedIntegralHomologyZeroEquivInteger (A ∩ B : Set X) x) := by
  apply Prod.ext
  · exact pathConnectedIntegralHomologyZeroEquivInteger_naturality
      (interToLeft A B) x
  · change pathConnectedIntegralHomologyZeroEquivInteger B
        (-(integralSingularHomologyMap 0 (interToRight A B)) x) = _
    rw [map_neg, pathConnectedIntegralHomologyZeroEquivInteger_naturality]

/-- Homomorphism-level normal form for the actual degree-zero Mayer--Vietoris difference map. -/
public theorem differenceMap_zero_normalForm :
    ((pathConnectedIntegralHomologyZeroEquivInteger A).prodCongr
      (pathConnectedIntegralHomologyZeroEquivInteger B)).toAddMonoidHom.comp
        (differenceMap A B 0) =
      integerAntidiagonal.comp
        (pathConnectedIntegralHomologyZeroEquivInteger
          (A ∩ B : Set X)).toAddMonoidHom := by
  ext x
  · exact pathConnectedIntegralHomologyZeroEquivInteger_naturality
      (interToLeft A B) x
  · change pathConnectedIntegralHomologyZeroEquivInteger B
        (-(integralSingularHomologyMap 0 (interToRight A B)) x) = _
    rw [map_neg, pathConnectedIntegralHomologyZeroEquivInteger_naturality]
    rfl

/-- In particular, the actual degree-zero difference map is injective. -/
public theorem differenceMap_zero_injective : Function.Injective (differenceMap A B 0) := by
  intro x y h
  apply (pathConnectedIntegralHomologyZeroEquivInteger
    (A ∩ B : Set X)).injective
  have h' := congrArg
    (((pathConnectedIntegralHomologyZeroEquivInteger A).prodCongr
      (pathConnectedIntegralHomologyZeroEquivInteger B))) h
  have h'' :
      (pathConnectedIntegralHomologyZeroEquivInteger (A ∩ B : Set X) x,
        -pathConnectedIntegralHomologyZeroEquivInteger (A ∩ B : Set X) x) =
      (pathConnectedIntegralHomologyZeroEquivInteger (A ∩ B : Set X) y,
        -pathConnectedIntegralHomologyZeroEquivInteger (A ∩ B : Set X) y) := by
    simpa only [differenceMap_zero_apply_normalForm A B] using h'
  exact congrArg Prod.fst h''

end IntegralMayerVietoris

end SphereSixComplex
