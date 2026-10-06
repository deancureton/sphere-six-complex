module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.ULift

@[expose] public section

/-! # Integral singular homology on the pinned actual chain complex

The coefficient lift only places the integers in the space's universe.
The chains, differentials, homology and induced maps are Mathlib's singular
ones. No homology computation or Hurewicz/duality law is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- The integers, lifted only to match the universe of the singular simplices. -/
abbrev integralSingularCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

/-- The actual integral singular chain complex, with its original alternating
face differential. -/
abbrev integralSingularChains (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).obj (TopCat.of X)

/-- Actual integral singular homology, as a module over the integers. -/
abbrev integralSingularHomology (n : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℤ :=
  (integralSingularChains X).homology n

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The homology map induced by the original continuous target map. -/
def integralSingularHomologyMap (n : ℕ) (f : C(X, Y)) :
    integralSingularHomology n X →ₗ[ℤ] integralSingularHomology n Y :=
  (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map
    (TopCat.ofHom f)).hom

/-- Identity on the actual space induces identity on its actual singular homology. -/
theorem integralSingularHomologyMap_id (n : ℕ) :
    integralSingularHomologyMap n (.id X) = LinearMap.id :=
  congrArg ModuleCat.Hom.hom
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map_id
      (TopCat.of X))

/-- The original composition law holds on the actual integral homology maps. -/
theorem integralSingularHomologyMap_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularHomologyMap n (g.comp f) =
      (integralSingularHomologyMap n g).comp (integralSingularHomologyMap n f) :=
  congrArg ModuleCat.Hom.hom
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj integralSingularCoefficients).map_comp
      (TopCat.ofHom f) (TopCat.ofHom g))

/-- Homotopy invariance uses the original continuous homotopy and Mathlib's
proved singular chain homotopy, including the original parametrization. -/
theorem integralSingularHomologyMap_homotopic (n : ℕ) {f g : C(X, Y)} (h : f.Homotopic g) :
    integralSingularHomologyMap n f = integralSingularHomologyMap n g := by
  obtain ⟨H⟩ := h
  exact congrArg ModuleCat.Hom.hom
    (@TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (ModuleCat.{u} ℤ)
      _ _ _ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) (TopCat.ofHom g) _ H
        integralSingularCoefficients n)

/-- The original augmentation identifies H0 of every path-connected space
with the integers, without requiring a manifold hypothesis. -/
def integralSingularHomologyZeroEquiv [PathConnectedSpace X] :
    integralSingularHomology 0 X ≃ₗ[ℤ] ℤ :=
  (asIso ((TopCat.of X).singularHomology₀ε integralSingularCoefficients)).toLinearEquiv.trans
    ULift.moduleEquiv

end DifferentialGeometry.Topology
