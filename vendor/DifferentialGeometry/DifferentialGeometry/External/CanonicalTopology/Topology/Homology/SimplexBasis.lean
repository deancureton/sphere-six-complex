module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic

@[expose] public section

/-! # The actual singular simplices form a basis of the actual chain groups -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

/-- The actual simplices in the pinned singular simplicial set. -/
abbrev integralSingularSimplex (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)

/-- These are exactly continuous maps from the original barycentric simplex. -/
def integralSingularSimplexEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularSimplex n X ≃ C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)

/-- Identify the actual categorical coproduct chain group with the explicit
finite formal sums of its same actual simplices. -/
def integralSingularChainFinsuppIso (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X n ≅
      ModuleCat.of ℤ (integralSingularSimplex n X →₀ ULift.{u} ℤ) :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
    integralSingularCoefficients n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (integralSingularSimplex n X))

/-- Integral coordinates of an actual singular chain, with the coefficient
universe lift removed by its actual linear equivalence. -/
def integralSingularChainRepr (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X n ≃ₗ[ℤ] (integralSingularSimplex n X →₀ ℤ) :=
  (integralSingularChainFinsuppIso n X).toLinearEquiv.trans
    (Finsupp.mapRange.linearEquiv ULift.moduleEquiv)

/-- The basis is indexed by the actual singular simplices, rather than a
postulated freely generated replacement for the original chain group. -/
def integralSingularChainBasis (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Basis (integralSingularSimplex n X) ℤ ((integralSingularChains X).X n) :=
  Basis.ofRepr (integralSingularChainRepr n X)

/-- Freeness of each original chain group has the preceding explicit basis. -/
instance integralSingularChain_free (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Module.Free ℤ ((integralSingularChains X).X n) :=
  Module.Free.of_basis (integralSingularChainBasis n X)

/-- In particular the original chain groups are projective, as needed for
the integral universal coefficient argument. -/
instance integralSingularChain_projective (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Projective ((integralSingularChains X).X n) :=
  ModuleCat.projective_of_free (integralSingularChainBasis n X)

end DifferentialGeometry.Topology
