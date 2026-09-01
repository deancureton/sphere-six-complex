module

public import SphereSixComplex.Topology.HomologySphere
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Integral singular cohomology

Integral singular cohomology is defined from the dual of Mathlib's integral singular chain
complex.  No classical topology theorem is used in this construction.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory

namespace SphereSixComplex

/-- The integral singular chain complex used to define cochains. -/
public abbrev IntegralSingularCochainSource (X : Type) [TopologicalSpace X] :
    ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

/-- The integral singular `n`-cochains of a space. -/
public abbrev IntegralSingularCochains (n : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  (IntegralSingularCochainSource X).X n →+ ℤ

/-- The singular coboundary is precomposition with the singular boundary. -/
public def integralSingularCoboundary (X : Type) [TopologicalSpace X] (n : ℕ) :
    IntegralSingularCochains n X →+
      IntegralSingularCochains (n + 1) X where
  toFun f := f.comp (ConcreteCategory.hom
    ((IntegralSingularCochainSource X).d (n + 1) n))
  map_zero' := rfl
  map_add' _ _ := rfl

public theorem integralSingularCoboundary_comp_zero
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    AddCommGrpCat.ofHom (integralSingularCoboundary X n) ≫
        AddCommGrpCat.ofHom (integralSingularCoboundary X (n + 1)) = 0 := by
  ext f x
  change (integralSingularCoboundary X (n + 1)
    (integralSingularCoboundary X n f)) x = 0
  simp only [integralSingularCoboundary]
  change f (((IntegralSingularCochainSource X).d (n + 2) (n + 1) ≫
    (IntegralSingularCochainSource X).d (n + 1) n) x) = 0
  rw [(IntegralSingularCochainSource X).d_comp_d]
  simp

/-- The integral singular cochain complex, obtained by applying `Hom(-, ℤ)` degreewise to the
integral singular chain complex. -/
public def integralSingularCochainComplex (X : Type) [TopologicalSpace X] :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of
    (fun n ↦ AddCommGrpCat.of (IntegralSingularCochains n X))
    (fun n ↦ AddCommGrpCat.ofHom (integralSingularCoboundary X n))
    (integralSingularCoboundary_comp_zero X)

/-- Integral singular cohomology in degree `n`. -/
public abbrev IntegralSingularCohomology (n : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  (integralSingularCochainComplex X).homology n

end SphereSixComplex

end

end
