module

public import SphereSixComplex.Prerequisites.Topology.Sphere.HomologyZero
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Integral singular chains and induced chain maps -/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- Integral singular chains of a categorical topological space. -/
public abbrev integralSingularChainComplexObj (X : TopCat) :
    ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X


end SphereSixComplex
