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

/-- The singular-chain map induced by a morphism of categorical topological spaces. -/
public noncomputable def integralSingularChainMapObj {X Y : TopCat} (i : X ⟶ Y) :
    integralSingularChainComplexObj X ⟶ integralSingularChainComplexObj Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map i

end SphereSixComplex
