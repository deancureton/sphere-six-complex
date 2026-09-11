module

public import SphereSixComplex.Prerequisites.Topology.SingularExcision
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projective reduction for the small-chain theorem

Integral simplicial chain groups are free abelian and hence projective.  Consequently, for the
nonnegatively graded singular chain complexes used by the excision development, it is enough to
prove that the cover-small inclusion is a quasi-isomorphism: projectivity upgrades it to the
chain-homotopy equivalence packaged by `CoverSmallChainApproximation`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Simplicial

namespace SphereSixComplex

/-- The homological form of the small-chain theorem: the cover-small inclusion induces an
isomorphism on homology in every degree. -/
public def CoverSmallChainQuasiIsomorphism
    {i : Type} (X : TopCat) (U : i → Set X) : Prop :=
  QuasiIso (coverSmallIntegralSingularChainInclusion X U)




end SphereSixComplex
