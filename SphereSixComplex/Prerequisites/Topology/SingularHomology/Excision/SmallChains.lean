module

public import Mathlib.Algebra.Homology.QuasiIso
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.SimplexCoordinates
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.Relative
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Small singular chains for excision

For a family of subsets, the small singular subcomplex consists of simplices factoring
through a member of the family. Its integral chain complex has a canonical inclusion
into the full singular chain complex.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

section SmallChains

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The categorical inclusion of a topological subspace. -/
public noncomputable def topologicalSubsetInclusion (s : Set X) :
    TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Singular simplices which factor through one member of `U`. -/
public noncomputable def coverSmallSingularSubcomplex :
    (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ j, SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))


/-- Integral chains on the cover-small singular simplicial set. -/
public noncomputable abbrev coverSmallIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (AddCommGrpCat.of ℤ)

/-- Inclusion of cover-small integral singular chains into all integral singular chains. -/
public noncomputable def coverSmallIntegralSingularChainInclusion :
    coverSmallIntegralSingularChainComplex X U ⟶ integralSingularChainComplexObj X :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (AddCommGrpCat.of ℤ)


/-- A subspace equal to the whole space is homeomorphic to the ambient space by its inclusion. -/
public noncomputable def topologicalSubsetHomeomorphOfEqUniv
    (s : Set X) (hs : s = Set.univ) : s ≃ₜ X :=
  (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ X)


end SmallChains

end SphereSixComplex
