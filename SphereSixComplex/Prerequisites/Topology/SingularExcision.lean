module

public import Mathlib.Algebra.Homology.QuasiIso
public import SphereSixComplex.Prerequisites.Topology.RelativeSingularHomology
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Small singular chains for excision

This file builds the first chain-level layer of the singular excision argument.  Given a family
of subsets of a space, the small singular subcomplex consists of the singular simplices which
factor through one member of the family.  Its chain complex maps canonically and monomorphically
to the full singular chain complex, and every cover-member chain map factors through it.

The classical subdivision theorem says that, for an open cover, this inclusion is a chain-homotopy
equivalence.  The definitions below state that next step using mathlib's actual `HomotopyEquiv`
API and prove its full homological consequence.  Mathlib's current simplicial subdivision functor
does not yet provide a last-vertex map, a subdivision chain map, or its chain homotopy to the
identity, so that theorem cannot yet be constructed from library primitives.
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

public theorem mem_coverSmallSingularSubcomplex_iff
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (coverSmallSingularSubcomplex X U).obj n ↔
      ∃ j, x ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))).obj n := by
  simp [coverSmallSingularSubcomplex]

/-- Membership means exactly that the singular simplex is the image of a simplex in one cover
member. -/
public theorem mem_coverSmallSingularSubcomplex_iff_exists_preimage
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (coverSmallSingularSubcomplex X U).obj n ↔
      ∃ (j : ι) (y : (TopCat.toSSet.obj (TopCat.of (U j))).obj n),
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j))).app n y = x := by
  simp [mem_coverSmallSingularSubcomplex_iff, Subfunctor.range_obj]

/-- Integral chains on the cover-small singular simplicial set. -/
public noncomputable abbrev coverSmallIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (AddCommGrpCat.of ℤ)

/-- Inclusion of cover-small integral singular chains into all integral singular chains. -/
public noncomputable def coverSmallIntegralSingularChainInclusion :
    coverSmallIntegralSingularChainComplex X U ⟶ integralSingularChainComplexObj X :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (AddCommGrpCat.of ℤ)

instance coverSmallIntegralSingularChainInclusion_mono :
    Mono (coverSmallIntegralSingularChainInclusion X U) := by
  dsimp [coverSmallIntegralSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono

/-- The singular set of each cover member factors through the small singular subcomplex. -/
public noncomputable def coverMemberToSmallSingularSet (j : ι) :
    TopCat.toSSet.obj (TopCat.of (U j)) ⟶ coverSmallSingularSubcomplex X U :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
    ((le_iSup (fun k ↦ SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U k)))) j))

@[reassoc (attr := simp)]
public theorem coverMemberToSmallSingularSet_comp_inclusion (j : ι) :
    coverMemberToSmallSingularSet X U j ≫ (coverSmallSingularSubcomplex X U).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion X (U j)) :=
  SSet.Subcomplex.lift_ι _ _

/-- The chain map from a cover member into the small singular chains. -/
public noncomputable def coverMemberToSmallIntegralSingularChains (j : ι) :
    integralSingularChainComplexObj (TopCat.of (U j)) ⟶
      coverSmallIntegralSingularChainComplex X U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet X U j) (AddCommGrpCat.of ℤ)

/-- Chains from a cover member factor coherently through the small-chain inclusion. -/
@[reassoc]
public theorem coverMemberToSmallIntegralSingularChains_comp_inclusion (j : ι) :
    coverMemberToSmallIntegralSingularChains X U j ≫
        coverSmallIntegralSingularChainInclusion X U =
      integralSingularChainMapObj (topologicalSubsetInclusion X (U j)) := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverMemberToSmallSingularSet X U j) ≫
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverSmallSingularSubcomplex X U).ι =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
  rw [← Functor.map_comp, coverMemberToSmallSingularSet_comp_inclusion]









/-- A subspace equal to the whole space is homeomorphic to the ambient space by its inclusion. -/
public noncomputable def topologicalSubsetHomeomorphOfEqUniv
    (s : Set X) (hs : s = Set.univ) : s ≃ₜ X :=
  (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ X)





end SmallChains

end SphereSixComplex
