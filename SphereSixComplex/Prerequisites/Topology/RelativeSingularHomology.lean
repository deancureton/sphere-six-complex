module

public import SphereSixComplex.Prerequisites.Topology.StandardSphereHomologyZeroCore
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Relative integral singular homology as a cokernel complex

For a morphism of spaces, this file defines the relative integral singular chain complex to be the
categorical cokernel of the induced singular-chain map.  For a monomorphism of spaces, singular
chains preserve the monomorphism, so the absolute chains, ambient chains, and relative chains form
a short exact sequence.  Mathlib's snake-lemma construction then supplies the connecting maps and
the three exact pieces of the associated long homology sequence.

The construction is specialized to `S⁶ = ∂D⁷ ⟶ D⁷`.  Contractibility of the disk makes the
connecting map from positive-degree relative homology to sphere homology an isomorphism.  What
remains unavailable is excision or a cellular/relative-chain calculation identifying
`Hₖ(D⁷,S⁶;ℤ)` with `ℤ` in degree seven and zero otherwise.
-/

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

/-- Relative integral singular chains, defined as the cokernel of the subspace chain map. -/
public noncomputable def relativeIntegralSingularChainComplex {X Y : TopCat} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (integralSingularChainMapObj i)

/-- The quotient map from ambient singular chains to relative singular chains. -/
public noncomputable def relativeIntegralSingularChainProjection {X Y : TopCat} (i : X ⟶ Y) :
    integralSingularChainComplexObj Y ⟶ relativeIntegralSingularChainComplex i :=
  cokernel.π (integralSingularChainMapObj i)

/-- The canonical short complex of subspace, ambient, and relative singular chains. -/
public noncomputable def relativeIntegralSingularShortComplex {X Y : TopCat} (i : X ⟶ Y) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (integralSingularChainMapObj i)
    (relativeIntegralSingularChainProjection i)
    (cokernel.condition (integralSingularChainMapObj i))

/-- For a monomorphism of spaces, the relative singular-chain short complex is short exact. -/
public theorem relativeIntegralSingularShortComplex_shortExact
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] :
    (relativeIntegralSingularShortComplex i).ShortExact := by
  let _ : Mono (integralSingularChainMapObj i) := by
    dsimp [integralSingularChainMapObj]
    infer_instance
  exact
    { exact := ShortComplex.exact_cokernel (integralSingularChainMapObj i)
      mono_f := by
        dsimp [relativeIntegralSingularShortComplex]
        infer_instance
      epi_g := by
        dsimp [relativeIntegralSingularShortComplex,
          relativeIntegralSingularChainProjection]
        constructor
        intro Z g h w
        exact Cofork.IsColimit.hom_ext
          (cokernelIsCokernel (integralSingularChainMapObj i)) w }








end SphereSixComplex
