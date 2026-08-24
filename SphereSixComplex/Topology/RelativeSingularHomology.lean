module

public import SphereSixComplex.Topology.StandardSphereHomologyZero
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
public abbrev IntegralSingularChainComplexObj (X : TopCat) :
    ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X

/-- The singular-chain map induced by a morphism of categorical topological spaces. -/
public noncomputable def integralSingularChainMapObj {X Y : TopCat} (i : X ⟶ Y) :
    IntegralSingularChainComplexObj X ⟶ IntegralSingularChainComplexObj Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map i

/-- Relative integral singular chains, defined as the cokernel of the subspace chain map. -/
public noncomputable def RelativeIntegralSingularChainComplex {X Y : TopCat} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (integralSingularChainMapObj i)

/-- The quotient map from ambient singular chains to relative singular chains. -/
public noncomputable def relativeIntegralSingularChainProjection {X Y : TopCat} (i : X ⟶ Y) :
    IntegralSingularChainComplexObj Y ⟶ RelativeIntegralSingularChainComplex i :=
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

/-- The connecting map from relative homology in degree `n+1` to subspace homology in degree `n`. -/
public noncomputable def relativeIntegralSingularBoundary
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (RelativeIntegralSingularChainComplex i).homology (n + 1) ⟶
      (IntegralSingularChainComplexObj X).homology n :=
  (relativeIntegralSingularShortComplex_shortExact i).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by omega))

/-- Exactness at ambient homology: subspace homology maps to ambient homology and then relative
homology. -/
public theorem relativeIntegralSingular_homology_exact_ambient
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (integralSingularChainMapObj i) n)
      (HomologicalComplex.homologyMap (relativeIntegralSingularChainProjection i) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap
          (integralSingularChainMapObj i ≫
            cokernel.π (integralSingularChainMapObj i)) n = 0
        rw [cokernel.condition, HomologicalComplex.homologyMap_zero])).Exact :=
  (relativeIntegralSingularShortComplex_shortExact i).homology_exact₂ n

/-- Exactness at relative homology: ambient homology maps to relative homology and then to the
previous subspace degree. -/
public theorem relativeIntegralSingular_homology_exact_relative
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (relativeIntegralSingularChainProjection i) (n + 1))
      (relativeIntegralSingularBoundary i n)
      (by
        exact (relativeIntegralSingularShortComplex_shortExact i).comp_δ
          (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega)))).Exact :=
  (relativeIntegralSingularShortComplex_shortExact i).homology_exact₃
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))

/-- Exactness at subspace homology: the connecting map is followed by the map to ambient
homology. -/
public theorem relativeIntegralSingular_homology_exact_subspace
    {X Y : TopCat} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk
      (relativeIntegralSingularBoundary i n)
      (HomologicalComplex.homologyMap (integralSingularChainMapObj i) n)
      (by
        exact (relativeIntegralSingularShortComplex_shortExact i).δ_comp
          (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega)))).Exact :=
  (relativeIntegralSingularShortComplex_shortExact i).homology_exact₁
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))

/-- The relative integral singular chain complex of the pair `(D⁷,S⁶)`. -/
public noncomputable abbrev DiskSevenSphereSixRelativeIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  RelativeIntegralSingularChainComplex (TopCat.diskBoundaryInclusion 7)

/-- The short exact sequence of chains for `S⁶ ⟶ D⁷ ⟶ (D⁷,S⁶)`. -/
public theorem diskSevenSphereSix_relativeIntegralSingularShortComplex_shortExact :
    (relativeIntegralSingularShortComplex (TopCat.diskBoundaryInclusion 7)).ShortExact :=
  relativeIntegralSingularShortComplex_shortExact (TopCat.diskBoundaryInclusion 7)

/-- In positive sphere degrees, the boundary map identifies relative homology of `(D⁷,S⁶)` with
the preceding homology of `S⁶`, because both adjacent disk homology objects vanish. -/
public noncomputable def diskSevenSphereSix_relativeBoundaryIso
    (n : ℕ) (hn : n ≠ 0) :
    DiskSevenSphereSixRelativeIntegralSingularChainComplex.homology (n + 1) ≅
      (IntegralSingularChainComplexObj (TopCat.diskBoundary 7)).homology n :=
  diskSevenSphereSix_relativeIntegralSingularShortComplex_shortExact.δIso
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))
    (topCatDiskSeven_integralSingularHomology_isZero (n + 1) (by omega))
    (topCatDiskSeven_integralSingularHomology_isZero n hn)

end SphereSixComplex
