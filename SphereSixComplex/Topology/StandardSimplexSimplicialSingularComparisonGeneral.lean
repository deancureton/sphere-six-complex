module

public import SphereSixComplex.Topology.StandardSimplexSimplicialSingularComparison

/-!
# Simplicial--singular comparison for a standard simplex with arbitrary coefficients

The coefficient-general results live in
`StandardSimplexSimplicialSingularComparison`; this module is retained as a compatibility import.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-! The suffixed declarations were part of the original public API of this compatibility module.
Keep them as thin aliases while the unsuffixed declarations now live in the main module. -/

public theorem simplicialHomologyZeroAugmentation_naturality_general
    {X Y : SSet.{0}} (f : X ⟶ Y) (R : AddCommGrpCat) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R :=
  simplicialHomologyZeroAugmentation_naturality f R

public theorem standardSimplex_simplicialChains_exactAt_general
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((Δ[n] : SSet.{0}).chainComplex R).ExactAt k :=
  standardSimplex_simplicialChains_exactAt R n k hk

public theorem standardSimplexRealization_singularChains_exactAt_general
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).chainComplex R).ExactAt k :=
  standardSimplexRealization_singularChains_exactAt R n k hk

public theorem standardSimplex_simplicialToRealizationSingularChainMap_quasiIso_general
    (R : AddCommGrpCat) (n : ℕ) :
    QuasiIso (simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R) :=
  standardSimplex_simplicialToRealizationSingularChainMap_quasiIso R n

end SphereSixComplex

end
