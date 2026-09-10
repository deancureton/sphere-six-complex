module

public import SphereSixComplex.Topology.RelativeSingularHomotopy
public import SphereSixComplex.Topology.ClosedPrismHomology

@[expose] public section
noncomputable section
open CategoryTheory HomologicalComplex MonoidalCategory
namespace SphereSixComplex

public theorem relativeClosedPrismHomology_projection
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y} [Mono i]
    {f : CWTopologicalPairMap i j}
    (H : TopCat.Homotopy f.left f.left) (K : TopCat.Homotopy f.right f.right)
    (h : i ▷ TopCat.I ≫ K.h = H.h ≫ j) (n : ℕ) :
    homologyMap (cwRelativeIntegralSingularChainProjection i) (n + 1) ≫
      closedPrismHomology (cwRelativeSingularHomotopy H K h) n =
    closedPrismHomology (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)) n ≫
      homologyMap (cwRelativeIntegralSingularChainProjection j) (n + 2) := by
  apply closedPrismHomology_naturality
  exact cwRelativeSingularHomotopy_projection H K h

end SphereSixComplex
