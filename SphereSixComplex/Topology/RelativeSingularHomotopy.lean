module

public import SphereSixComplex.Topology.SingularPrismNaturality
public import SphereSixComplex.Topology.QuotientChainHomotopy
public import SphereSixComplex.Topology.CellularHomologyClassicalBoundary

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SphereSixComplex

public def cwRelativeSingularHomotopy
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y} [Mono i]
    {f g : CWTopologicalPairMap i j}
    (H : TopCat.Homotopy f.left g.left) (K : TopCat.Homotopy f.right g.right)
    (h : i ▷ TopCat.I ≫ K.h = H.h ≫ j) :
    Homotopy (cwRelativeIntegralSingularChainMapOfPair f)
      (cwRelativeIntegralSingularChainMapOfPair g) := by
  apply quotientChainHomotopy (cwRelativeIntegralSingularShortComplex i)
    (cwRelativeIntegralSingularShortComplex j)
    (cwRelativeIntegralSingularShortComplex_shortExact i)
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ))
  · intro p q
    change (cwIntegralSingularChainMapObj i).f p ≫
      (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)).hom p q ≫
        (cwRelativeIntegralSingularChainProjection j).f q = 0
    have hn := topologicalPrism_naturality H K i j h (AddCommGrpCat.of ℤ) p q
    change (cwIntegralSingularChainMapObj i).f p ≫ _ =
      _ ≫ (cwIntegralSingularChainMapObj j).f q at hn
    rw [← Category.assoc, hn, Category.assoc]
    have hz := congrArg (fun k ↦ k.f q)
      (cwRelativeIntegralSingularShortComplex j).zero
    change (cwIntegralSingularChainMapObj j).f q ≫
      (cwRelativeIntegralSingularChainProjection j).f q = 0 at hz
    rw [hz, comp_zero]
  · exact cokernel.π_desc _ _ _
  · exact cokernel.π_desc _ _ _

public theorem cwRelativeSingularHomotopy_projection
    {A X B Y : TopCat} {i : A ⟶ X} {j : B ⟶ Y} [Mono i]
    {f g : CWTopologicalPairMap i j}
    (H : TopCat.Homotopy f.left g.left) (K : TopCat.Homotopy f.right g.right)
    (h : i ▷ TopCat.I ≫ K.h = H.h ≫ j) (p q : ℕ) :
    (cwRelativeIntegralSingularChainProjection i).f p ≫
      (cwRelativeSingularHomotopy H K h).hom p q =
    (K.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)).hom p q ≫
      (cwRelativeIntegralSingularChainProjection j).f q := by
  exact quotientChainHomotopyComponent_projection _ _
    (cwRelativeIntegralSingularShortComplex_shortExact i) _ _ _ _

end SphereSixComplex
