module

public import SphereSixComplex.Prerequisites.Geometry.ComplexThreefold
public import SphereSixComplex.Prerequisites.Geometry.Gluing

/-!
# Complex threefolds obtained by gluing

A finite connected gluing with a compatible complex atlas is a compact complex threefold
when the glued space is compact, Hausdorff, and second countable.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- A compact connected gluing with compatible complex atlases is a complex threefold. -/
@[expose] public noncomputable def complexThreefoldOfGluing (D : TopCat.GlueData)
    [Finite D.J] [Nonempty D.J] [∀ i, Nonempty (D.U i)]
    [∀ i, ConnectedSpace (D.U i)]
    [∀ i, ChartedSpace ComplexModel (D.U i)]
    [T2Space (GluedSpace D)] [SecondCountableTopology (GluedSpace D)]
    (hcomplex : GluingAtlasCompatible
      (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) D)
    (hcompact : CompactSpace (GluedSpace D))
    (hconnected : GluingIntersectionGraphConnected D) : ComplexThreefold where
  Carrier := GluedSpace D
  topology := inferInstance
  charts := gluedChartedSpace D
  manifold := isManifold_gluedChartedSpace D hcomplex
  compact := hcompact
  connected := connectedSpace_gluedSpace D hconnected
  t2 := inferInstance
  secondCountable := inferInstance

end

end SphereSixComplex
