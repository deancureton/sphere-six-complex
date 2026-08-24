module

public import SphereSixComplex.Construction
public import SphereSixComplex.Geometry.Gluing

/-!
# Complex threefolds obtained by gluing

This file connects the generic topological gluing construction to the exact complex-threefold
contract used by the main theorem.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- A finite connected gluing of compact complex pieces, with compatible complex and underlying
real atlases, supplies the precise compact complex-threefold object used by the construction. -/
@[expose] public noncomputable def complexThreefoldOfGluing (D : TopCat.GlueData)
    [Finite D.J] [Nonempty D.J] [∀ i, Nonempty (D.U i)]
    [∀ i, ConnectedSpace (D.U i)]
    [∀ i, ChartedSpace ComplexModel (D.U i)]
    [T2Space (GluedSpace D)] [SecondCountableTopology (GluedSpace D)]
    (hcomplex : GluingAtlasCompatible
      (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) D)
    (hreal : @IsManifold ℝ inferInstance RealModel inferInstance inferInstance RealModel
      inferInstance (modelWithCornersSelf ℝ RealModel) ∞ (GluedSpace D) inferInstance
      (underlyingRealChartedSpace (gluedChartedSpace D)))
    (hcompact : CompactSpace (GluedSpace D))
    (hconnected : GluingIntersectionGraphConnected D) : ComplexThreefold where
  Carrier := GluedSpace D
  topology := inferInstance
  charts := gluedChartedSpace D
  manifold := isManifold_gluedChartedSpace D hcomplex
  realManifold := hreal
  compact := hcompact
  connected := connectedSpace_gluedSpace D hconnected
  t2 := inferInstance
  secondCountable := inferInstance

end

end SphereSixComplex
