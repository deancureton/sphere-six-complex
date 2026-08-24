module

public import SphereSixComplex.Geometry.ComplexThreefoldGluing
public import SphereSixComplex.Topology.FundamentalGroupComputation
public import SphereSixComplex.Topology.MayerVietoris

/-!
# Assembly of the completed paper threefold

This file connects the generic complex gluing, van Kampen presentation, and integral-homology
calculation to the exact `CompletedPaperThreefold` contract used by the final theorem.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- A finite complex gluing with the paper's verified van Kampen and integral-homology data
produces the exact completed-threefold object used by smooth recognition. -/
public noncomputable def completedPaperThreefoldOfGluing (D : TopCat.GlueData)
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
    (hconnected : GluingIntersectionGraphConnected D)
    (hvanKampen : Topology.HasVanKampenData (GluedSpace D) 0 1 (-1))
    (hhomology : HasIntegralHomologyOfSixSphere (GluedSpace D)) : CompletedPaperThreefold where
  X := complexThreefoldOfGluing D hcomplex hreal hcompact hconnected
  fundamentalGroup :=
    hvanKampen.hasVanKampenPresentation.hasPaperFundamentalGroup
  integralHomology := hhomology

/-- The assembled gluing supplies the simply connected integral-homology-sphere input required by
the remaining six-dimensional smooth-recognition theorem. -/
public theorem smoothRecognitionInputOfGluing (D : TopCat.GlueData)
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
    (hconnected : GluingIntersectionGraphConnected D)
    (hvanKampen : Topology.HasVanKampenData (GluedSpace D) 0 1 (-1))
    (hhomology : HasIntegralHomologyOfSixSphere (GluedSpace D)) :
    let P := completedPaperThreefoldOfGluing D hcomplex hreal hcompact hconnected hvanKampen
      hhomology
    letI := P.X.topology
    letI := underlyingRealChartedSpace P.X.charts
    SmoothSimplyConnectedIntegralHomologySixSphere P.X.Carrier := by
  exact (completedPaperThreefoldOfGluing D hcomplex hreal hcompact hconnected hvanKampen
    hhomology).smoothRecognitionInput

end

end SphereSixComplex
