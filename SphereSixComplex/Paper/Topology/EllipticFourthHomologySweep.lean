module

public import SphereSixComplex.Paper.Topology.EllipticFillingHomology
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthInteriorTranslation
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex.Topology CircleProductIdentityMappingTorus Hurewicz.Chains

public def ellipticFourthHomologySweep (A : AnalyticData) :
    IntegralSingularHomology 1 A.ellipticInterior →+
      IntegralSingularHomology 2 A.ellipticInterior :=
  (integralSingularHomologyMap 2 A.ellipticFourthTranslation).comp (normalizedCircleCross 1)

end SphereSixComplex.Geometry.AnalyticData
