module

public import SphereSixComplex.Prerequisites.Topology.PuncturedPlane.PowerFactorization
public import SphereSixComplex.Elliptic.FundamentalGroup.Relators
public import SphereSixComplex.Elliptic.Band.MarkedDisc
public import SphereSixComplex.Periods.FuchsianModularLift.Ramification
public import SphereSixComplex.Prerequisites.Topology.Homotopy.FreeLoopProduct
public import SphereSixComplex.Prerequisites.Topology.SingularHomology.FreeLoop
public import SphereSixComplex.Elliptic.Sweep.FourthInteriorTranslation

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
