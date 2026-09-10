module
public import SphereSixComplex.Paper.Topology.ActualEllipticFourthInteriorTranslation
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Paper.Topology.CuspEllipticHomologyFullIterate

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology CircleProductIdentityMappingTorus Hurewicz.Chains

public def ellipticFourthHomologySweep (A : PaperAnalyticData) :
    IntegralSingularHomology 1 A.ellipticInterior →+
      IntegralSingularHomology 2 A.ellipticInterior :=
  (integralSingularHomologyMap 2 A.ellipticFourthTranslation).comp (normalizedCircleCross 1)

public theorem ellipticFourthHomologySweep_fullIterate (A : PaperAnalyticData) :
    (12 : ℤ) • A.ellipticFourthHomologySweep
      (-integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase A.cuspAffineBridgeMeridian)) =
    A.ellipticFourthHomologySweep
      (integralSingularHomologyMap 1 A.cuspOverlapToEllipticInterior
        (hurewiczFunction A.cuspOverlapBase
          (Additive.toMul (A.cuspAffineBridgeTranslation
            (Pi.single (0 : Fin 4) 1))))) := by
  simpa only [map_zsmul] using congrArg A.ellipticFourthHomologySweep
    A.cuspOverlap_homology_fullIterate

end SphereSixComplex.Geometry.PaperAnalyticData
