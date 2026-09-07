module

public import SphereSixComplex.Topology.PaperActualEllipticRelatorNormalClosureTypes
public import SphereSixComplex.Topology.PaperEllipticSynchronizedPeriodTransport

@[expose] public section

namespace SphereSixComplex.Geometry.PaperAnalyticData

public theorem establishedActualEllipticRelatorNormalClosureResidual (A : PaperAnalyticData) :
    Nonempty (A.ActualEllipticRelatorNormalClosureResidual A.actualCuspCentralNaturality) :=
  A.actualEllipticRelatorNormalClosureResidual_proved

end SphereSixComplex.Geometry.PaperAnalyticData
