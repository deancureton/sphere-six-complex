module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorNormalClosureTypes
public import SphereSixComplex.Paper.Topology.PaperEllipticSynchronizedPeriodTransport

@[expose] public section

namespace SphereSixComplex.Geometry.PaperAnalyticData

public theorem ellipticRelatorMembership_nonempty (A : PaperAnalyticData) :
    Nonempty (A.EllipticRelatorMembership A.cuspCentralNaturality) :=
  A.ellipticRelatorMembership_proved

end SphereSixComplex.Geometry.PaperAnalyticData
