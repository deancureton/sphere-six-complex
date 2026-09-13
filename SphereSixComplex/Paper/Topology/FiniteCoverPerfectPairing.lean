module

public import SphereSixComplex.Paper.Topology.AffineCyclicCoverDegreeTwoInvariance
public import Mathlib.LinearAlgebra.Dual.Basis

/-! # Projected coordinate tori in the elliptic fibers -/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix

namespace SphereSixComplex.Topology.FiniteCoverPerfectPairing

open EllipticFilling AffineCyclicQuotientHomology

variable {U : Periods.TriangleUniformization} (F : Periods.PeriodFunctions U)

/-- The projected standard generators used to specify the order-three quotient homology basis. -/
public noncomputable def orderThreeProjectedDegreeTwoGenerator (j : Fin 6) :
    IntegralSingularHomology 2 (orderThreeReducedCentralFiber F) :=
  integralSingularHomologyMap 2
    (RadialEllipticActionData.centralFiberCoverProjection (orderThreeRadialActionData F))
    ((orderThreeCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm (Pi.single j 1))

/-- The projected standard generators used to specify the order-four quotient homology basis. -/
public noncomputable def orderFourProjectedDegreeTwoGenerator (j : Fin 6) :
    IntegralSingularHomology 2 (orderFourReducedCentralFiber F) :=
  integralSingularHomologyMap 2
    (RadialEllipticActionData.centralFiberCoverProjection (orderFourRadialActionData F))
    ((orderFourCentralFiberCoverSourceHomologyBasis F).degreeTwo.symm (Pi.single j 1))

end SphereSixComplex.Topology.FiniteCoverPerfectPairing
