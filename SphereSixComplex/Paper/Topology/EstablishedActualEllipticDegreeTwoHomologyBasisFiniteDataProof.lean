module

public import SphereSixComplex.Paper.Topology.EllipticDegreeTwoBasisFromOrbitSweep

/-!
# The actual elliptic degree-two homology bases
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology.FiniteCoverPerfectPairing

open EllipticDegreeTwoBasisFromOrbitSweep
open Geometry Geometry.EllipticFamilySpecialization

/-- The primal finite calculation for the two elliptic cyclic quotients attached to the actual
paper data, derived from normalized finite-order mapping-torus orbit sweeps. -/
public theorem nonempty_actualEllipticDegreeTwoHomologyBasisFiniteData
    (A : AnalyticData) :
    Nonempty (EllipticDegreeTwoHomologyBasisFiniteData A.periods) :=
  actualEllipticDegreeTwoHomologyBasisFiniteData A.periods

end SphereSixComplex.Topology.FiniteCoverPerfectPairing

end

end
