module

public import SphereSixComplex.Paper.Topology.AffineVanKampenTransport
public import SphereSixComplex.Paper.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Paper.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Paper.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorNormalClosure

/-!
# Actual affine filling-cover models for the paper star

The three regular cover squares are based on the actual overlaps and filling pieces of the
four-piece star. Their deck kernels feed the source-independent based van Kampen bridge; the
paper's final affine relations and generation are then proved consequences.

The bundled cover-square API remains available for intermediate geometric work.  The production
van Kampen theorem uses the smaller connector-invariant normal-closure bridge directly.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover

variable (A : PaperAnalyticData)

/-- The established analytic choices give a complete van Kampen witness for their actual star. -/
public theorem actualStarHasVanKampenData :
    Topology.HasVanKampenData A.VanKampenSpace 0 1 (-1) :=
  A.ellipticRelatorMembership_nonempty.elim fun R ↦
    R.hasVanKampenData

end SphereSixComplex.Geometry.PaperAnalyticData

end
