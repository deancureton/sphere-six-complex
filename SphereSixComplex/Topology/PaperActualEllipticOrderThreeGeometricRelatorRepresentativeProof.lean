module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeMarkedPeriodRepresentativeProof

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- A literal global loop representing the geometric order-three meridian-cube relator with its
marked `epsilon`-period contribution. -/
public noncomputable def orderThreeActualCuspGeometricRelatorPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.orderThreeActualCuspMarkedEpsilonPeriodPath.trans
    A.orderThreeActualCuspZeroSectionTriplePath

/-- The explicit global representative has the expected geometric product class. -/
public theorem orderThreeActualCuspGeometricRelatorPath_class :
    Path.Homotopic.Quotient.mk A.orderThreeActualCuspGeometricRelatorPath =
      A.geometricCentralRhoOne ^ 3 *
        Additive.toMul (A.geometricCentralTranslation epsilon) := by
  rw [orderThreeActualCuspGeometricRelatorPath,
    Path.Homotopic.Quotient.mk_trans,
    A.orderThreeActualCuspZeroSectionTriplePath_class,
    A.orderThreeActualCuspMarkedEpsilonPeriodPath_class]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
