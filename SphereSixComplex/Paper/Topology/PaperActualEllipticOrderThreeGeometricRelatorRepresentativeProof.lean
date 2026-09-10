module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeMarkedPeriodRepresentativeProof

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

/-- A literal global loop representing the geometric order-three meridian-cube relator with its
marked `epsilon`-period contribution. -/
public noncomputable def ellipticThreeCuspGeometricRelatorPath :
    Path A.cuspCentralBase A.cuspCentralBase :=
  A.ellipticThreeCuspMarkedEpsilonPeriodPath.trans
    A.ellipticThreeCuspZeroSectionTriplePath

/-- The explicit global representative has the expected geometric product class. -/
public theorem ellipticThreeCuspGeometricRelatorPath_class :
    Path.Homotopic.Quotient.mk A.ellipticThreeCuspGeometricRelatorPath =
      A.geometricCentralRhoOne ^ 3 *
        Additive.toMul (A.geometricCentralTranslation epsilon) := by
  rw [ellipticThreeCuspGeometricRelatorPath,
    Path.Homotopic.Quotient.mk_trans,
    A.ellipticThreeCuspZeroSectionTriplePath_class,
    A.ellipticThreeCuspMarkedEpsilonPeriodPath_class]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
