module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeFullProductCoordinateProof
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.ContinuousMap.Interval
public import Mathlib.Topology.ContinuousMap.Ordered

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap


namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex
open SphereSixComplex.Topology

variable (A : AnalyticData)

/-- The local offset-period factor of the punctured product splitting. -/
public noncomputable def orderThreeLocalOffsetFiberCentralPath :
    letI := A.ellipticThreeBoundaryAction
    Path A.ellipticThreeCentralBase A.ellipticThreeCentralBase := by
  let _ := A.ellipticThreeBoundaryAction
  exact (((Path.refl A.orderThreeCayleyPuncturedBasepoint).prod
    A.orderThreePrincipalGaugeWithOffsetPath).map
      A.orderThreePuncturedProductToCentralMap.continuous).cast
        A.ellipticThreeCentralBase_eq_puncturedProductBase
        A.ellipticThreeCentralBase_eq_puncturedProductBase

/-- The local base-circle factor, with its torus coordinate held fixed. -/
public noncomputable def orderThreeLocalOffsetBaseCentralPath :
    letI := A.ellipticThreeBoundaryAction
    Path A.ellipticThreeCentralBase A.ellipticThreeCentralBase := by
  let _ := A.ellipticThreeBoundaryAction
  exact ((A.orderThreeFillingRelationCayleyPuncturedLoop.prod
    (Path.refl (A.orderThreePrincipalGaugeWithOffsetPath 0))).map
      A.orderThreePuncturedProductToCentralMap.continuous).cast
        A.ellipticThreeCentralBase_eq_puncturedProductBase
        A.ellipticThreeCentralBase_eq_puncturedProductBase

public theorem orderThreeLocalFiberThenBaseCentralPath_eq_trans :
    letI := A.ellipticThreeBoundaryAction
    A.orderThreeLocalFiberThenBaseCentralPath =
      A.orderThreeLocalOffsetFiberCentralPath.trans
        A.orderThreeLocalOffsetBaseCentralPath := by
  let _ := A.ellipticThreeBoundaryAction
  unfold orderThreeLocalFiberThenBaseCentralPath
    orderThreeLocalOffsetFiberCentralPath orderThreeLocalOffsetBaseCentralPath
  rw [Path.map_trans]
  rfl


/-- The global zero-section triple displayed at the final affine basepoint. -/
public noncomputable def orderThreeCentralAffineZeroSectionTriplePath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.ellipticThreeCuspZeroSectionTriplePath.cast
    A.centralAffineBase_eq_cuspCentralBase
    A.centralAffineBase_eq_cuspCentralBase


end SphereSixComplex.Geometry.AnalyticData

end

end
