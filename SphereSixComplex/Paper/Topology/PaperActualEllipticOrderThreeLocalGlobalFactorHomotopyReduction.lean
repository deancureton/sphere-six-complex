module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeFullProductCoordinateProof
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomotopyComposition

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap



namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology

variable (A : PaperAnalyticData)

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

/-- The corrected cusp period displayed at the final affine basepoint. -/
public noncomputable def orderThreeCentralAffineCorrectedEpsilonPeriodPath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.ellipticThreeCuspCorrectedEpsilonPeriodPath.cast
    A.centralAffineBase_eq_cuspCentralBase
    A.centralAffineBase_eq_cuspCentralBase

/-- The global zero-section triple displayed at the final affine basepoint. -/
public noncomputable def orderThreeCentralAffineZeroSectionTriplePath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.ellipticThreeCuspZeroSectionTriplePath.cast
    A.centralAffineBase_eq_cuspCentralBase
    A.centralAffineBase_eq_cuspCentralBase

public theorem orderThreeCentralAffineCorrectedGeometricRelatorPath_eq_trans :
    A.orderThreeCentralAffineCorrectedGeometricRelatorPath =
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.trans
        A.orderThreeCentralAffineZeroSectionTriplePath := by
  unfold orderThreeCentralAffineCorrectedGeometricRelatorPath
    ellipticThreeCuspCorrectedGeometricRelatorPath
    orderThreeCentralAffineCorrectedEpsilonPeriodPath
    orderThreeCentralAffineZeroSectionTriplePath
  rw [Path.cast_trans]





/-- The two coherent factor comparisons assemble to a free homotopy of the complete split
relator, with pointwise equal endpoint traces. -/
public theorem ellipticThree_exists_relatorHomotopy_of_factorHomotopies
    (h : (let _ := A.ellipticThreeBoundaryAction
  ∃ Hfiber : ContinuousMap.Homotopy
      A.orderThreeLocalOffsetFiberCentralPath.toContinuousMap
      A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.toContinuousMap,
    ∃ Hbase : ContinuousMap.Homotopy
      A.orderThreeLocalOffsetBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineZeroSectionTriplePath.toContinuousMap,
      (∀ s : unitInterval, Hfiber (s, 1) = Hbase (s, 0)) ∧
      (∀ s : unitInterval, Hfiber (s, 0) = Hbase (s, 1)))) :
    letI := A.ellipticThreeBoundaryAction
    ∃ H : ContinuousMap.Homotopy
      A.orderThreeLocalFiberThenBaseCentralPath.toContinuousMap
      A.orderThreeCentralAffineCorrectedGeometricRelatorPath.toContinuousMap,
      ∀ s : unitInterval, H (s, 0) = H (s, 1) := by
  let _ := A.ellipticThreeBoundaryAction
  rcases h with ⟨Hfiber, Hbase, hjoin, htrace⟩
  let H := Hfiber.hcompLoop Hbase hjoin
  have hsource :
      (A.orderThreeLocalOffsetFiberCentralPath.trans
        A.orderThreeLocalOffsetBaseCentralPath).toContinuousMap =
      A.orderThreeLocalFiberThenBaseCentralPath.toContinuousMap :=
    congrArg Path.toContinuousMap
      A.orderThreeLocalFiberThenBaseCentralPath_eq_trans.symm
  have htarget :
      (A.orderThreeCentralAffineCorrectedEpsilonPeriodPath.trans
        A.orderThreeCentralAffineZeroSectionTriplePath).toContinuousMap =
      A.orderThreeCentralAffineCorrectedGeometricRelatorPath.toContinuousMap :=
    congrArg Path.toContinuousMap
      A.orderThreeCentralAffineCorrectedGeometricRelatorPath_eq_trans.symm
  let H' := H.cast hsource htarget
  refine ⟨H', ?_⟩
  intro s
  change H (s, 0) = H (s, 1)
  exact Hfiber.hcompLoop_trace Hbase hjoin htrace s

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
