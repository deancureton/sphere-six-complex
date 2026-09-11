module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeCorrectedFiberRepresentativeProof

/-!
# Point-set reduction for the order-three translation loop
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

/-- The inverse corrected `epsilon`-period, rebased at the displayed affine basepoint. -/
public noncomputable def orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.ellipticThreeCuspCorrectedEpsilonPeriodPath.symm.cast
    A.centralAffineBase_eq_cuspCentralBase
    A.centralAffineBase_eq_cuspCentralBase

public theorem ellipticThreeCuspCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.ellipticThreeCuspCorrectedEpsilonPeriodPath.symm =
      Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon)) := by
  rw [Path.Homotopic.Quotient.mk_symm]
  rw [A.ellipticThreeCuspCorrectedEpsilonPeriodPath_class]
  rw [map_neg, toMul_neg]
  change Path.Homotopic.Quotient.symm
      (Additive.toMul (A.correctedActualCuspCentralTranslation epsilon)) =
    Path.Homotopic.Quotient.symm
      (Additive.toMul (A.correctedActualCuspCentralTranslation epsilon))
  rfl

public theorem orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath =
      Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)) := by
  unfold orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath
  rw [Path.Homotopic.Quotient.mk_cast]
  rw [A.ellipticThreeCuspCorrectedNegativeEpsilonPeriodPath_class]
  rw [A.centralAffineCorePiOneData_translation]
  unfold cuspToCentralAffineBaseEquiv
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]

/-- Pointwise, the physical translation loop is the central projection of the inverse-collar
representative of its straight affine-cover segment. -/
public theorem orderThreeTranslationStraightCentralLoop_apply_collarInverse
    (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.ellipticThreeBoundaryAction
    let g := Additive.toMul
      (A.ellipticThreeBoundaryDeckData.translation (-epsilon))
    let q :=
      (A.ellipticThreeBoundaryBase.1,
        Path.segment A.ellipticThreeBoundaryBase.2
          (g • A.ellipticThreeBoundaryBase.2) t)
    A.ellipticThreeBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection
        (orderThreeCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderThree.radius
            (A.orderThreeCollarInverseRepresentative q))) := by
  let _ := A.ellipticThreeBoundaryAction
  exact A.ellipticThreeBoundaryDeckStraightCentralLoop_apply_explicit
    (Additive.toMul
      (A.ellipticThreeBoundaryDeckData.translation (-epsilon))) t

/-- The corrected negative period transported to the order-three boundary chart basepoint. -/
public noncomputable def orderThreeCentralBoundaryCorrectedNegativeEpsilonPeriodPath :
    Path A.ellipticThreeCentralBase A.ellipticThreeCentralBase :=
  A.orderThreeCentralBaseWhisker.symm.trans
    (A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath.trans
      A.orderThreeCentralBaseWhisker)

public theorem orderThreeCentralBoundaryCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeCentralBoundaryCorrectedNegativeEpsilonPeriodPath =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeCentralBaseWhisker
        (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) := by
  unfold orderThreeCentralBoundaryCorrectedNegativeEpsilonPeriodPath
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.orderThreeCentralBaseWhisker _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rw [A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath_class]
  rfl

/-- The same transported loop written at the literal cusp basepoint used by the chart API. -/
public noncomputable def orderThreeCentralBoundaryChartCorrectedNegativeEpsilonPeriodPath :
    Path A.ellipticThreeCentralBase A.ellipticThreeCentralBase :=
  A.orderThreeCentralBoundaryChartPath.symm.trans
    (A.ellipticThreeCuspCorrectedEpsilonPeriodPath.symm.trans
      A.orderThreeCentralBoundaryChartPath)

public theorem orderThreeCentralBoundaryChartCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeCentralBoundaryChartCorrectedNegativeEpsilonPeriodPath =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeCentralBoundaryChartPath
        (Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon))) := by
  unfold orderThreeCentralBoundaryChartCorrectedNegativeEpsilonPeriodPath
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change (Path.Homotopic.Quotient.mk A.orderThreeCentralBoundaryChartPath).symm.trans
      ((Path.Homotopic.Quotient.mk
        A.ellipticThreeCuspCorrectedEpsilonPeriodPath.symm).trans
        (Path.Homotopic.Quotient.mk A.orderThreeCentralBoundaryChartPath)) = _
  rw [A.ellipticThreeCuspCorrectedNegativeEpsilonPeriodPath_class]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.orderThreeCentralBoundaryChartPath _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rfl

/-- The corrected negative period transported along the prescribed geometric connector. -/
public noncomputable def orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath :
    Path A.ellipticThreeCentralBase A.ellipticThreeCentralBase :=
  A.ellipticThreeCentralGeometricConnector.symm.trans
    (A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath.trans
      A.ellipticThreeCentralGeometricConnector)

public theorem orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.ellipticThreeCentralGeometricConnector
        (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) := by
  unfold orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.ellipticThreeCentralGeometricConnector _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rw [A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath_class]
  rfl

/-- The translation premise in the geometric-connector reduction is exactly one relative path
homotopy between two explicit loops. -/
public theorem orderThreeGeometricConnector_translationClass_iff_pathHomotopic :
    letI := A.ellipticThreeBoundaryAction
    (Path.Homotopic.Quotient.mk
          (A.ellipticThreeBoundaryDeckStraightCentralLoop
            (Additive.toMul
              (A.ellipticThreeBoundaryDeckData.translation (-epsilon)))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.ellipticThreeCentralGeometricConnector
          (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))) ↔
      Path.Homotopic
        (A.ellipticThreeBoundaryDeckStraightCentralLoop
          (Additive.toMul
            (A.ellipticThreeBoundaryDeckData.translation (-epsilon))))
        A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath := by
  let _ := A.ellipticThreeBoundaryAction
  rw [← A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath_class]
  exact Path.Homotopic.Quotient.eq

/-- An endpoint-relative proof of the translation comparison supplies the exact translation
premise of the geometric-connector assembly theorem. -/
public theorem orderThreeCentralBoundaryExistentialStraightLoopIdentities_of_translationHomotopy
    (hmeridian :
      letI := A.ellipticThreeBoundaryAction
      Path.Homotopic.Quotient.mk
          (A.ellipticThreeBoundaryDeckStraightCentralLoop
            A.ellipticThreeBoundaryDeckData.meridian) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.ellipticThreeCentralGeometricConnector A.centralAffineCorePiOneData.rhoOne)
    (htranslation :
      letI := A.ellipticThreeBoundaryAction
      Path.Homotopic
        (A.ellipticThreeBoundaryDeckStraightCentralLoop
          (Additive.toMul
            (A.ellipticThreeBoundaryDeckData.translation (-epsilon))))
        A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath) :
    A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities := by
  let _ := A.ellipticThreeBoundaryAction
  apply A.orderThreeCentralBoundaryExistentialStraightLoopIdentities_of_geometricConnector_loopClasses
    hmeridian
  exact A.orderThreeGeometricConnector_translationClass_iff_pathHomotopic.mpr htranslation

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
