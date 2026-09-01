module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeCorrectedFibreRepresentativeProof
public import SphereSixComplex.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction

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
  A.orderThreeActualCuspCorrectedEpsilonPeriodPath.symm.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

public theorem orderThreeActualCuspCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeActualCuspCorrectedEpsilonPeriodPath.symm =
      Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon)) := by
  rw [Path.Homotopic.Quotient.mk_symm]
  rw [A.orderThreeActualCuspCorrectedEpsilonPeriodPath_class]
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
  rw [A.orderThreeActualCuspCorrectedNegativeEpsilonPeriodPath_class]
  rw [A.centralAffineCorePiOneData_translation]
  unfold actualCuspToCentralAffineBaseEquiv
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]

/-- Pointwise, the physical translation loop is the central projection of the inverse-collar
representative of its straight affine-cover segment. -/
public theorem orderThreeTranslationStraightCentralLoop_apply_collarInverse
    (t : unitInterval) :
    letI := orderThreeAffineMappingTorusDeckAction A.periods
    letI := A.orderThreeActualEllipticBoundaryAction
    let g := Additive.toMul
      (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))
    let q :=
      (A.orderThreeActualEllipticBoundaryBase.1,
        Path.segment A.orderThreeActualEllipticBoundaryBase.2
          (g • A.orderThreeActualEllipticBoundaryBase.2) t)
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection
        (orderThreeCollarToRegular A.periods
          (sourceActionProperlyDiscontinuous_of_eq
            A.modular.modularParameter.toTriangleUniformization_sourceAction)
          A.starSeparation.orderThree.sourceData
          (orderThreePuncturedCollarGaugeEquiv A.periods
            A.starSeparation.orderThree.radius
            (A.orderThreeCollarInverseRepresentative q))) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit
    (Additive.toMul
      (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))) t

/-- The corrected negative period transported to the order-three boundary chart basepoint. -/
public noncomputable def orderThreeCentralBoundaryCorrectedNegativeEpsilonPeriodPath :
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase :=
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
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase :=
  A.orderThreeCentralBoundaryChartPath.symm.trans
    (A.orderThreeActualCuspCorrectedEpsilonPeriodPath.symm.trans
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
        A.orderThreeActualCuspCorrectedEpsilonPeriodPath.symm).trans
        (Path.Homotopic.Quotient.mk A.orderThreeCentralBoundaryChartPath)) = _
  rw [A.orderThreeActualCuspCorrectedNegativeEpsilonPeriodPath_class]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.orderThreeCentralBoundaryChartPath _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rfl

/-- The corrected negative period transported along the prescribed geometric connector. -/
public noncomputable def orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath :
    Path A.orderThreeActualEllipticCentralBase A.orderThreeActualEllipticCentralBase :=
  A.orderThreeActualCentralGeometricConnector.symm.trans
    (A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath.trans
      A.orderThreeActualCentralGeometricConnector)

public theorem orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        A.orderThreeActualCentralGeometricConnector
        (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) := by
  unfold orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
    A.orderThreeActualCentralGeometricConnector _
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  simp only [CategoryTheory.Iso.conj_apply]
  rw [A.orderThreeCentralAffineCorrectedNegativeEpsilonPeriodPath_class]
  rfl

/-- The translation premise in the geometric-connector reduction is exactly one relative path
homotopy between two explicit loops. -/
public theorem orderThreeGeometricConnector_translationClass_iff_pathHomotopic :
    letI := A.orderThreeActualEllipticBoundaryAction
    (Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
            (Additive.toMul
              (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon)))) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderThreeActualCentralGeometricConnector
          (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))) ↔
      Path.Homotopic
        (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))
        A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  rw [← A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath_class]
  exact Path.Homotopic.Quotient.eq

/-- An endpoint-relative proof of the translation comparison supplies the exact translation
premise of the geometric-connector assembly theorem. -/
public theorem orderThreeCentralBoundaryExistentialStraightLoopIdentities_of_translationHomotopy
    (hmeridian :
      letI := A.orderThreeActualEllipticBoundaryAction
      Path.Homotopic.Quotient.mk
          (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
            A.orderThreeActualEllipticBoundaryDeckData.meridian) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath
          A.orderThreeActualCentralGeometricConnector A.centralAffineCorePiOneData.rhoOne)
    (htranslation :
      letI := A.orderThreeActualEllipticBoundaryAction
      Path.Homotopic
        (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
          (Additive.toMul
            (A.orderThreeActualEllipticBoundaryDeckData.translation (-epsilon))))
        A.orderThreeGeometricConnectorCorrectedNegativeEpsilonPeriodPath) :
    A.OrderThreeCentralBoundaryExistentialStraightLoopIdentities := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  apply A.orderThreeCentralBoundaryExistentialStraightLoopIdentities_of_geometricConnector_loopClasses
    hmeridian
  exact A.orderThreeGeometricConnector_translationClass_iff_pathHomotopic.mpr htranslation

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
