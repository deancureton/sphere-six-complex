module

public import SphereSixComplex.Topology.PaperActualEllipticOrderThreeProductLoopSplittingProof
public import SphereSixComplex.Topology.PaperActualEllipticRelatorFreeHomotopyReduction

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The literal global period loop carrying the corrected order-three `epsilon` label. -/
public noncomputable def orderThreeActualCuspCorrectedEpsilonPeriodPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.actualCuspCentralPeriodLoop
    (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon)

/-- The corrected literal period path has exactly the marked affine-core translation class. -/
public theorem orderThreeActualCuspCorrectedEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk A.orderThreeActualCuspCorrectedEpsilonPeriodPath =
      Additive.toMul (A.correctedActualCuspCentralTranslation epsilon) := by
  unfold orderThreeActualCuspCorrectedEpsilonPeriodPath
    correctedActualCuspCentralTranslation
  rw [← A.actualCuspCentralTranslation_eq_periodLoop]
  rfl

/-- A concrete global representative of the corrected order-three affine relator. -/
public noncomputable def orderThreeActualCuspCorrectedGeometricRelatorPath :
    Path A.actualCuspCentralBase A.actualCuspCentralBase :=
  A.orderThreeActualCuspCorrectedEpsilonPeriodPath.trans
    A.orderThreeActualCuspZeroSectionTriplePath

/-- Transporting the concrete corrected representative to the displayed affine base gives the
exact order-three expected relator, with no range-level choice of a lattice label. -/
public theorem orderThreeActualCuspCorrectedGeometricRelatorPath_class :
    A.actualCuspToCentralAffineBaseEquiv
        (Path.Homotopic.Quotient.mk
          A.orderThreeActualCuspCorrectedGeometricRelatorPath) =
      A.orderThreeCentralExpectedRelator := by
  rw [orderThreeActualCuspCorrectedGeometricRelatorPath,
    Path.Homotopic.Quotient.mk_trans,
    A.orderThreeActualCuspZeroSectionTriplePath_class,
    A.orderThreeActualCuspCorrectedEpsilonPeriodPath_class]
  change A.actualCuspToCentralAffineBaseEquiv
      (A.geometricCentralRhoOne ^ 3 *
        Additive.toMul (A.correctedActualCuspCentralTranslation epsilon)) = _
  unfold orderThreeCentralExpectedRelator
  rw [map_mul, map_pow, A.centralAffineCorePiOneData_rhoOne]
  have ht := A.centralAffineCorePiOneData_translation (-epsilon)
  congr 1
  calc
    A.actualCuspToCentralAffineBaseEquiv
          (Additive.toMul (A.correctedActualCuspCentralTranslation epsilon)) =
        (A.actualCuspToCentralAffineBaseEquiv
          (Additive.toMul (A.correctedActualCuspCentralTranslation (-epsilon))))⁻¹ := by
            rw [map_neg, toMul_neg, map_inv]
            simp
    _ = (Additive.toMul
          (A.centralAffineCorePiOneData.translation (-epsilon)))⁻¹ :=
      (congrArg Inv.inv ht).symm

/-- The same concrete representative, displayed at the affine basepoint expected by the final
free-homotopy reduction. -/
public noncomputable def orderThreeCentralAffineCorrectedGeometricRelatorPath :
    Path A.centralAffineBase A.centralAffineBase :=
  A.orderThreeActualCuspCorrectedGeometricRelatorPath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

public theorem orderThreeCentralAffineCorrectedGeometricRelatorPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeCentralAffineCorrectedGeometricRelatorPath =
      A.orderThreeCentralExpectedRelator := by
  unfold orderThreeCentralAffineCorrectedGeometricRelatorPath
  rw [Path.Homotopic.Quotient.mk_cast]
  rw [← A.orderThreeActualCuspCorrectedGeometricRelatorPath_class]
  unfold actualCuspToCentralAffineBaseEquiv
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
