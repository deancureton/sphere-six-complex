module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeProductLoopSplittingProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticRelatorFreeHomotopyReduction

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup

variable (A : PaperAnalyticData)

/-- The literal global period loop carrying the corrected order-three `epsilon` label. -/
public noncomputable def ellipticThreeCuspCorrectedEpsilonPeriodPath :
    Path A.cuspCentralBase A.cuspCentralBase :=
  A.cuspCentralPeriodLoop
    (rhoLambda ((g₁ * g₂) ^ A.geometricCentralCuspConjugatorExponent) epsilon)

/-- The corrected literal period path has exactly the marked affine-core translation class. -/
public theorem ellipticThreeCuspCorrectedEpsilonPeriodPath_class :
    Path.Homotopic.Quotient.mk A.ellipticThreeCuspCorrectedEpsilonPeriodPath =
      Additive.toMul (A.correctedActualCuspCentralTranslation epsilon) := by
  unfold ellipticThreeCuspCorrectedEpsilonPeriodPath
    correctedActualCuspCentralTranslation
  rw [← A.cuspCentralTranslation_eq_periodLoop]
  rfl

/-- A concrete global representative of the corrected order-three affine relator. -/
public noncomputable def ellipticThreeCuspCorrectedGeometricRelatorPath :
    Path A.cuspCentralBase A.cuspCentralBase :=
  A.ellipticThreeCuspCorrectedEpsilonPeriodPath.trans
    A.ellipticThreeCuspZeroSectionTriplePath

/-- Transporting the concrete corrected representative to the displayed affine base gives the
exact order-three expected relator, with no range-level choice of a lattice label. -/
public theorem ellipticThreeCuspCorrectedGeometricRelatorPath_class :
    A.cuspToCentralAffineBaseEquiv
        (Path.Homotopic.Quotient.mk
          A.ellipticThreeCuspCorrectedGeometricRelatorPath) =
      A.orderThreeCentralExpectedRelator := by
  rw [ellipticThreeCuspCorrectedGeometricRelatorPath,
    Path.Homotopic.Quotient.mk_trans,
    A.ellipticThreeCuspZeroSectionTriplePath_class,
    A.ellipticThreeCuspCorrectedEpsilonPeriodPath_class]
  change A.cuspToCentralAffineBaseEquiv
      (A.geometricCentralRhoOne ^ 3 *
        Additive.toMul (A.correctedActualCuspCentralTranslation epsilon)) = _
  unfold orderThreeCentralExpectedRelator
  rw [map_mul, map_pow, A.centralAffineCorePiOneData_rhoOne]
  have ht := A.centralAffineCorePiOneData_translation (-epsilon)
  congr 1
  calc
    A.cuspToCentralAffineBaseEquiv
          (Additive.toMul (A.correctedActualCuspCentralTranslation epsilon)) =
        (A.cuspToCentralAffineBaseEquiv
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
  A.ellipticThreeCuspCorrectedGeometricRelatorPath.cast
    A.centralAffineBase_eq_actualCuspCentralBase
    A.centralAffineBase_eq_actualCuspCentralBase

public theorem orderThreeCentralAffineCorrectedGeometricRelatorPath_class :
    Path.Homotopic.Quotient.mk
        A.orderThreeCentralAffineCorrectedGeometricRelatorPath =
      A.orderThreeCentralExpectedRelator := by
  unfold orderThreeCentralAffineCorrectedGeometricRelatorPath
  rw [Path.Homotopic.Quotient.mk_cast]
  rw [← A.ellipticThreeCuspCorrectedGeometricRelatorPath_class]
  unfold cuspToCentralAffineBaseEquiv
  rw [SphereSixComplex.Topology.fundamentalGroupMulEquivOfEq_apply]

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
