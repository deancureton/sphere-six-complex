module
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
import all SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
import all SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeZeroSectionHomotopyProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeBaseFactorHomotopyProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourLocalGlobalFactorHomotopyReduction

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.AnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

variable (A : AnalyticData)


public theorem orderFourCentralAffineZeroSectionQuadruplePath_class :
    Path.Homotopic.Quotient.mk A.orderFourCentralAffineZeroSectionQuadruplePath =
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoTwo) ^ 4 := by
  unfold orderFourCentralAffineZeroSectionQuadruplePath
  rw [Path.Homotopic.Quotient.mk_cast,
    A.ellipticFourCuspZeroSectionQuadruplePath_class]
  rw [← map_pow]
  unfold cuspToCentralAffineBaseEquiv
  rw [fundamentalGroupMulEquivOfEq_apply]


public theorem orderThreeCentralAffineZeroSectionTriplePath_class :
    Path.Homotopic.Quotient.mk A.orderThreeCentralAffineZeroSectionTriplePath =
      (A.cuspToCentralAffineBaseEquiv A.geometricCentralRhoOne) ^ 3 := by
  unfold orderThreeCentralAffineZeroSectionTriplePath
  rw [Path.Homotopic.Quotient.mk_cast,
    A.ellipticThreeCuspZeroSectionTriplePath_class]
  rw [← map_pow]
  unfold cuspToCentralAffineBaseEquiv
  rw [fundamentalGroupMulEquivOfEq_apply]


end SphereSixComplex.Geometry.AnalyticData
