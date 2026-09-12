module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCompletionReduction
public import SphereSixComplex.Paper.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Paper.Geometry.RealPeriodTrivialization
public import SphereSixComplex.Paper.Topology.PaperCuspBoundaryUniversalCover
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangFullFiberSliceComparisonProof
import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandSquares

/-!
# Vanishing of fiber classes under the marked cusp boundary

The first four raw degree-two basis vectors have zero pulled-back marked boundary, by the
explicit open-cover calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.AnalyticData

open EllipticInteriorMarkedCycleData
open SphereSixComplex.CircleMappingTorusHomologyBases

namespace EllipticTwoDiscCoverData


/-- The pulled-back marked boundary vanishes on the four non-invariant raw basis vectors. -/
public theorem cuspPulledBackMarkedBoundary_rawBasis_castAdd_eq_zero
    {A : AnalyticData} (R : A.AffineRadialCompletionInput)
    (i : Fin 4) :
    (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm
            (Pi.single (Fin.castAdd 2 i) 1))) = 0 := by
  rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
  change (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
    (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
      (R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.cuspRawHomologyTwoEquiv.symm
          (Pi.single (Fin.castAdd 2 i) 1)))) = 0
  rw [cuspOpenCoverConnectingHom_rawBasis_castAdd_eq_zero]
  simp


end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.AnalyticData

end

end
