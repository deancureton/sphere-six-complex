module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished

/-!
# Finite reduction of the marked cusp connecting square

The Wang side of the marked connecting square is the last raw degree-two coordinate.  On the
pulled-back Mayer--Vietoris side, the first four raw basis vectors vanish by the explicit cover
calculation.  Thus the full square follows from two scalar evaluations on the invariant basis.
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
