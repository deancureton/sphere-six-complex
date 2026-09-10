module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof

/-!
# Exact residual for the marked cusp boundary

Pullback naturality for the two-disc Mayer--Vietoris cover is already unconditional.  The
remaining comparison is precisely the orientation-sensitive square between its connecting
morphism and the constructed cusp Wang boundary after applying the fourth period coordinate.

The theorem below shows that this one homomorphism square is equivalent to the two remaining
invariant-basis evaluations.  Thus proving ordinary exactness of the Wang sequence cannot close
the gap: the missing input must identify the oriented connecting morphism.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open EllipticTwoDiscCoverData
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace EllipticTwoDiscCoverData

/-- The marked connecting-morphism square directly supplies the two invariant evaluations. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_markedConnectingNaturality
    (R : A.AffineRadialCompletionInput)
    (h : R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment) :
    CuspPulledBackMarkedInvariantBasisData R := by
  have hSquare := h.square
  rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive] at hSquare
  constructor
  · have hFour := DFunLike.congr_fun hSquare
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFour
  · have hFive := DFunLike.congr_fun hSquare
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFive

/-- The two invariant-basis evaluations are exactly the marked connecting-morphism square.
The first four basis evaluations used in the converse are already theorems of the explicit
pulled-back cover calculation. -/
public theorem cuspPulledBackMarkedInvariantBasisData_iff_markedConnectingNaturality
    (R : A.AffineRadialCompletionInput) :
    CuspPulledBackMarkedInvariantBasisData R ↔
      R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment := by
  constructor
  · exact cuspMarkedConnectingNaturality_of_invariantBasisData R
  · exact cuspPulledBackMarkedInvariantBasisData_of_markedConnectingNaturality R

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
