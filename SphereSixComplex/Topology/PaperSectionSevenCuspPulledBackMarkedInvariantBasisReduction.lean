module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished

/-!
# Reduction of the cusp invariant-basis evaluations

The two marked Mayer--Vietoris boundary evaluations follow from the corresponding oriented
full-fibre-slice comparisons.  All subsequent steps use the constructed Wang boundary, the
canonical cusp-to-band map, and the proved period marking.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The two oriented full-fibre-slice comparisons imply the two marked invariant-basis
evaluations of the pulled-back Mayer--Vietoris boundary. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_fullFibreSliceInvariantResidual
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspWangFullFibreSliceInvariantResidual R) :
    CuspPulledBackMarkedInvariantBasisData R := by
  have hExplicit : ActualCuspWangFullFibreSliceExplicitFiniteResidual R :=
    (explicitFiniteResidual_iff_invariantResidual R).mpr h
  have hBasis := (wangBoundaryBasisComparison_iff_explicitFiniteResidual R).mpr hExplicit
  let C : ActualCuspWangFullFibreSliceComparison R :=
    ⟨hBasis⟩
  let realization := actualCuspWangOpenCoverChainRealization_of_fullFibreSlice R
    C.fiberToBand_homology C.wangBoundary_eq_chainConnecting
  have hBoundary : R.twoDiscCover.CanonicalCuspWangBoundaryNaturality :=
    realization.canonicalWangBoundaryNaturality
  have hOrderThree : R.twoDiscCover.CanonicalCuspFiberOrderThreePeriodMarking :=
    R.canonicalCuspFiberOrderThreePeriodMarking
      (actualCuspFiberPeriodMarkingCompatibility A)
  have hMarking : R.twoDiscCover.CanonicalCuspFiberBandPeriodMarking R.homologyAlignment :=
    R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree
      R.homologyAlignment hOrderThree
  let W := R.twoDiscCover.sectionSevenCuspWangBandCompatibility_of_canonicalMap
    R.homologyAlignment hBoundary hMarking
  have hSquare := W.connectingNaturality.square
  rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive] at hSquare
  constructor
  · have hFour := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFour
  · have hFive := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFive

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
