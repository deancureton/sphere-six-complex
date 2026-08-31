module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof
public import
  SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished

/-!
# Cusp marked invariant basis from oriented full-fibre naturality

The full fibre at the selected overlap crossing already induces the correct period-marked map
to the elliptic band.  Consequently, the two remaining marked evaluations follow from one
oriented naturality square: its induced map on first homology must intertwine the Wang boundary
with the connecting morphism of the pulled-back binary open cover.

This isolates the remaining geometric input without mentioning a basis or a scalar coordinate.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticTwoDiscCoverData
open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The oriented naturality square for the selected full-fibre slice.  Unlike exactness alone,
this equality fixes the sign of the connecting morphism. -/
public def ActualCuspWangFullFibreOrientedBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  (actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
      (actualCuspWangBoundaryHom A) =
    R.twoDiscCover.cuspOpenCoverConnectingHom

/-- The homomorphism-level naturality square is equivalent to the two invariant-generator
comparisons left after the four zero-boundary cases. -/
public theorem fullFibreOrientedBoundaryNaturality_iff_invariantResidual
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspWangFullFibreOrientedBoundaryNaturality R ↔
      ActualCuspWangFullFibreSliceInvariantResidual R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [ActualCuspWangFullFibreOrientedBoundaryNaturality]
  constructor
  · intro h
    have hBasis : ∀ i : Fin 6,
        ((actualCuspWangFibreToCuspCoverIntersectionHomologyOne (A := A) R).comp
            (actualCuspWangBoundaryHom A))
              (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
          R.twoDiscCover.cuspOpenCoverConnectingHom
            (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1)) := fun i ↦
      DFunLike.congr_fun h
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))
    apply (explicitFiniteResidual_iff_invariantResidual R).mp
    apply (wangBoundaryBasisComparison_iff_explicitFiniteResidual R).mp
    exact hBasis
  · intro h
    apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
      A.actualCuspRawHomologyTwoEquiv
    exact (wangBoundaryBasisComparison_iff_explicitFiniteResidual R).mpr
      ((explicitFiniteResidual_iff_invariantResidual R).mpr h)

/-- The oriented homomorphism square supplies the finite full-fibre comparison package. -/
public theorem actualCuspWangFullFibreSliceComparison_of_orientedBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspWangFullFibreOrientedBoundaryNaturality R) :
    ActualCuspWangFullFibreSliceComparison R where
  wangBoundary_eq_chainConnecting_basis i := DFunLike.congr_fun h
    (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))

/-- Oriented naturality for the selected full-fibre slice gives the canonical unmarked Wang
boundary square. -/
public theorem canonicalCuspWangBoundaryNaturality_of_fullFibreOrientedBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspWangFullFibreOrientedBoundaryNaturality R) :
    R.twoDiscCover.CanonicalCuspWangBoundaryNaturality := by
  let C := actualCuspWangFullFibreSliceComparison_of_orientedBoundaryNaturality R h
  let Z := actualCuspWangOpenCoverChainRealization_of_fullFibreSlice R
    C.fiberToBand_homology C.wangBoundary_eq_chainConnecting
  exact Z.canonicalWangBoundaryNaturality

/-- The one oriented full-fibre naturality square implies both remaining marked evaluations on
the invariant raw degree-two generators. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_fullFibreOrientedBoundaryNaturality
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspWangFullFibreOrientedBoundaryNaturality R) :
    CuspPulledBackMarkedInvariantBasisData R := by
  have hBoundary : R.twoDiscCover.CanonicalCuspWangBoundaryNaturality :=
    canonicalCuspWangBoundaryNaturality_of_fullFibreOrientedBoundaryNaturality R h
  have hMarking : R.twoDiscCover.CanonicalCuspFiberBandPeriodMarking R.homologyAlignment :=
    R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree R.homologyAlignment
      (R.canonicalCuspFiberOrderThreePeriodMarking
        (actualCuspFiberPeriodMarkingCompatibility A))
  let C := R.twoDiscCover.sectionSevenCuspWangBandCompatibility_of_canonicalMap
    R.homologyAlignment hBoundary hMarking
  have hSquare := C.connectingNaturality.square
  rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive] at hSquare
  constructor
  · have hFour := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFour
  · have hFive := DFunLike.congr_fun hSquare
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFive

/-- Equivalently, the two unmarked invariant-generator comparisons for the selected full-fibre
slice imply both marked scalar evaluations. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_fullFibreInvariantResidual
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : ActualCuspWangFullFibreSliceInvariantResidual R) :
    CuspPulledBackMarkedInvariantBasisData R :=
  cuspPulledBackMarkedInvariantBasisData_of_fullFibreOrientedBoundaryNaturality R
    ((fullFibreOrientedBoundaryNaturality_iff_invariantResidual R).mpr h)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
