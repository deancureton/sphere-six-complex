module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspMarkedConnectingNaturalityProof
public import
  SphereSixComplex.Paper.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished

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

open EllipticTwoDiscCoverData
open EllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace EllipticTwoDiscCoverData

/-- The oriented naturality square for the selected full-fibre slice.  Unlike exactness alone,
this equality fixes the sign of the connecting morphism. -/
public def ActualCuspWangFullFiberOrientedBoundaryNaturality
    (R : A.AffineRadialCompletionInput) : Prop :=
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  (actualCuspWangFiberToCuspCoverIntersectionHomologyOne (A := A) R).comp
      (actualCuspWangBoundaryHom A) =
    R.twoDiscCover.cuspOpenCoverConnectingHom

/-- The homomorphism-level naturality square is equivalent to the two invariant-generator
comparisons left after the four zero-boundary cases. -/
public theorem fullFiberOrientedBoundaryNaturality_iff_invariantResidual
    (R : A.AffineRadialCompletionInput) :
    ActualCuspWangFullFiberOrientedBoundaryNaturality R ↔
      ActualCuspWangFullFiberSliceInvariantResidual R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [ActualCuspWangFullFiberOrientedBoundaryNaturality]
  constructor
  · intro h
    have hBasis : ∀ i : Fin 6,
        ((actualCuspWangFiberToCuspCoverIntersectionHomologyOne (A := A) R).comp
            (actualCuspWangBoundaryHom A))
              (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1)) =
          R.twoDiscCover.cuspOpenCoverConnectingHom
            (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1)) := fun i ↦
      DFunLike.congr_fun h
        (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))
    apply (explicitFiniteResidual_iff_invariantResidual R).mp
    apply (wangBoundaryBasisComparison_iff_explicitFiniteResidual R).mp
    exact hBasis
  · intro h
    apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
      A.cuspRawHomologyTwoEquiv
    exact (wangBoundaryBasisComparison_iff_explicitFiniteResidual R).mpr
      ((explicitFiniteResidual_iff_invariantResidual R).mpr h)

/-- The oriented homomorphism square supplies the finite full-fibre comparison package. -/
public theorem actualCuspWangFullFiberSliceComparison_of_orientedBoundaryNaturality
    (R : A.AffineRadialCompletionInput)
    (h : ActualCuspWangFullFiberOrientedBoundaryNaturality R) :
    ActualCuspWangFullFiberSliceComparison R where
  wangBoundary_eq_chainConnecting_basis i := DFunLike.congr_fun h
    (A.cuspRawHomologyTwoEquiv.symm (Pi.single i 1))

/-- Oriented naturality for the selected full-fibre slice gives the canonical unmarked Wang
boundary square. -/
public theorem canonicalCuspWangBoundaryNaturality_of_fullFiberOrientedBoundaryNaturality
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput)
    (h : ActualCuspWangFullFiberOrientedBoundaryNaturality R) :
    (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne.comp (actualCuspWangBoundaryHom A) =
         R.twoDiscCover.cuspPulledBackBoundaryHom) := by
  let C := actualCuspWangFullFiberSliceComparison_of_orientedBoundaryNaturality R h
  let Z := actualCuspWangOpenCoverChainRealization_of_fullFiberSlice R
    (C.fiberToBand_homology hmark) C.wangBoundary_eq_chainConnecting
  exact Z.canonicalWangBoundaryNaturality

/-- The one oriented full-fibre naturality square implies both remaining marked evaluations on
the invariant raw degree-two generators. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_fullFiberOrientedBoundaryNaturality
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput)
    (h : ActualCuspWangFullFiberOrientedBoundaryNaturality R) :
    ((R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 0 ∧
      (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) = 1) := by
  have hBoundary : (R.twoDiscCover.canonicalCuspFiberToBandHomologyOne.comp (actualCuspWangBoundaryHom A) =
                        R.twoDiscCover.cuspPulledBackBoundaryHom) :=
    canonicalCuspWangBoundaryNaturality_of_fullFiberOrientedBoundaryNaturality hmark R h
  have hMarking : (R.homologyAlignment.actualHomologyCoordinates.bandOne.toAddMonoidHom.comp
                         R.twoDiscCover.canonicalCuspFiberToBandHomologyOne =
                       let G := A.actualCuspRadialClutchingData
                       let _ := G.fiberTopology
                       G.monodromyCoordinates.degreeOne.toAddMonoidHom) :=
    R.twoDiscCover.canonicalCuspFiberBandPeriodMarking_of_orderThree R.homologyAlignment
      (R.canonicalCuspFiberOrderThreePeriodMarking
        (cuspFiberPeriodMarkingCompatibility A))
  let C := R.twoDiscCover.sectionSevenCuspWangBandCompatibility_of_canonicalMap
    R.homologyAlignment hBoundary hMarking
  have hSquare := C.connectingNaturality
  rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive] at hSquare
  constructor
  · have hFour := DFunLike.congr_fun hSquare
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFour
  · have hFive := DFunLike.congr_fun hSquare
      (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))
    simpa [coordinateAfterAddEquiv_apply] using hFive

/-- Equivalently, the two unmarked invariant-generator comparisons for the selected full-fibre
slice imply both marked scalar evaluations. -/
public theorem cuspPulledBackMarkedInvariantBasisData_of_fullFiberInvariantResidual
    (hmark : A.affineNamedStripLift.lift
      A.affineActualCuspCrossingPoint =
        A.cuspAngularRegularBasePoint A.affineActualCuspCrossingTime)
    (R : A.AffineRadialCompletionInput)
    (h : ActualCuspWangFullFiberSliceInvariantResidual R) :
    ((R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) = 0 ∧
      (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.cuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) = 1) :=
  cuspPulledBackMarkedInvariantBasisData_of_fullFiberOrientedBoundaryNaturality hmark R
    ((fullFiberOrientedBoundaryNaturality_iff_invariantResidual R).mpr h)

end EllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
