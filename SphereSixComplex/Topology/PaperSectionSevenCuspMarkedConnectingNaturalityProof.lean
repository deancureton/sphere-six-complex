module

public import SphereSixComplex.Topology.PaperSectionSevenAffineCuspFiberPeriodMarking
public import SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspWangBoundaryNaturalityProof
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangFullFibreSliceComparisonProof

/-!
# Finite reduction of the marked cusp connecting square

The Wang side of the marked connecting square is the last raw degree-two coordinate.  On the
pulled-back Mayer--Vietoris side, the first four raw basis vectors vanish by the explicit cover
calculation.  Thus the full square follows from two scalar evaluations on the invariant basis.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData
open SphereSixComplex.CircleMappingTorusHomologyBases

namespace SectionSevenEllipticTwoDiscCoverData

/-- The marked Wang composite is the last raw degree-two coordinate. -/
public theorem actualCuspMarkedWangComposite_eq_rawCoordinateFive
    (A : PaperAnalyticData) :
    (actualCuspFiberFourthCoordinateHom A).comp (actualCuspWangBoundaryHom A) =
      coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 5 := by
  apply AddMonoidHom.ext
  intro x
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  change A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
      (actualCuspWangBoundaryHom A x) 3 = A.actualCuspRawHomologyTwoEquiv x 5
  rw [actualCuspWangBoundaryHom_rawCoordinates]
  rfl

/-- The pulled-back marked boundary vanishes on the four non-invariant raw basis vectors. -/
public theorem cuspPulledBackMarkedBoundary_rawBasis_castAdd_eq_zero
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
    (i : Fin 4) :
    (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.actualCuspRawHomologyTwoEquiv.symm
            (Pi.single (Fin.castAdd 2 i) 1))) = 0 := by
  rw [R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
  change (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
    (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
      (R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm
          (Pi.single (Fin.castAdd 2 i) 1)))) = 0
  rw [cuspOpenCoverConnectingHom_rawBasis_castAdd_eq_zero]
  simp

/-- The two invariant-basis scalar evaluations left after the explicit zero-boundary cases. -/
public def CuspPulledBackMarkedInvariantBasisData
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
      (R.twoDiscCover.cuspPulledBackBoundaryHom
        (A.actualCuspRawHomologyTwoEquiv.symm
          (Pi.single (4 : Fin 6) 1))) = 0 ∧
  (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
      (R.twoDiscCover.cuspPulledBackBoundaryHom
        (A.actualCuspRawHomologyTwoEquiv.symm
          (Pi.single (5 : Fin 6) 1))) = 1

/-- The two invariant-basis evaluations imply the complete marked connecting square. -/
public theorem cuspMarkedConnectingNaturality_of_invariantBasisData
    {A : PaperAnalyticData} (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CuspPulledBackMarkedInvariantBasisData R) :
    R.twoDiscCover.CuspMarkedConnectingNaturality R.homologyAlignment where
  square := by
    rw [actualCuspMarkedWangComposite_eq_rawCoordinateFive]
    apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
      A.actualCuspRawHomologyTwoEquiv
    intro i
    change (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment)
        (R.twoDiscCover.cuspPulledBackBoundaryHom
          (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
      coordinateAfterAddEquiv A.actualCuspRawHomologyTwoEquiv 5
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))
    by_cases hi : i.val < 4
    · let j : Fin 4 := ⟨i.val, hi⟩
      have hij : Fin.castAdd 2 j = i := Fin.ext rfl
      rw [← hij, cuspPulledBackMarkedBoundary_rawBasis_castAdd_eq_zero]
      rw [coordinateAfterAddEquiv_apply, AddEquiv.apply_symm_apply]
      rw [Pi.single_eq_of_ne (by omega : (5 : Fin 6) ≠ Fin.castAdd 2 j)]
    · have hi45 : i = 4 ∨ i = 5 := by omega
      rcases hi45 with rfl | rfl
      · rw [h.1]
        simp [coordinateAfterAddEquiv_apply]
      · rw [h.2]
        simp [coordinateAfterAddEquiv_apply]

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
