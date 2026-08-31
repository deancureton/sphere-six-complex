module

public import SphereSixComplex.Topology.PaperSectionSevenCuspPulledBackMarkedInvariantBasisReduction

/-!
# Canonical signed-overlap reduction for the cusp cover

The Wang boundary has image in the last two marked first-homology coordinates.  The first four
raw degree-two basis classes have zero boundary in the pulled-back cover.  This determines a
canonical homomorphism from the entire cusp-fibre first homology to the two-component overlap:
the first two marked coordinates are sent to zero, while the last two are sent to the pulled-back
cover boundaries of the corresponding invariant degree-two generators.

This construction realizes the oriented Wang boundary without choosing a single overlap slice.
The remaining geometric content is exactly the two marked evaluations already isolated by
`CuspPulledBackMarkedInvariantBasisData`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SectionSevenEllipticInteriorMarkedCycleData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The two invariant raw degree-two generators, transported by the pulled-back cover boundary. -/
public noncomputable def actualCuspInvariantCoverBoundary
    (R : A.SectionSevenAffineRadialCompletionInput) (j : Fin 2) :
    CuspCoverIntersectionHomologyOne R :=
  R.twoDiscCover.cuspOpenCoverConnectingHom
    (A.actualCuspRawHomologyTwoEquiv.symm
      (Pi.single (Fin.natAdd 4 j) 1))

/-- The canonical signed-overlap carrier.  Its last two coordinates are the two invariant
pulled-back cover boundaries; the other two coordinates are killed. -/
public noncomputable def actualCuspCanonicalSignedOverlap
    (R : A.SectionSevenAffineRadialCompletionInput) :
    ActualCuspFiberHomologyOne A →+ CuspCoverIntersectionHomologyOne R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact
    { toFun := fun x ↦
        (G.monodromyCoordinates.degreeOne x 2) • actualCuspInvariantCoverBoundary R 0 +
          (G.monodromyCoordinates.degreeOne x 3) • actualCuspInvariantCoverBoundary R 1
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [map_add, Pi.add_apply, add_smul]
        abel }

@[simp]
public theorem actualCuspMonodromyDegreeOne_symm_single_apply
    (A : PaperAnalyticData) (j k : Fin 4) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.monodromyCoordinates.degreeOne
        (G.monodromyCoordinates.degreeOne.symm (Pi.single j 1)) k =
      (Pi.single j 1 : Fin 4 → ℤ) k := by
  dsimp
  rw [AddEquiv.apply_symm_apply]

@[simp]
public theorem actualCuspCanonicalSignedOverlap_coordinateBasis
    (R : A.SectionSevenAffineRadialCompletionInput) (j : Fin 4) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    actualCuspCanonicalSignedOverlap R
        (G.monodromyCoordinates.degreeOne.symm (Pi.single j 1)) =
      if j = 2 then actualCuspInvariantCoverBoundary R 0
      else if j = 3 then actualCuspInvariantCoverBoundary R 1
      else 0 := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  fin_cases j <;> simp [actualCuspCanonicalSignedOverlap, actualCuspInvariantCoverBoundary]

/-- The canonical signed carrier intertwines the actual Wang boundary and the connecting map of
the pulled-back two-open cover.  This is the full unmarked boundary equality, including its
orientation. -/
public theorem actualCuspCanonicalSignedOverlap_boundary
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (actualCuspCanonicalSignedOverlap R).comp (actualCuspWangBoundaryHom A) =
      R.twoDiscCover.cuspOpenCoverConnectingHom := by
  apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
    A.actualCuspRawHomologyTwoEquiv
  intro i
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  rw [AddMonoidHom.comp_apply, actualCuspWangBoundaryHom_rawBasis]
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val, hi⟩
    have hij : Fin.castAdd 2 j = i := Fin.ext rfl
    rw [← hij, actualCuspWangBoundaryRawBasisCoordinates_castAdd,
      G.monodromyCoordinates.degreeOne.symm.map_zero, map_zero,
      cuspOpenCoverConnectingHom_rawBasis_castAdd_eq_zero]
  · have hi45 : i = 4 ∨ i = 5 := by omega
    rcases hi45 with rfl | rfl
    · rw [actualCuspWangBoundaryRawBasisCoordinates_four]
      simp [actualCuspCanonicalSignedOverlap, actualCuspInvariantCoverBoundary]
    · rw [actualCuspWangBoundaryRawBasisCoordinates_five]
      simp [actualCuspCanonicalSignedOverlap, actualCuspInvariantCoverBoundary]

/-- For the canonical signed carrier, the marked-band equation is equivalent to the two
remaining invariant-basis evaluations. -/
public theorem actualCuspCanonicalSignedOverlap_markedBandDifference_iff
    (R : A.SectionSevenAffineRadialCompletionInput) :
    (R.twoDiscCover.ellipticBandFourthCoordinateHom R.homologyAlignment).comp
          (R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne.comp
            (actualCuspCanonicalSignedOverlap R)) =
        actualCuspFiberFourthCoordinateHom A ↔
      CuspPulledBackMarkedInvariantBasisData R := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  constructor
  · intro h
    constructor
    · have hfour := DFunLike.congr_fun h
          (A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.symm
            (Pi.single (2 : Fin 4) 1))
      simp only [AddMonoidHom.comp_apply] at hfour
      rw [actualCuspCanonicalSignedOverlap_coordinateBasis (A := A) R 2] at hfour
      simpa [actualCuspInvariantCoverBoundary,
        cuspPulledBackBoundaryHom_eq_comp,
        actualCuspFiberFourthCoordinateHom, coordinateAfterAddEquiv_apply] using hfour
    · have hfive := DFunLike.congr_fun h
          (A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne.symm
            (Pi.single (3 : Fin 4) 1))
      simp only [AddMonoidHom.comp_apply] at hfive
      rw [actualCuspCanonicalSignedOverlap_coordinateBasis (A := A) R 3] at hfive
      simpa [actualCuspInvariantCoverBoundary,
        cuspPulledBackBoundaryHom_eq_comp,
        actualCuspFiberFourthCoordinateHom, coordinateAfterAddEquiv_apply] using hfive
  · intro h
    apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
      A.actualCuspRadialClutchingData.monodromyCoordinates.degreeOne
    intro j
    simp only [AddMonoidHom.comp_apply]
    rw [actualCuspCanonicalSignedOverlap_coordinateBasis (A := A) R j]
    by_cases hj2 : j = 2
    · subst j
      simpa [actualCuspInvariantCoverBoundary,
        cuspPulledBackBoundaryHom_eq_comp,
        actualCuspFiberFourthCoordinateHom, coordinateAfterAddEquiv_apply] using h.1
    · by_cases hj3 : j = 3
      · subst j
        simpa [actualCuspInvariantCoverBoundary,
          cuspPulledBackBoundaryHom_eq_comp,
          actualCuspFiberFourthCoordinateHom, coordinateAfterAddEquiv_apply] using h.2
      · simp [hj2, hj3, actualCuspFiberFourthCoordinateHom,
          coordinateAfterAddEquiv_apply]

/-- The canonical signed carrier constructs the complete comparison precisely when the two
remaining marked geometric evaluations hold. -/
public noncomputable def actualCuspWangSignedOverlapComparison_of_invariantBasisData
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CuspPulledBackMarkedInvariantBasisData R) :
    ActualCuspWangSignedOverlapComparison R where
  signedOverlap := actualCuspCanonicalSignedOverlap R
  boundary := actualCuspCanonicalSignedOverlap_boundary R
  markedBandDifference :=
    (actualCuspCanonicalSignedOverlap_markedBandDifference_iff R).2 h

/-- Existence of a correctly oriented two-legged overlap comparison is equivalent to the two
remaining marked geometric evaluations.  In particular, the unmarked signed boundary carrier
is unconditional; no further Wang or Mayer--Vietoris naturality assumption remains. -/
public theorem nonempty_actualCuspWangSignedOverlapComparison_iff
    (R : A.SectionSevenAffineRadialCompletionInput) :
    Nonempty (ActualCuspWangSignedOverlapComparison R) ↔
      CuspPulledBackMarkedInvariantBasisData R := by
  constructor
  · rintro ⟨C⟩
    exact C.invariantBasisData R
  · exact fun h ↦ ⟨actualCuspWangSignedOverlapComparison_of_invariantBasisData R h⟩

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
