module

public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealizationEstablished
public import SphereSixComplex.Topology.PaperSectionSevenCuspWangOpenCoverChainRealization

/-!
# Finite reduction of the canonical cusp Wang boundary square

The first four raw degree-two basis vectors have zero Wang boundary and zero pulled-back cover
boundary.  Consequently the complete naturality square is determined by its values on the two
remaining invariant basis vectors.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

/-- The two invariant-basis comparisons remaining after the four zero-boundary cases have been
proved from the Wang presentation and the explicit pulled-back cover. -/
public def CanonicalCuspWangBoundaryInvariantResidual
    (R : A.SectionSevenAffineRadialCompletionInput) : Prop :=
  R.twoDiscCover.canonicalCuspFiberToBandHomologyOne
      (actualCuspWangBoundaryHom A
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1))) =
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (4 : Fin 6) 1)) ∧
  R.twoDiscCover.canonicalCuspFiberToBandHomologyOne
      (actualCuspWangBoundaryHom A
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))) =
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single (5 : Fin 6) 1))

/-- The two invariant-basis comparisons imply the complete canonical Wang boundary square. -/
public theorem canonicalCuspWangBoundaryNaturality_of_invariantResidual
    (R : A.SectionSevenAffineRadialCompletionInput)
    (h : CanonicalCuspWangBoundaryInvariantResidual R) :
    R.twoDiscCover.CanonicalCuspWangBoundaryNaturality := by
  rw [CanonicalCuspWangBoundaryNaturality]
  apply SphereSixComplex.addMonoidHom_ext_of_equiv_pi_single_one
    A.actualCuspRawHomologyTwoEquiv
  intro i
  change R.twoDiscCover.canonicalCuspFiberToBandHomologyOne
      (actualCuspWangBoundaryHom A
        (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))) =
    R.twoDiscCover.cuspPulledBackBoundaryHom
      (A.actualCuspRawHomologyTwoEquiv.symm (Pi.single i 1))
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val, hi⟩
    have hij : Fin.castAdd 2 j = i := Fin.ext rfl
    rw [← hij, actualCuspWangBoundaryHom_rawBasis,
      actualCuspWangBoundaryRawBasisCoordinates_castAdd, map_zero,
      R.twoDiscCover.cuspPulledBackBoundaryHom_eq_comp]
    change _ = R.twoDiscCover.cuspCoverIntersectionToEllipticBandHomologyOne
      (R.twoDiscCover.cuspOpenCoverConnectingHom
        (A.actualCuspRawHomologyTwoEquiv.symm
          (Pi.single (Fin.castAdd 2 j) 1)))
    rw [cuspOpenCoverConnectingHom_rawBasis_castAdd_eq_zero]
    simp
  · have hi45 : i = 4 ∨ i = 5 := by omega
    rcases hi45 with rfl | rfl
    · exact h.1
    · exact h.2

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData
